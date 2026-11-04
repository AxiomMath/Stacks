module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackLocus
public import StacksFrontier.AlgebraicGeometry.Quot.InvertibleTwistPower
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackTensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.NumericalIntersection

/-!
# The twisted Euler characteristics of a family of coherent sheaves

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and let `L` be an
invertible `𝒪_X`-module.  For an object `(T ⟶ B, 𝓕)` of `Coh_{X/B}` and a point `t ∈ T`, write
`X_t = X ×_B Spec κ(t)` for the fibre, `𝓕_t` for the pullback of `𝓕` to it and `L_t` for the
pullback of `L`.  Stacks 0DNF considers the function

`n ↦ χ(X_t, 𝓕_t ⊗_{𝒪_{X_t}} L_t^{⊗ n}) = ∑ᵢ (-1)ⁱ dim_{κ(t)} Hⁱ(X_t, 𝓕_t ⊗ L_t^{⊗ n})`.

This file constructs that function.

## Main definitions

* `AlgebraicGeometry.Space.globalSectionsRingHom`: for an algebraic space `F` over `S` and a
  morphism `F ⟶ V` to a scheme over `S`, the ring map `Γ(V, 𝒪_V) ⟶ Γ(F, 𝒪_F)`.
* `AlgebraicGeometry.Space.eulerCharacteristicAlong`: the alternating sum
  `∑ᵢ (-1)ⁱ dim_k Hⁱ(F, M)` of the dimensions of the cohomology of an `𝒪_F`-module over a field
  `k` mapping to `Γ(F, 𝒪_F)`.
* `AlgebraicGeometry.Space.CoherentObject.pointTest`, `.fibreSpace` and `.fibreModule`: for an
  object `(T, 𝓕)` of `Coh_{X/B}` and a point `t ∈ T`, the test scheme `Spec κ(t) ⟶ T ⟶ B`, the
  fibre `X_t` and the pullback `𝓕_t`.
* `AlgebraicGeometry.Space.CoherentObject.twistedEuler`: **the twisted Euler characteristic**
  `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})`.
* `AlgebraicGeometry.Space.CoherentObject.HasHilbertPolynomial`: the condition
  `P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` for all `n` and `t` cutting out `Coh^{P, L}_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.eulerCharacteristicAlong_congr`: the Euler characteristic depends on
  the module only up to isomorphism.
* `AlgebraicGeometry.Space.CoherentObject.twistedEuler_eq_fibreTensorPower`: the twist may be
  taken with the tensor powers of the pullback `L_t` itself.
* `AlgebraicGeometry.Space.CoherentObject.twistedEuler_invertibleTensorPower`: the twisted Euler
  characteristics with respect to `L^{⊗ k}` are those with respect to `L` at the multiples of
  `k`, the identity on fibres behind Stacks 0DP8.

## Implementation notes

The cohomology `Hⁱ(X_t, -)` is the cohomology of modules on the small étale ringed site of the
fibre, a module over the ring `Γ(X_t, 𝒪_{X_t})` of global functions; it is regarded as a
`κ(t)`-vector space along the ring map `κ(t) = Γ(Spec κ(t)) ⟶ Γ(X_t, 𝒪_{X_t})` induced by the
projection `X_t ⟶ Spec κ(t)`.  This is `AlgebraicGeometry.Space.cohomologyOverBase` with the
base scheme of the algebraic space replaced by a scheme over it: the fibre `X_t` is an algebraic
space over the same scheme `S` as `X`, and over `Spec κ(t)` through a morphism.

The dimension is `Module.finrank` and the sum is a `finsum`, so the function is defined for every
module; for `𝓕` in `Coh_{X/B}` the cohomology of `𝓕_t ⊗ L_t^{⊗ n}` is finite dimensional and
vanishes in large degrees, the support of `𝓕_t` being proper over `κ(t)`, and then this is the
Euler characteristic of the source.

The twist `L_t^{⊗ n}` is taken as the pullback of `L^{⊗ n}` along the projection `X_t ⟶ X`.
Pullback commutes with tensor products, so this is canonically the `n`-th tensor power of `L_t`,
which is `AlgebraicGeometry.Space.CoherentObject.twistedEuler_eq_fibreTensorPower`; taking it in
this form spares the invertibility of `L_t` as an instance in the definition.

The cohomology is taken with the module universe raised to the universe of the objects of the
small étale site, the universe in which `AlgebraicGeometry.Space.cohomologyOverBase` lives.

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DN1](https://stacks.math.columbia.edu/tag/0DN1)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

section GlobalSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The morphism to a scheme `V` over `S` from the scheme underlying an étale chart of `F`,
through a morphism `φ : F ⟶ V`. -/
def chartToScheme {V : BigFppfOver B S hS} (φ : F ⟶ yoneda.obj V) (U : SmallEtale B S hS F) :
    (SmallEtale.toOver B S hS F).obj U ⟶ V :=
  Yoneda.fullyFaithful.preimage (U.obj.hom ≫ φ)

/-- For a morphism `g : U ⟶ U'` of étale charts of `F`, the composite of the induced morphism of
schemes with `chartToScheme B S hS F φ U'` is `chartToScheme B S hS F φ U`. -/
theorem chartToScheme_naturality {V : BigFppfOver B S hS} (φ : F ⟶ yoneda.obj V)
    {U U' : SmallEtale B S hS F} (g : U ⟶ U') :
    (SmallEtale.toOver B S hS F).map g ≫ chartToScheme B S hS F φ U' =
      chartToScheme B S hS F φ U := by
  apply Yoneda.fullyFaithful.map_injective
  simp only [chartToScheme, Functor.map_comp, Functor.FullyFaithful.map_preimage]
  rw [← Category.assoc]
  congr 1
  exact CostructuredArrow.w g.hom

/-- The ring map `Γ(V, 𝒪_V) ⟶ Γ(F, 𝒪_F)` induced by a morphism `φ : F ⟶ V` from an algebraic
space to a scheme over `S`: a function on `V` is sent to the family of its pullbacks to the étale
charts of `F`. -/
def globalSectionsRingHom {V : BigFppfOver B S hS} (φ : F ⟶ yoneda.obj V) :
    Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj V)) →+*
      Stacks.Cohomology.SiteModules.GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
  (RingHom.pi fun U : (SmallEtale B S hS F)ᵒᵖ => (Scheme.Γ.map
      ((BigFppfOver.toScheme B S hS).map (chartToScheme B S hS F φ U.unop)).op).hom).codRestrict _
    fun a U U' g => by
      change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (chartToScheme B S hS F φ U.unop)).op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map g.unop)).op).hom a = _
      rw [← Functor.map_comp, ← op_comp, ← Functor.map_comp]
      exact congrArg (fun k => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom a)
        (chartToScheme_naturality B S hS F φ (U := U'.unop) (U' := U.unop) g.unop)

/-- The alternating sum `∑ᵢ (-1)ⁱ dim_k Hⁱ(F, M)` of the dimensions of the cohomology modules
of an `𝒪_F`-module `M` on the small étale site of `F`, each regarded as a `k`-vector space along
a ring map `ψ : k ⟶ Γ(F, 𝒪_F)`. -/
def eulerCharacteristicAlong (k : Type u) [Field k]
    (ψ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    (M : Modules.{u, u} B S hS F hF) : ℤ :=
  ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k
    ((ModuleCat.restrictScalars ψ).obj
      ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) i).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} M))) : ℤ)

/-- **The Euler characteristic depends on the module only up to isomorphism.** -/
theorem eulerCharacteristicAlong_congr (k : Type u) [Field k]
    (ψ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    {M N : Modules.{u, u} B S hS F hF} (e : M ≅ N) :
    eulerCharacteristicAlong B S hS F hF k ψ M = eulerCharacteristicAlong B S hS F hF k ψ N := by
  unfold eulerCharacteristicAlong
  congr 1
  funext i
  congr 2
  exact LinearEquiv.finrank_eq
    ((ModuleCat.restrictScalars ψ).mapIso
      ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) i).mapIso
        (uliftForPresentationMapIso.{u, 0} B S hS F hF e))).toLinearEquiv

end GlobalSections

namespace CoherentObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- `Spec κ(t)`, for a point `t` of the test scheme of an object of `Coh_{X/B}`, as an object of
the big fppf site over `S`. -/
def pointScheme (A : CoherentObject D) (t : A.testScheme) : BigFppfOver B S hS :=
  siteObject B S hS (B.residueField_spec_contains A.T.left.left.property t)
    (A.testScheme.fromSpecResidueField t ≫ B.inclusion.map A.T.left.hom)

/-- The morphism `Spec κ(t) ⟶ T` of schemes over `S`. -/
def pointSchemeHom (A : CoherentObject D) (t : A.testScheme) :
    A.pointScheme t ⟶ A.T.left :=
  Over.homMk (ObjectProperty.homMk (A.testScheme.fromSpecResidueField t)) (by
    apply ObjectProperty.hom_ext
    simp [pointScheme])

/-- `Spec κ(t) ⟶ T ⟶ B`, for a point `t` of the test scheme, as a test scheme over `B`. -/
def pointTest (A : CoherentObject D) (t : A.testScheme) : SchemesOver D.Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (A.pointSchemeHom t) ≫ A.T.hom)

/-- The morphism `Spec κ(t) ⟶ T` of test schemes over `B`. -/
def pointTestHom (A : CoherentObject D) (t : A.testScheme) : A.pointTest t ⟶ A.T :=
  CostructuredArrow.homMk (A.pointSchemeHom t) rfl

/-- The fibre `X_t = X ×_B Spec κ(t)` over a point `t` of the test scheme. -/
abbrev fibreSpace (A : CoherentObject D) (t : A.testScheme) : AlgebraicSpaces B S hS :=
  D.space (A.pointTest t)

/-- The pullback `𝓕_t` of the module of an object of `Coh_{X/B}` to the fibre over a point. -/
def fibreModule (A : CoherentObject D) (t : A.testScheme) :
    Modules.{u, u} B S hS (A.fibreSpace t).1 (A.fibreSpace t).2 :=
  (modulePullback B S hS (D.relativeMap (A.pointTestHom t))).obj A.F

/-- The ring map `κ(t) ⟶ Γ(X_t, 𝒪_{X_t})` induced by the projection `X_t ⟶ Spec κ(t)`. -/
def fibreFieldHom (A : CoherentObject D) (t : A.testScheme) :
    A.testScheme.residueField t →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O)) :=
  (globalSectionsRingHom B S hS (A.fibreSpace t).1 (A.fibreSpace t).2
    (D.projection (A.pointTest t)).hom).comp
    (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom

/-- **The twisted Euler characteristics of Stacks 0DNF.**  For an object `(T, 𝓕)` of
`Coh_{X/B}`, an invertible `𝒪_X`-module `L` and a point `t ∈ T`, the function

`n ↦ χ(X_t, 𝓕_t ⊗_{𝒪_{X_t}} L_t^{⊗ n}) = ∑ᵢ (-1)ⁱ dim_{κ(t)} Hⁱ(X_t, 𝓕_t ⊗ L_t^{⊗ n})`. -/
def twistedEuler (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) (n : ℤ) : ℤ :=
  eulerCharacteristicAlong B S hS (A.fibreSpace t).1 (A.fibreSpace t).2
    (A.testScheme.residueField t) (A.fibreFieldHom t)
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj
        (A.fibreModule t)).obj
      ((modulePullback B S hS (baseChangeProjection D.f (A.pointTest t))).obj
        (invertibleTensorPower B S hS D.X.1 D.X.2 L n)))

/-- The Euler characteristic of `𝓕_t ⊗ M` on the fibre depends on `M` only up to isomorphism. -/
private theorem eulerCharacteristicAlong_fibreModule_tensor_congr (A : CoherentObject D)
    (t : A.testScheme) {M N : Modules.{u, u} B S hS (A.fibreSpace t).1 (A.fibreSpace t).2}
    (e : M ≅ N) :
    eulerCharacteristicAlong B S hS (A.fibreSpace t).1 (A.fibreSpace t).2
        (A.testScheme.residueField t) (A.fibreFieldHom t)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj
            (A.fibreModule t)).obj M) =
      eulerCharacteristicAlong B S hS (A.fibreSpace t).1 (A.fibreSpace t).2
        (A.testScheme.residueField t) (A.fibreFieldHom t)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj
            (A.fibreModule t)).obj N) :=
  eulerCharacteristicAlong_congr _ _ _ _ _ _ _
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj
        (A.fibreModule t)).mapIso e)

/-- **The twisted Euler characteristic is computed with the tensor powers of `L_t`**: the twist
`(L^{⊗ n})_t` used in `AlgebraicGeometry.Space.CoherentObject.twistedEuler` is canonically
`L_t^{⊗ n}`, the pullback `L_t` being invertible, so
`twistedEuler L A t n = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` with the power taken on the fibre. -/
theorem twistedEuler_eq_fibreTensorPower (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) (n : ℤ) :
    letI := isInvertible_modulePullback B S hS (baseChangeProjection D.f (A.pointTest t)) L
    twistedEuler L A t n =
      eulerCharacteristicAlong B S hS (A.fibreSpace t).1 (A.fibreSpace t).2
        (A.testScheme.residueField t) (A.fibreFieldHom t)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj
            (A.fibreModule t)).obj
          (invertibleTensorPower B S hS (A.fibreSpace t).1 (A.fibreSpace t).2
            ((modulePullback B S hS (baseChangeProjection D.f (A.pointTest t))).obj L) n)) :=
  eulerCharacteristicAlong_fibreModule_tensor_congr A t
    (modulePullbackInvertibleTensorPowerIso B S hS
      (baseChangeProjection D.f (A.pointTest t)) L n)

/-- **The membership condition of `Coh^{P, L}_{X/B}`** (Stacks 0DNF): an object `(T, 𝓕)` of
`Coh_{X/B}` has Hilbert polynomial `P` with respect to `L` when
`P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` for every point `t ∈ T` and every `n ∈ ℤ`.  This is
`AlgebraicGeometry.Space.IsPrescribedTwistedEuler` for the actual twisted Euler characteristics
`AlgebraicGeometry.Space.CoherentObject.twistedEuler`. -/
def HasHilbertPolynomial (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (P : ℤ → ℤ) (A : CoherentObject D) : Prop :=
  IsPrescribedTwistedEuler P (twistedEuler L A)

/-- An object `A` of `Coh_{X/B}` has Hilbert polynomial `P` with respect to `L` if and only if
`P n = twistedEuler L A t n` for every point `t` of the test scheme and every `n ∈ ℤ`. -/
theorem hasHilbertPolynomial_iff (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (P : ℤ → ℤ) (A : CoherentObject D) :
    HasHilbertPolynomial L P A ↔ ∀ (t : A.testScheme) (n : ℤ), P n = twistedEuler L A t n :=
  Iff.rfl

/-- **The twisted Euler characteristics with respect to `L^{⊗ k}` are those with respect to `L`
at the multiples of `k`**: `χ(X_t, 𝓕_t ⊗ (L^{⊗ k})_t^{⊗ m}) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ k m})`. -/
theorem twistedEuler_invertibleTensorPower (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) (k m : ℤ) :
    twistedEuler (invertibleTensorPower B S hS D.X.1 D.X.2 L k) A t m =
      twistedEuler L A t (k * m) :=
  eulerCharacteristicAlong_fibreModule_tensor_congr A t
    ((modulePullback B S hS (baseChangeProjection D.f (A.pointTest t))).mapIso
      (invertibleTensorPowerTensorPowerIso B S hS D.X.1 D.X.2 L k m))

end CoherentObject

end AlgebraicGeometry.Space

end
