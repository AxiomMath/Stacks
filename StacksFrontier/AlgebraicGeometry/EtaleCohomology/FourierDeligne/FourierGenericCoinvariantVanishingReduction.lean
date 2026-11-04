module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierGenericCoinvariantVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformPunctual
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PunctualEtaleModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.InverseImageNoPunctualSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleOpens
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.ProjectionFormulaBaseChange

/-!
# Generic vanishing of `H²(Φ(H[0]))`: reduction to an extension by zero

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. Let `H` be a sheaf on `𝔸¹_k` whose restriction to a nonempty open `V` is locally
constant with finite values. Nothing is assumed about `H` off `V`.

Writing `W ⊆ 𝔸¹_k` for the image of `V` and `M = H|_W`, the counit `j_{W!} M ⟶ H` is a
monomorphism whose cokernel `Q` vanishes on `W`. So `Q` is punctual, `Φ(Q[0])` is concentrated
in degree zero (`Stacks.EtaleCohomology.isZero_homology_fourierTransform_of_isZero_inverseImage`),
and the long exact cohomology sequence of the triangulated functor `Φ` makes
`H²(Φ(j_{W!} M[0])) ⟶ H²(Φ(H[0]))` an epimorphism. A quotient of a punctual sheaf is punctual,
so the generic vanishing for `H` follows from the generic vanishing for the extension by zero
`j_{W!} M` of a locally constant sheaf with finite values, which is constructible.

This is the first step of the proof of the input (L2) of the single-level argument for the
irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.FourierExtensionByZeroGenericVanishingInput`: (L2) for the extension
  by zero of a locally constant sheaf with finite values on a nonempty open.

## Main results

* `Stacks.EtaleCohomology.epi_homology_map_singleFunctor_map_of_isZero`: in the long exact
  cohomology sequence of a triangulated functor applied to a short exact sequence, `Hⁿ(F(X₁[0]))`
  maps onto `Hⁿ(F(X₂[0]))` when `Hⁿ(F(X₃[0])) = 0`.
* `Stacks.EtaleCohomology.fourierGenericCoinvariantVanishingInput_of_extensionByZero`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so do the
statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Sequence

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  (F : DerivedCategory.Plus C ⥤ DerivedCategory.Plus C) [F.CommShift ℤ] [F.IsTriangulated]

/-- **`Hⁿ(F(X₁[0])) ⟶ Hⁿ(F(X₂[0]))` is onto when `Hⁿ(F(X₃[0])) = 0`**, for a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` and a triangulated functor `F` on `D⁺`: the long exact cohomology sequence
of the image of the triangle `X₁[0] → X₂[0] → X₃[0] → X₁[1]`. -/
theorem epi_homology_map_singleFunctor_map_of_isZero {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℤ) (hz : IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj
      (F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₃)))) :
    Epi ((DerivedCategory.Plus.homologyFunctor C n).map
      (F.map ((DerivedCategory.Plus.singleFunctor C 0).map S.f))) :=
  ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _
    (F.map_distinguished _ (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS)) n).2
    (hz.eq_of_tgt _ _)

end Sequence

/-- **(L2) for an extension by zero**: for a sheaf `M` of `Λ`-modules on a nonempty open `V` of
`𝔸¹_k`, locally constant with finite values, `H²(Φ(j_! M[0]))` vanishes on a nonempty open `U`
of `𝔸¹_k`, `Φ` the Fourier transform for an additive character `ψ` with `∑ ψ = 0` and
coefficients in a finite ring in which `#k` is a unit. At a geometric point `t̄` the stalk is
`H²_c(V_t̄, M ⊗ L_ψ(x t))`, the coinvariants of the twisted monodromy representation of
`π₁(V_t̄)`, which vanish for all but finitely many `t̄`. -/
def FourierExtensionByZeroGenericVanishingInput : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
    (B : BigEtaleSite.{u})
    (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj
      (cover k (Polynomial k) Polynomial.X)),
    ∑ a : k, ψ a = 0 → IsUnit (Fintype.card k : Λ) →
    ∀ (j : CompactificationOf (Over.mk (affineLineStructureMap k))) {V : Scheme.{u}}
      (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V]
      (M : EtaleModules.{u, 0} Λ V),
      Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
        (fun E => Module.Finite Λ E) M →
      IsPunctualEtaleModule Λ ((DerivedCategory.Plus.homologyFunctor _ 2).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ jV).obj M))))

attribute [local instance] etaleModuleInverseImage_preservesFiniteColimits in
/-- **The cokernel of `j_! j⁻¹ H ⟶ H` vanishes on the open `j`**, for an open immersion `j`:
`j⁻¹` is right exact and carries the counit to an isomorphism. -/
theorem isZero_etaleModuleInverseImage_cokernel_counit (Λ : Type) [Ring Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (H : EtaleModules.{u, 0} Λ X) :
    IsZero ((etaleModuleInverseImage.{u, 0} Λ j).obj
      (cokernel ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app H))) := by
  let c := (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app H
  let Fj := etaleModuleInverseImage.{u, 0} Λ j
  have : IsIso (Fj.map c) :=
    (NatIso.isIso_map_iff (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j) c).2
      (isIso_etaleModuleRestriction_map_counit.{u, 0} Λ j H)
  exact IsZero.of_epi_eq_zero _ (by
    rw [← cancel_epi (Fj.map c), ← Fj.map_comp, cokernel.condition, Fj.map_zero, comp_zero])

/-- **(L2) reduces to an extension by zero**: the generic vanishing of `H²(Φ(H[0]))` for a sheaf
`H` locally constant with finite values on a nonempty open `V` follows from that for
`j_{W!}(H|_W)`, `W` the image of `V`, whose image under `H²(Φ(-[0]))` maps onto `H²(Φ(H[0]))`. -/
theorem fourierGenericCoinvariantVanishingInput_of_extensionByZero
    (h : FourierExtensionByZeroGenericVanishingInput.{u}) :
    FourierGenericCoinvariantVanishingInput.{u} := by
  intro k _ _ Λ _ _ ψ B p₀ hψ hq j H V jV _ _ hH
  let X := Spec (.of (Polynomial k))
  let W : X.Opens := jV.opensRange
  have : Nonempty W := ⟨⟨jV.base (Classical.arbitrary V), ⟨_, rfl⟩⟩⟩
  let M := (etaleModuleRestriction.{u, 0} Λ W.ι).obj H
  have hW : W.ι = jV.isoOpensRange.inv ≫ jV := (jV.isoOpensRange_inv_comp).symm
  have hM : Stacks.ConstantSheaf.IsLocallyConstantWith Λ (W : Scheme.{u}).smallEtaleTopology
      (fun E => Module.Finite Λ E) M :=
    isLocallyConstantWith_of_iso Λ _
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ W.ι).app H)
      (isLocallyConstantWith_of_iso Λ _
        ((etaleModuleInverseImageCompIso' Λ jV.isoOpensRange.inv jV W.ι hW).app H).symm
        (isLocallyConstantWith_inverseImage Λ _ jV.isoOpensRange.inv hH))
  let c := (etaleModuleExtensionByZeroAdj.{u, 0} Λ W.ι).counit.app H
  have : Mono c := mono_etaleModuleExtensionByZeroAdj_counit_app Λ W H
  let S := ShortComplex.mk c (cokernel.π c) (cokernel.condition c)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel c) inferInstance inferInstance
  have hQ : IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj S.X₃))) :=
    isZero_homology_fourierTransform_of_isZero_inverseImage k Λ ψ B p₀ j _ W.ι
      (isZero_etaleModuleInverseImage_cokernel_counit Λ W.ι H) 2 (by norm_num)
  have hepi := @epi_homology_map_singleFunctor_map_of_isZero _ _ _ _
    (fourierTransform k Λ ψ B p₀ j) (fourierTransformCommShift k Λ ψ B p₀ j)
    (isTriangulated_fourierTransform k Λ ψ B p₀ j) S hS 2 hQ
  exact @IsPunctualEtaleModule.of_epi _ _ _ _ _ ((DerivedCategory.Plus.homologyFunctor _ 2).map
    ((fourierTransform k Λ ψ B p₀ j).map ((DerivedCategory.Plus.singleFunctor _ 0).map S.f)))
    hepi (h k Λ ψ B p₀ hψ hq j W.ι M hM)

end Stacks.EtaleCohomology

end
