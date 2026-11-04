module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistTriangleCanonicalDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision

/-!
# The connecting maps of compactly supported cohomology: naturality and Frobenius

Let `k` be a finite field, `X` a scheme over `k` with a compactification `j` and `k̄` an
extension of `k`. A short exact sequence `0 → G₁ → G₂ → G₃ → 0` of sheaves of `Λ`-modules on
`X_étale` has connecting maps

`δ : Hⁱ_c(X_k̄, G₃) ⟶ Hⁱ⁺¹_c(X_k̄, G₁)`,

read off the distinguished triangle `Stacks.EtaleCohomology.compactSupportFrobeniusTriangle`.
This file proves three things about them.

* They are natural in the short exact sequence. The connecting morphism of that triangle is the
  canonical one (`CategoryTheory.Functor.twistTriangle_mor₃_eq`), even though the triangle is
  built from a resolution chosen by choice.
* They commute with the canonical geometric Frobenius `π_X^*`.
* The sequence `Hⁱ_c(X_k̄, G₂) → Hⁱ_c(X_k̄, G₃) → Hⁱ⁺¹_c(X_k̄, G₁)` is exact.

For the open–closed sequence `0 → j_! j⁻¹ G → G → i_* i⁻¹ G → 0` on a curve, this gives the
inclusion `H⁰_loc ⊆ H¹_c` of Weil II 1.8 ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).
That inclusion must be natural for the transition maps of an ℓ-adic sheaf and for the action of
its coefficients.

The standard model `HasDerivedCategory.standard` is used because the triangle is defined there.

## Main definitions

* `Stacks.EtaleCohomology.compactSupportSheafδ`: the connecting map of a short exact sequence
  of sheaves.

## Main results

* `Stacks.EtaleCohomology.compactSupportFrobeniusTriangle_mor₃_naturality`.
* `Stacks.EtaleCohomology.compactSupportSheafδ_naturality`,
  `Stacks.EtaleCohomology.compactSupportSheafδ_frobenius`,
  `Stacks.EtaleCohomology.exact_compactSupportSheafδ`,
  `Stacks.EtaleCohomology.injective_compactSupportSheafδ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- `RΓ_c(X_k̄, -)` of a morphism of bounded below complexes, read in the unbounded derived
category. -/
public abbrev compactSupportComplexMap {K L : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ}
    (hK : CochainComplex.plus _ K) (hL : CochainComplex.plus _ L) (g : K ⟶ L) :
    DerivedCategory.Plus.ι.obj ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj ⟨K, hK⟩) ⟶
      DerivedCategory.Plus.ι.obj ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj ⟨L, hL⟩) :=
  DerivedCategory.Plus.ι.map ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
    (ObjectProperty.homMk g))

/-- **The connecting morphism of the Frobenius-equivariant triangle of `RΓ_c(X_k̄, -)` is
natural** in the short exact sequence of bounded below complexes. -/
public theorem compactSupportFrobeniusTriangle_mor₃_naturality
    {S S' : ShortComplex (CochainComplex (EtaleModules.{u, 0} Λ X) ℤ)} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
    (h₃ : CochainComplex.plus _ S.X₃) (h₁' : CochainComplex.plus _ S'.X₁)
    (h₂' : CochainComplex.plus _ S'.X₂) (h₃' : CochainComplex.plus _ S'.X₃) (φ : S ⟶ S') :
    (compactSupportFrobeniusTriangle.{u, 0} Λ f j kbar p q hcard hS h₁ h₂ h₃).mor₃ ≫
        (compactSupportComplexMap Λ f j kbar h₁ h₁' φ.τ₁)⟦(1 : ℤ)⟧' =
      compactSupportComplexMap Λ f j kbar h₃ h₃' φ.τ₃ ≫
        (compactSupportFrobeniusTriangle.{u, 0} Λ f j kbar p q hcard hS' h₁' h₂' h₃').mor₃ :=
  Functor.twistTriangle_mor₃_naturality _ _
    (compactSupportShortComplex_shortExact.{u, 0} Λ f j kbar hS)
    (compactSupportShortComplex_shortExact.{u, 0} Λ f j kbar hS') _ _ _ _ _ _ _ _
    (((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
      ).mapHomologicalComplex _).mapShortComplex.map
      (((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapHomologicalComplex _
        ).mapShortComplex.map φ))

/-! ### Sheaves -/

/-- A square of bounded below complexes, carried by a functor; stated on variables. -/
public theorem map_homMk_comp_eq {𝒜 𝒟 : Type*} [Category* 𝒜] [Category* 𝒟] [Abelian 𝒜]
    (H : CochainComplex.Plus 𝒜 ⥤ 𝒟) {K L L' M : CochainComplex 𝒜 ℤ}
    (hK : CochainComplex.plus 𝒜 K) (hL : CochainComplex.plus 𝒜 L)
    (hL' : CochainComplex.plus 𝒜 L') (hM : CochainComplex.plus 𝒜 M) (a : K ⟶ L) (b : L ⟶ M)
    (a' : K ⟶ L') (b' : L' ⟶ M) (h : a ≫ b = a' ≫ b') :
    H.map (ObjectProperty.homMk a : (⟨K, hK⟩ : CochainComplex.Plus 𝒜) ⟶ ⟨L, hL⟩) ≫
        H.map (ObjectProperty.homMk b : (⟨L, hL⟩ : CochainComplex.Plus 𝒜) ⟶ ⟨M, hM⟩) =
      H.map (ObjectProperty.homMk a' : (⟨K, hK⟩ : CochainComplex.Plus 𝒜) ⟶ ⟨L', hL'⟩) ≫
        H.map (ObjectProperty.homMk b' : (⟨L', hL'⟩ : CochainComplex.Plus 𝒜) ⟶ ⟨M, hM⟩) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  ext : 1
  exact h

section Sheaf

variable {G : ShortComplex (EtaleModules.{u, 0} Λ X)} (hG : G.ShortExact)

/-- A short complex of sheaves, placed in degree `0`. -/
public abbrev sheafSingleShortComplex (G : ShortComplex (EtaleModules.{u, 0} Λ X)) :
    ShortComplex (CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) :=
  G.map (HomologicalComplex.single (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ) 0)

include hG in
public lemma sheafSingleShortComplex_shortExact : (sheafSingleShortComplex Λ G).ShortExact :=
  hG.map_of_exact (HomologicalComplex.single (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ) 0)

public lemma plus_single (M : EtaleModules.{u, 0} Λ X) :
    CochainComplex.plus _ ((HomologicalComplex.single (EtaleModules.{u, 0} Λ X)
      (ComplexShape.up ℤ) 0).obj M) :=
  ⟨0, (inferInstance : CochainComplex.IsStrictlyGE ((HomologicalComplex.single
    (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ) 0).obj M) 0)⟩

include hG in
/-- The distinguished triangle of `RΓ_c(X_k̄, -)` of a short exact sequence of sheaves. -/
public abbrev compactSupportSheafTriangle :
    Triangle (DerivedCategory (ModuleCat.{u + 1} Λ)) :=
  compactSupportFrobeniusTriangle.{u, 0} Λ f j kbar p q hcard
    (sheafSingleShortComplex_shortExact Λ hG) (plus_single Λ G.X₁) (plus_single Λ G.X₂)
    (plus_single Λ G.X₃)

include hG in
/-- **The connecting map `Hⁱ_c(X_k̄, G₃) ⟶ Hⁱ⁺¹_c(X_k̄, G₁)`** of a short exact sequence of
sheaves of `Λ`-modules on `X_étale`. -/
public def compactSupportSheafδ (i i' : ℤ) (hi : i + 1 = i') :
    (compactSupportSheafCohomology Λ f j kbar i).obj G.X₃ ⟶
      (compactSupportSheafCohomology Λ f j kbar i').obj G.X₁ :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).homologySequenceδ
    (compactSupportSheafTriangle Λ f j kbar p q hcard hG) i i' hi

variable {G' : ShortComplex (EtaleModules.{u, 0} Λ X)} (hG' : G'.ShortExact)

include hG hG' in
/-- The morphism of triangles of `RΓ_c(X_k̄, -)` induced by a morphism of short exact sequences
of sheaves. -/
public def compactSupportSheafTriangleMap (ψ : G ⟶ G') :
    compactSupportSheafTriangle Λ f j kbar p q hcard hG ⟶
      compactSupportSheafTriangle Λ f j kbar p q hcard hG' where
  hom₁ := compactSupportComplexMap Λ f j kbar (plus_single Λ G.X₁) (plus_single Λ G'.X₁)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ψ.τ₁)
  hom₂ := compactSupportComplexMap Λ f j kbar (plus_single Λ G.X₂) (plus_single Λ G'.X₂)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ψ.τ₂)
  hom₃ := compactSupportComplexMap Λ f j kbar (plus_single Λ G.X₃) (plus_single Λ G'.X₃)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ψ.τ₃)
  comm₁ := map_homMk_comp_eq (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
    DerivedCategory.Plus.ι) _ _ _ _ _ _ _ _ ((HomologicalComplex.single (EtaleModules.{u, 0} Λ X)
      (ComplexShape.up ℤ) 0).mapShortComplex.map ψ).comm₁₂.symm
  comm₂ := map_homMk_comp_eq (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
    DerivedCategory.Plus.ι) _ _ _ _ _ _ _ _ ((HomologicalComplex.single (EtaleModules.{u, 0} Λ X)
      (ComplexShape.up ℤ) 0).mapShortComplex.map ψ).comm₂₃.symm
  comm₃ := compactSupportFrobeniusTriangle_mor₃_naturality Λ f j kbar p q hcard
    (sheafSingleShortComplex_shortExact Λ hG) (sheafSingleShortComplex_shortExact Λ hG')
    (plus_single Λ G.X₁) (plus_single Λ G.X₂) (plus_single Λ G.X₃) (plus_single Λ G'.X₁)
    (plus_single Λ G'.X₂) (plus_single Λ G'.X₃)
    ((HomologicalComplex.single (EtaleModules.{u, 0} Λ X)
      (ComplexShape.up ℤ) 0).mapShortComplex.map ψ)

include hG hG' in
/-- **The connecting maps are natural** in the short exact sequence of sheaves. -/
public theorem compactSupportSheafδ_naturality (ψ : G ⟶ G') (i i' : ℤ) (hi : i + 1 = i') :
    (compactSupportSheafCohomology Λ f j kbar i).map ψ.τ₃ ≫
        compactSupportSheafδ Λ f j kbar p q hcard hG' i i' hi =
      compactSupportSheafδ Λ f j kbar p q hcard hG i i' hi ≫
        (compactSupportSheafCohomology Λ f j kbar i').map ψ.τ₁ :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).homologySequenceδ_naturality
    (compactSupportSheafTriangleMap Λ f j kbar p q hcard hG hG' ψ) i i' hi

include hG in
/-- **The connecting maps commute with the canonical geometric Frobenius `π_X^*`.** -/
public theorem compactSupportSheafδ_frobenius (i i' : ℤ) (hi : i + 1 = i') :
    (compactSupportSheafFrobenius Λ f j kbar p q hcard i).app G.X₃ ≫
        compactSupportSheafδ Λ f j kbar p q hcard hG i i' hi =
      compactSupportSheafδ Λ f j kbar p q hcard hG i i' hi ≫
        (compactSupportSheafFrobenius Λ f j kbar p q hcard i').app G.X₁ :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).homologySequenceδ_naturality
    (compactSupportFrobeniusTriangleEndo.{u, 0} Λ f j kbar p q hcard
      (sheafSingleShortComplex_shortExact Λ hG) (plus_single Λ G.X₁) (plus_single Λ G.X₂)
      (plus_single Λ G.X₃)) i i' hi

include hG in
/-- **Exactness at `Hⁱ_c(X_k̄, G₃)`**: `Hⁱ_c(X_k̄, G₂) ⟶ Hⁱ_c(X_k̄, G₃) ⟶ Hⁱ⁺¹_c(X_k̄, G₁)` is
exact. -/
public theorem exact_compactSupportSheafδ (i i' : ℤ) (hi : i + 1 = i') :
    Function.Exact ((compactSupportSheafCohomology Λ f j kbar i).map G.g).hom
      (compactSupportSheafδ Λ f j kbar p q hcard hG i i' hi).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).homologySequence_exact₃ _
      (compactSupportFrobeniusTriangle_distinguished.{u, 0} Λ f j kbar p q hcard
        (sheafSingleShortComplex_shortExact Λ hG) (plus_single Λ G.X₁) (plus_single Λ G.X₂)
        (plus_single Λ G.X₃)) i i' hi)

include hG in
/-- **The connecting map is injective when `Hⁱ_c(X_k̄, G₂) = 0`.** -/
public theorem injective_compactSupportSheafδ (i i' : ℤ) (hi : i + 1 = i')
    (h : IsZero ((compactSupportSheafCohomology Λ f j kbar i).obj G.X₂)) :
    Function.Injective (compactSupportSheafδ Λ f j kbar p q hcard hG i i' hi).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_compactSupportSheafδ Λ f j kbar p q hcard hG i i' hi x).1 hx
  rw [(ModuleCat.subsingleton_of_isZero h).elim y 0, map_zero]

end Sheaf

end Stacks.EtaleCohomology
