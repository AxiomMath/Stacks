module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusExtensionCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobeniusNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars

/-!
# `RΓ_c` of the base change to a finite extension of the base field

Let `k` be a finite field with `q = p ^ f` elements, `X` a separated scheme of finite type over
`k` with a compactification `j : X ⟶ X̄`, `k'` an extension of `k` and `k̄` an extension of `k'`.
Write `X' = X ×_k k'`, a scheme over `k'` compactified by the base change `j' : X' ⟶ X̄ ×_k k'`
(`Stacks.EtaleCohomology.compactificationFieldBaseChange`), and `g : X' ⟶ X` for the projection.
For a bounded below complex `K` on `X_étale`,

`RΓ_c(X'_{k̄}, g⁻¹ K) ≅ RΓ_c(X_{k̄}, K)`,

naturally in `K`: extension by zero commutes with the inverse image along `g` (Tag 03S6) and the
geometric fibres of `X̄ ×_k k'` and of `X̄` agree.  If `k'` has `q ^ m` elements, the
identification carries the canonical Frobenius `π_{X'}^*` of `X'` over `k'` to `(π_X^*) ^ m`.
This is the comparison of cohomology in the proof of [Stacks, Tag 03V0], where the trace formula
of Tag 03V2 for `X'` over `k'` computes the traces of the powers of `π_X^*`.

## Main definitions

* `Stacks.EtaleCohomology.compactSupportFieldExtensionIso`:
  `RΓ_c(X'_{k̄}, g⁻¹ K) ≅ RΓ_c(X_{k̄}, K)`.

## Main results

* `Stacks.EtaleCohomology.compactSupportFieldExtensionIso_hom_naturality`: the identification is
  natural in `K`.
* `Stacks.EtaleCohomology.compactSupportFieldExtensionIso_comm`: it carries `π_{X'}^*` to a power
  of `π_X^*`.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard


/-! ### The comparison of `RΓ_c` -/

section Comparison

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (k' : Type u) [Field k'] [Algebra k k']
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar]

/-- Extension by zero along the base-changed compactification commutes with the inverse image
along `g : X ×_k k' ⟶ X`, degreewise on a bounded below complex (Tag 03S6). -/
def compactificationFieldBaseChangeExtensionByZeroComplexIso
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    (etaleModuleExtensionByZero.{u, r} Λ
        (compactificationFieldBaseChange f j k').immersion).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, r} Λ
          (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.obj K) ≅
      (etaleModuleInverseImage.{u, r} Λ
          (extensionProj (Over.mk j.toBase) k')).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj K) :=
  ObjectProperty.isoMk _
    ((NatIso.mapHomologicalComplex
        (compactificationFieldBaseChangeExtensionByZeroIso Λ f j k') _).app
      K.obj)

/-- **`RΓ_c(X'_{k̄}, g⁻¹ K) ≅ RΓ_c(X_{k̄}, K)`** for `X' = X ×_k k'` compactified by the base
change of `j`: Tag 03S6 for the compactification, then the identification of the geometric fibres
`(X̄ ×_k k')_{k̄} = X̄_{k̄}`. -/
def compactSupportFieldExtensionIso (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    (compactSupportFrobeniusFunctor.{u, r} Λ (pullback.snd f (specAlgebraMap k k'))
        (compactificationFieldBaseChange f j k') kbar).obj
        ((etaleModuleInverseImage.{u, r} Λ
          (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.obj K) ≅
      (compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).obj K :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, r} Λ
          (pullback.snd (extensionOver (Over.mk j.toBase) k').hom (specAlgebraMap k' kbar))).mapIso
        (DerivedCategory.Plus.Q.mapIso
          ((etaleModuleInverseImage.{u, r} Λ
            (fieldBaseChangeProj (extensionOver (Over.mk j.toBase) k')
              kbar)).mapCochainComplexPlus.mapIso
              (compactificationFieldBaseChangeExtensionByZeroComplexIso Λ f j k' K)))) ≪≫
    frobeniusExtensionCohomologyIso Λ (Over.mk j.toBase) k' kbar
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj K)

/-- Pasting a naturality square in front of a composite; stated on variables. -/
private lemma comp_comp_naturality {D : Type*} [Category* D] {X₀ X₁ X₂ Y₀ Y₁ Y₂ : D}
    (iC : X₀ ⟶ X₁) (eC : X₁ ⟶ X₂) (iD : Y₀ ⟶ Y₁) (eD : Y₁ ⟶ Y₂) (a : X₀ ⟶ Y₀) (b : X₁ ⟶ Y₁)
    (c : X₂ ⟶ Y₂) (h₁ : a ≫ iD = iC ≫ b) (h₂ : b ≫ eD = eC ≫ c) :
    a ≫ iD ≫ eD = (iC ≫ eC) ≫ c := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- A functor carries a commutative square to a commutative square; stated on variables. -/
private lemma map_comp_map_eq {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {X₀ X₁ X₂ X₃ : C} {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₃} {c : X₀ ⟶ X₂} {d : X₂ ⟶ X₃}
    (h : a ≫ b = c ≫ d) : G.map a ≫ G.map b = G.map c ≫ G.map d := by
  rw [← G.map_comp, h, G.map_comp]

/-- **The identification `RΓ_c(X'_{k̄}, g⁻¹ K) ≅ RΓ_c(X_{k̄}, K)` is natural in `K`.** -/
theorem compactSupportFieldExtensionIso_hom_naturality
    {K L : CochainComplex.Plus (EtaleModules.{u, r} Λ X)} (φ : K ⟶ L) :
    (compactSupportFrobeniusFunctor.{u, r} Λ (pullback.snd f (specAlgebraMap k k'))
        (compactificationFieldBaseChange f j k') kbar).map
        ((etaleModuleInverseImage.{u, r} Λ
          (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.map φ) ≫
      (compactSupportFieldExtensionIso Λ f j k' kbar L).hom =
    (compactSupportFieldExtensionIso Λ f j k' kbar K).hom ≫
      (compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).map φ := by
  have hι : (etaleModuleExtensionByZero.{u, r} Λ
        (compactificationFieldBaseChange f j k').immersion).mapCochainComplexPlus.map
        ((etaleModuleInverseImage.{u, r} Λ
          (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.map φ) ≫
      (compactificationFieldBaseChangeExtensionByZeroComplexIso Λ f j k' L).hom =
      (compactificationFieldBaseChangeExtensionByZeroComplexIso Λ f j k' K).hom ≫
        (etaleModuleInverseImage.{u, r} Λ
            (extensionProj (Over.mk j.toBase) k')).mapCochainComplexPlus.map
          ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.map φ) := by
    ext n : 2
    exact (compactificationFieldBaseChangeExtensionByZeroIso Λ f j k').hom.naturality (φ.hom.f n)
  refine comp_comp_naturality _ _ _ _ _ _ _ ?_
    (frobeniusExtensionCohomologyIso_hom_naturality Λ (Over.mk j.toBase) k' kbar
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.map φ))
  exact map_comp_map_eq (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (map_comp_map_eq (etaleModuleDerivedDirectImage.{u, r} Λ
        (pullback.snd (extensionOver (Over.mk j.toBase) k').hom (specAlgebraMap k' kbar)))
      (map_comp_map_eq DerivedCategory.Plus.Q
        (map_comp_map_eq (etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj (extensionOver (Over.mk j.toBase) k') kbar)).mapCochainComplexPlus
            hι)))

end Comparison

section Power

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (k' : Type u) [Field k'] [Algebra k k']
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar]
  [Fintype k'] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
  (hcard : Fintype.card k = p ^ q)

/-- **The Frobenius of `X ×_k k'` is the power of the Frobenius of `X`.**  If `k'` has
`q ^ (m + 1)` elements, the identification `RΓ_c(X'_{k̄}, g⁻¹ K) ≅ RΓ_c(X_{k̄}, K)` carries the
canonical Frobenius action of `X' = X ×_k k'` over `k'` to the `(m + 1)`-st power of the canonical
Frobenius action of `X` over `k`. -/
theorem compactSupportFieldExtensionIso_comm (m : ℕ)
    (hcard' : Fintype.card k' = p ^ (q * (m + 1)))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    canonicalCompactSupportFrobenius.{u, 0} Λ (pullback.snd f (specAlgebraMap k k'))
        (compactificationFieldBaseChange f j k') kbar p (q * (m + 1)) hcard'
        ((etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.obj K) ≫
      (compactSupportFieldExtensionIso Λ f j k' kbar K).hom =
    (compactSupportFieldExtensionIso Λ f j k' kbar K).hom ≫
      ((End.of (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard K)) ^ (m + 1)).asHom := by
  have h₁ := frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ)
    (extensionOver (Over.mk j.toBase) k') kbar p (q * (m + 1)) hcard'
    (compactificationFieldBaseChangeExtensionByZeroComplexIso Λ f j k' K).hom
  have h₂ := frobeniusExtensionCohomologyIso_comm Λ (Over.mk j.toBase) k' kbar p q hcard m hcard'
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K)
  exact comp_comp_naturality _ _ _ _ _ _ _ h₁.symm h₂

end Power

end Stacks.EtaleCohomology

end
