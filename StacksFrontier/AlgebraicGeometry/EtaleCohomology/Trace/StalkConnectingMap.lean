module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DirectImageConnectingMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint

/-!
# The stalk of `j_* G` at a missing point maps to `H¹_c` of the open

Let `W` be a scheme over a finite field with a compactification, `j : V ⟶ W` an open immersion,
`i : Z ⟶ W` the complementary closed immersion and `y` a point of `Z`. Suppose that the stalk at
the geometric point over `y` embeds into `H⁰_c(W_k̄, i_* i⁻¹ -)`, naturally, carrying the
geometric Frobenius of `κ(y)` to `(π_W^*) ^ d` (this is
`Stacks.EtaleCohomology.ClosedPartStalkCompactSupportInput`). Compose that embedding, at `j_* G`,
with the map `H⁰_c(W_k̄, i_* i⁻¹ j_* G) ⟶ H¹_c(V_k̄, G)` of
`Stacks.EtaleCohomology.directImageConnecting`. The result is a map

`(j_* G)_ȳ ⟶ H¹_c(V_k̄, G)`,

natural in `G`. It carries the Frobenius of `κ(y)` to `(π_V^*) ^ d`, and it is injective when
`H⁰_c(W_k̄, j_* G) = 0`. On the levels of `ℱ_τ` this is the inclusion `H⁰_loc ⊆ H¹_c` of Weil II
1.8 ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

The standard model `HasDerivedCategory.standard` is used because compactly supported cohomology is
defined there.

## Main definitions

* `Stacks.EtaleCohomology.stalkConnecting`.

## Main results

* `Stacks.EtaleCohomology.stalkConnecting_naturality`,
  `Stacks.EtaleCohomology.stalkConnecting_frobenius`,
  `Stacks.EtaleCohomology.injective_stalkConnecting`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {W V Z : Scheme.{u}}
  (fW : W ⟶ Spec (.of k)) (jWb : CompactificationOf (Over.mk fW))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)
  (jW : V ⟶ W) [IsOpenImmersion jW] (iZ : Z ⟶ W) [IsClosedImmersion iZ]
  (hij : Set.range jW.base = (Set.range iZ.base)ᶜ) (y : W)
  (s : (Scheme.pointSmallEtale (Stacks.Frobenius.geometricPointAt W y).hom).sheafFiber ⟶
    etaleModuleClosedPart Λ iZ ⋙ compactSupportSheafCohomology Λ fW jWb kbar 0)

/-- **The map `(j_* G)_ȳ ⟶ H¹_c(V_k̄, G)`**: the embedding `s` of the stalk into
`H⁰_c(W_k̄, i_* i⁻¹ j_* G)`, followed by the connecting map. -/
public def stalkConnecting (G : EtaleModules.{u, 0} Λ V) :
    (Scheme.pointSmallEtale (Stacks.Frobenius.geometricPointAt W y).hom).sheafFiber.obj
        ((etaleModuleDirectImage.{u, 0} Λ jW).obj G) ⟶
      (compactSupportSheafCohomology Λ (jW ≫ fW) (jWb.restrictOpen jW) kbar 1).obj G :=
  s.app ((etaleModuleDirectImage.{u, 0} Λ jW).obj G) ≫
    directImageConnecting Λ fW jWb kbar p q hcard jW iZ hij G

/-- **The map `(j_* G)_ȳ ⟶ H¹_c(V_k̄, G)` is natural in `G`.** -/
public theorem stalkConnecting_naturality {G G' : EtaleModules.{u, 0} Λ V} (g : G ⟶ G') :
    (Scheme.pointSmallEtale (Stacks.Frobenius.geometricPointAt W y).hom).sheafFiber.map
        ((etaleModuleDirectImage.{u, 0} Λ jW).map g) ≫
        stalkConnecting Λ fW jWb kbar p q hcard jW iZ hij y s G' =
      stalkConnecting Λ fW jWb kbar p q hcard jW iZ hij y s G ≫
        (compactSupportSheafCohomology Λ (jW ≫ fW) (jWb.restrictOpen jW) kbar 1).map g := by
  dsimp only [stalkConnecting]
  rw [reassoc_of% (s.naturality ((etaleModuleDirectImage.{u, 0} Λ jW).map g)), Category.assoc]
  exact congrArg (s.app _ ≫ ·)
    (directImageConnecting_naturality Λ fW jWb kbar p q hcard jW iZ hij g)

/-- **The map `(j_* G)_ȳ ⟶ H¹_c(V_k̄, G)` is injective** when `s` is and
`H⁰_c(W_k̄, j_* G) = 0`. -/
public theorem injective_stalkConnecting (G : EtaleModules.{u, 0} Λ V)
    (hs : Function.Injective (s.app ((etaleModuleDirectImage.{u, 0} Λ jW).obj G)).hom)
    (h : IsZero ((compactSupportSheafCohomology Λ fW jWb kbar 0).obj
      ((etaleModuleDirectImage.{u, 0} Λ jW).obj G))) :
    Function.Injective (stalkConnecting Λ fW jWb kbar p q hcard jW iZ hij y s G).hom :=
  (injective_directImageConnecting Λ fW jWb kbar p q hcard jW iZ hij G h).comp hs

/-- The connecting map intertwines the powers of the geometric Frobenius. -/
public theorem directImageConnecting_frobenius_pow (G : EtaleModules.{u, 0} Λ V) (d : ℕ) :
    (directImageConnecting Λ fW jWb kbar p q hcard jW iZ hij G).hom ∘ₗ
        (((compactSupportSheafFrobenius Λ fW jWb kbar p q hcard 0).app
          ((etaleModuleClosedPart Λ iZ).obj
            ((etaleModuleDirectImage.{u, 0} Λ jW).obj G))).hom ^ d) =
      (((compactSupportSheafFrobenius Λ (jW ≫ fW) (jWb.restrictOpen jW) kbar p q hcard 1).app
          G).hom ^ d) ∘ₗ (directImageConnecting Λ fW jWb kbar p q hcard jW iZ hij G).hom := by
  have h := congrArg ModuleCat.Hom.hom
    (directImageConnecting_frobenius Λ fW jWb kbar p q hcard jW iZ hij G)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc,
      ih, LinearMap.comp_assoc, h, ← LinearMap.comp_assoc]

/-- **The map `(j_* G)_ȳ ⟶ H¹_c(V_k̄, G)` carries the geometric Frobenius of `κ(y)` to
`(π_V^*) ^ d`** when `s` carries it to `(π_W^*) ^ d`. -/
public theorem stalkConnecting_frobenius [Finite (W.residueField y)] (G : EtaleModules.{u, 0} Λ V)
    (d : ℕ)
    (hs : (s.app ((etaleModuleDirectImage.{u, 0} Λ jW).obj G)).hom ∘ₗ
        (Stacks.Frobenius.frobeniusStalk (ModuleCat.{u + 1} Λ) W y
          ((etaleModuleDirectImage.{u, 0} Λ jW).obj G)).hom =
      (((compactSupportSheafFrobenius Λ fW jWb kbar p q hcard 0).app
          ((etaleModuleClosedPart Λ iZ).obj
            ((etaleModuleDirectImage.{u, 0} Λ jW).obj G))).hom ^ d) ∘ₗ
        (s.app ((etaleModuleDirectImage.{u, 0} Λ jW).obj G)).hom) :
    (stalkConnecting Λ fW jWb kbar p q hcard jW iZ hij y s G).hom ∘ₗ
        (Stacks.Frobenius.frobeniusStalk (ModuleCat.{u + 1} Λ) W y
          ((etaleModuleDirectImage.{u, 0} Λ jW).obj G)).hom =
      (((compactSupportSheafFrobenius Λ (jW ≫ fW) (jWb.restrictOpen jW) kbar p q hcard 1).app
          G).hom ^ d) ∘ₗ (stalkConnecting Λ fW jWb kbar p q hcard jW iZ hij y s G).hom := by
  dsimp only [stalkConnecting]
  rw [ModuleCat.hom_comp, LinearMap.comp_assoc, hs, ← LinearMap.comp_assoc,
    directImageConnecting_frobenius_pow, LinearMap.comp_assoc]

end Stacks.EtaleCohomology
