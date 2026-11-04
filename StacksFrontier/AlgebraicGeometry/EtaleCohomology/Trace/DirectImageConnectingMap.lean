module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportConnectingMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafExcisionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle

/-!
# The boundary of `j_* G` at the missing points maps to `H¹_c` of the open

Let `W` be a scheme over a finite field `k` with a compactification `j̄`, `j : V ⟶ W` an open
immersion and `i : Z ⟶ W` the complementary closed immersion. For a sheaf `G` of `Λ`-modules on
`V`, the open–closed sequence of `j_* G` on `W`,

`0 → j_! j⁻¹ j_* G → j_* G → i_* i⁻¹ j_* G → 0`,

has a connecting map `H⁰_c(W_k̄, i_* i⁻¹ j_* G) ⟶ H¹_c(W_k̄, j_! j⁻¹ j_* G)`. Since
`j⁻¹ j_* G = G` and `H¹_c(W_k̄, j_! G) = H¹_c(V_k̄, G)` (for the induced compactification of `V`),
this is a map

`H⁰_c(W_k̄, i_* i⁻¹ j_* G) ⟶ H¹_c(V_k̄, G)`,

natural in `G` and commuting with the geometric Frobenius. It is injective when
`H⁰_c(W_k̄, j_* G) = 0`. This is the map `H⁰_loc ⟶ H¹_c` of Weil II 1.8
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) before the stalk at the missing point is
singled out.

The standard model `HasDerivedCategory.standard` is used because compactly supported cohomology is
defined there.

## Main definitions

* `Stacks.EtaleCohomology.moduleOpenClosedShortComplex`: the open–closed sequence of a sheaf.
* `Stacks.EtaleCohomology.directImageConnecting`: the map
  `H⁰_c(W_k̄, i_* i⁻¹ j_* G) ⟶ H¹_c(V_k̄, G)`.

## Main results

* `Stacks.EtaleCohomology.directImageConnecting_naturality`,
  `Stacks.EtaleCohomology.directImageConnecting_frobenius`,
  `Stacks.EtaleCohomology.injective_directImageConnecting`.
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
  (hij : Set.range jW.base = (Set.range iZ.base)ᶜ)

/-- **The open–closed sequence** `0 → j_! j⁻¹ G → G → i_* i⁻¹ G → 0` of a sheaf on `W`. -/
public abbrev moduleOpenClosedShortComplex (G : EtaleModules.{u, 0} Λ W) :
    ShortComplex (EtaleModules.{u, 0} Λ W) :=
  ShortComplex.mk ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jW).counit.app G)
    ((etaleModuleInverseImageAdj.{u, 0} Λ iZ).unit.app G)
    (etaleModuleExtensionByZero_counit_comp_inverseImage_unit Λ iZ jW hij G)

include hij in
/-- The open–closed sequence of a sheaf on `W` is short exact. -/
public lemma moduleOpenClosedShortComplex_shortExact (G : EtaleModules.{u, 0} Λ W) :
    (moduleOpenClosedShortComplex Λ jW iZ hij G).ShortExact :=
  (shortExact_etaleModuleExtensionByZero_directImage Λ iZ jW hij G).snd

/-- The open–closed sequence is functorial. -/
public abbrev moduleOpenClosedShortComplexMap {G G' : EtaleModules.{u, 0} Λ W} (g : G ⟶ G') :
    moduleOpenClosedShortComplex Λ jW iZ hij G ⟶ moduleOpenClosedShortComplex Λ jW iZ hij G' where
  τ₁ := (etaleModuleOpenPart Λ jW).map g
  τ₂ := g
  τ₃ := (etaleModuleClosedPart Λ iZ).map g
  comm₁₂ := ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jW).counit.naturality g)
  comm₂₃ := ((etaleModuleInverseImageAdj.{u, 0} Λ iZ).unit.naturality g)

/-- `j_! j⁻¹ j_* G ≅ j_! G` for an open immersion `j`, naturally in `G`. -/
public def directImageOpenPartIso :
    etaleModuleDirectImage.{u, 0} Λ jW ⋙ etaleModuleOpenPart Λ jW ≅
      etaleModuleExtensionByZero.{u, 0} Λ jW :=
  Functor.isoWhiskerRight (asIso (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ jW).counit)
    (etaleModuleExtensionByZero.{u, 0} Λ jW) ≪≫ Functor.leftUnitor _

/-- Pasting three commutative squares in a category. -/
public theorem paste_three {C : Type*} [Category* C] {a b c d a' b' c' d' : C}
    (x : a ⟶ a') (δ : a ⟶ b) (δ' : a' ⟶ b') (y : b ⟶ b') (m : b ⟶ c) (m' : b' ⟶ c')
    (z : c ⟶ c') (r : c ⟶ d) (r' : c' ⟶ d') (w : d ⟶ d') (h₁ : x ≫ δ' = δ ≫ y)
    (h₂ : y ≫ m' = m ≫ z) (h₃ : z ≫ r' = r ≫ w) :
    x ≫ δ' ≫ m' ≫ r' = (δ ≫ m ≫ r) ≫ w := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃, Category.assoc, Category.assoc]

/-- If `e.hom` intertwines the endomorphisms `f` and `g`, then `e.inv` intertwines `g` and `f`. -/
public theorem comm_inv_of_comm {C : Type*} [Category* C] {a b : C} (e : a ≅ b) (f : a ⟶ a)
    (g : b ⟶ b) (h : f ≫ e.hom = e.hom ≫ g) : g ≫ e.inv = e.inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

include hij in
/-- **The map `H⁰_c(W_k̄, i_* i⁻¹ j_* G) ⟶ H¹_c(V_k̄, G)`**: the connecting map of the open–closed
sequence of `j_* G`, followed by
`H¹_c(W_k̄, j_! j⁻¹ j_* G) ≅ H¹_c(W_k̄, j_! G) ≅ H¹_c(V_k̄, G)`. -/
public def directImageConnecting (G : EtaleModules.{u, 0} Λ V) :
    (compactSupportSheafCohomology Λ fW jWb kbar 0).obj
        ((etaleModuleClosedPart Λ iZ).obj ((etaleModuleDirectImage.{u, 0} Λ jW).obj G)) ⟶
      (compactSupportSheafCohomology Λ (jW ≫ fW) (jWb.restrictOpen jW) kbar 1).obj G :=
  compactSupportSheafδ Λ fW jWb kbar p q hcard
      (moduleOpenClosedShortComplex_shortExact Λ jW iZ hij
        ((etaleModuleDirectImage.{u, 0} Λ jW).obj G)) 0 1 (by norm_num) ≫
    (compactSupportSheafCohomology Λ fW jWb kbar 1).map ((directImageOpenPartIso Λ jW).hom.app G) ≫
    (compactSupportSheafCohomologyRestrictOpenIso Λ fW jWb kbar 1 jW).inv.app G

/-- **The map `H⁰_c(W_k̄, i_* i⁻¹ j_* G) ⟶ H¹_c(V_k̄, G)` is natural in `G`.** -/
public theorem directImageConnecting_naturality {G G' : EtaleModules.{u, 0} Λ V} (g : G ⟶ G') :
    (compactSupportSheafCohomology Λ fW jWb kbar 0).map
        ((etaleModuleClosedPart Λ iZ).map ((etaleModuleDirectImage.{u, 0} Λ jW).map g)) ≫
        directImageConnecting Λ fW jWb kbar p q hcard jW iZ hij G' =
      directImageConnecting Λ fW jWb kbar p q hcard jW iZ hij G ≫
        (compactSupportSheafCohomology Λ (jW ≫ fW) (jWb.restrictOpen jW) kbar 1).map g := by
  have h₁ := compactSupportSheafδ_naturality Λ fW jWb kbar p q hcard
    (moduleOpenClosedShortComplex_shortExact Λ jW iZ hij
      ((etaleModuleDirectImage.{u, 0} Λ jW).obj G))
    (moduleOpenClosedShortComplex_shortExact Λ jW iZ hij
      ((etaleModuleDirectImage.{u, 0} Λ jW).obj G'))
    (moduleOpenClosedShortComplexMap Λ jW iZ hij ((etaleModuleDirectImage.{u, 0} Λ jW).map g))
    0 1 (by norm_num)
  have h₂ : (compactSupportSheafCohomology Λ fW jWb kbar 1).map
        ((etaleModuleOpenPart Λ jW).map ((etaleModuleDirectImage.{u, 0} Λ jW).map g)) ≫
        (compactSupportSheafCohomology Λ fW jWb kbar 1).map
          ((directImageOpenPartIso Λ jW).hom.app G') =
      (compactSupportSheafCohomology Λ fW jWb kbar 1).map
          ((directImageOpenPartIso Λ jW).hom.app G) ≫
        (compactSupportSheafCohomology Λ fW jWb kbar 1).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jW).map g) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg _ ((directImageOpenPartIso Λ jW).hom.naturality g)
  have h₃ := (compactSupportSheafCohomologyRestrictOpenIso Λ fW jWb kbar 1 jW).inv.naturality g
  dsimp only [directImageConnecting]
  exact paste_three _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃

/-- **The map `H⁰_c(W_k̄, i_* i⁻¹ j_* G) ⟶ H¹_c(V_k̄, G)` commutes with the geometric
Frobenius.** -/
public theorem directImageConnecting_frobenius (G : EtaleModules.{u, 0} Λ V) :
    (compactSupportSheafFrobenius Λ fW jWb kbar p q hcard 0).app
        ((etaleModuleClosedPart Λ iZ).obj ((etaleModuleDirectImage.{u, 0} Λ jW).obj G)) ≫
        directImageConnecting Λ fW jWb kbar p q hcard jW iZ hij G =
      directImageConnecting Λ fW jWb kbar p q hcard jW iZ hij G ≫
        (compactSupportSheafFrobenius Λ (jW ≫ fW) (jWb.restrictOpen jW) kbar p q hcard 1).app
          G := by
  have h₁ := compactSupportSheafδ_frobenius Λ fW jWb kbar p q hcard
    (moduleOpenClosedShortComplex_shortExact Λ jW iZ hij
      ((etaleModuleDirectImage.{u, 0} Λ jW).obj G)) 0 1 (by norm_num)
  have h₂ := (compactSupportSheafFrobenius Λ fW jWb kbar p q hcard 1).naturality
    ((directImageOpenPartIso Λ jW).hom.app G)
  have h₃ := congrArg (fun t => t.app G)
    (compactSupportSheafCohomologyRestrictOpenIso_hom_frobenius Λ fW jWb kbar 1 jW p q hcard)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  have h₃' := comm_inv_of_comm
    ((compactSupportSheafCohomologyRestrictOpenIso Λ fW jWb kbar 1 jW).app G) _ _ h₃
  dsimp only [directImageConnecting]
  exact paste_three _ _ _ _ _ _ _ _ _ _ h₁ h₂.symm h₃'

include hij in
/-- **The map `H⁰_c(W_k̄, i_* i⁻¹ j_* G) ⟶ H¹_c(V_k̄, G)` is injective when
`H⁰_c(W_k̄, j_* G) = 0`.** -/
public theorem injective_directImageConnecting (G : EtaleModules.{u, 0} Λ V)
    (h : IsZero ((compactSupportSheafCohomology Λ fW jWb kbar 0).obj
      ((etaleModuleDirectImage.{u, 0} Λ jW).obj G))) :
    Function.Injective (directImageConnecting Λ fW jWb kbar p q hcard jW iZ hij G).hom := by
  have hδ := injective_compactSupportSheafδ Λ fW jWb kbar p q hcard
    (moduleOpenClosedShortComplex_shortExact Λ jW iZ hij
      ((etaleModuleDirectImage.{u, 0} Λ jW).obj G)) 0 1 (by norm_num) h
  have hi₁ : Function.Injective ((compactSupportSheafCohomology Λ fW jWb kbar 1).map
      ((directImageOpenPartIso Λ jW).hom.app G)).hom :=
    ((compactSupportSheafCohomology Λ fW jWb kbar 1).mapIso
      ((directImageOpenPartIso Λ jW).app G)).toLinearEquiv.injective
  have hi₂ : Function.Injective
      ((compactSupportSheafCohomologyRestrictOpenIso Λ fW jWb kbar 1 jW).inv.app G).hom :=
    ((compactSupportSheafCohomologyRestrictOpenIso Λ fW jWb kbar 1 jW).app
      G).symm.toLinearEquiv.injective
  exact hi₂.comp (hi₁.comp hδ)

end Stacks.EtaleCohomology
