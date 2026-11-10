module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ComponentsOverSeparableClosure
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.ConjugateComponents
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.AffineOfNoProperComponent

/-!
# Conjugate components of a base change have the same complementary degree

Let `X` be a scheme, `C ⊆ X` a closed subscheme, `X' ⊆ X` the scheme-theoretic closure of the
complement of `C`, and let `deg(C)` denote the degree of `C ∩ X'` over the global functions of
`C`, the quantity clause (4) of `AlgebraicGeometry.IsRationalBridge` constrains to be two. This
file proves that `deg` is unchanged by an isomorphism of the ambient scheme, and draws the
consequence for the Galois action on the irreducible components of a base change: two components
of `X_K` with the same image in `X` have the same complementary degree.

## Main results

* `AlgebraicGeometry.finrank_globalSections_comap_of_isIso`: for `I ≤ J` closed subschemes of `Y`
  and `φ : X ⟶ Y` an isomorphism, the degree of `J` over `I` equals the degree of the inverse
  image of `J` over the inverse image of `I`. The isomorphism is not assumed to lie over any
  base, so this transports a *relative* degree along a semilinear comparison.
* `AlgebraicGeometry.finrank_intersectionWithComplementaryCurve_comap_of_isIso`: the same for the
  intersection with the complementary curve, which is not a fixed closed subscheme but is itself
  built from `I`.
* `AlgebraicGeometry.finrank_intersectionWithComplementaryCurve_vanishingIdeal_eq_of_image_eq`:
  two reduced closed subschemes carried onto one another by an automorphism of the ambient scheme
  have the same complementary degree, and
  `AlgebraicGeometry.finrank_intersectionWithComplementaryCurve_component_eq_of_image_eq` at an
  irreducible component.
* `AlgebraicGeometry.finrank_intersectionWithComplementaryCurve_eq_of_baseChangeMap_eq`: all
  irreducible components of `X_K` lying over one irreducible component of `X` have the same
  complementary degree, for `K/k` normal.
* `AlgebraicGeometry.finrank_intersectionWithComplementaryCurve_eq_of_galoisBaseChangeMap`: the
  previous statement for the self-map of a base change attached to a `k`-automorphism of `K`.

## Implementation notes

The complementary curve ideal is the kernel of the open immersion of the complement of the
support, so transporting it needs only the flat-pullback statement
`AlgebraicGeometry.complementaryCurveIdeal_comap`, an isomorphism being flat.

What is new here is the degree. An isomorphism `φ : X ⟶ Y` identifies the inverse image of a
closed subscheme with the subscheme itself
(`AlgebraicGeometry.comapSubschemeIso`), compatibly with the two closed immersions, and the
inclusion of a smaller closed subscheme into a larger one is transported by that identification.
Taking global functions turns this into a commuting square of rings with two of its sides
isomorphisms, and `Algebra.finrank_eq_of_equiv_equiv` reads a dimension off either side. The
isomorphism of rings along the bottom need not be the identity — for the Galois self-map of a
base change `X_K ⟶ X_K` attached to `σ : K ≃ₐ[k] K` it restricts to `σ` on `K` — so the
dimension is preserved but no `K`-linear comparison exists; this is exactly why the statement is
about `Module.finrank` over the global functions of the subscheme and not over a fixed field.

## Why this is wanted: the symmetry input of Tag 0E65

[Stacks, Tag 0E65] asserts that the base change of a rational bridge is a finite *disjoint* union
of rational bridges. That is false, and
`AlgebraicGeometry.exists_iso_sigma_isRationalBridge_baseChange` of
`Curves/ContractingRationalBridges/BaseChange.lean` proves it with the geometric integrality that
repairs it; the erratum notes there carry the counterexample. The *union* form —
every irreducible component of `C_K` is a rational bridge of `X_K` — is true at the tag's own
hypotheses, and the one thing the bookkeeping cannot supply is a reason for the two X'-points to
be distributed evenly among the components.

That reason is this file. The counting available over the base — the dual-graph genus formula of
`Curves/GenusCurve/GenusDualGraph.lean` together with `deg(C ∩ X') = 2[k' : k]` — is symmetric in
the distribution and only pins its sum, so it leaves standing a chain `W₁ ∪ W₂ ∪ W₃` of three
genus-zero pieces meeting in degree one with both X'-points on `W₂`: the complementary degrees
are then `(1, 4, 1)`, every count is satisfied, and `W₁`, `W₃` are rational tails rather than
bridges. What excludes it is that the components of `C_Ω` over an algebraically closed `Ω ⊇ K`
are a single orbit of `Aut(Ω/k)`, because `C` is irreducible over `k`; the self-maps attached to
that group are isomorphisms of `X_Ω` carrying one component onto another, so by the theorems below
all the complementary degrees are equal. With `s` components per connected piece, `e` the degree
in which each meets `X'_Ω`, and `[k' : k]` connected pieces, equality of the `e`'s turns
`∑ e = 2[k' : k]` into `s · e = 2`: hence `s ≤ 2`, and a rational bridge is either geometrically
integral over `k'` or has exactly two geometric components meeting in one point with one X'-point
on each. The three-component chain cannot occur at all.

## References

* [Stacks Project, Tag 0E65](https://stacks.math.columbia.edu/tag/0E65)
* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 04KY](https://stacks.math.columbia.edu/tag/04KY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsIso φ]

/-- Taking inverse images along an isomorphism and along its inverse are mutually inverse
operations on closed subschemes. -/
private theorem base_inv_base (x : Y) : φ.base ((inv φ).base x) = x :=
  congrArg (fun g : Y ⟶ Y => g.base x) (IsIso.inv_hom_id φ)

/-- Inverse image along an isomorphism is an order isomorphism of closed subschemes, with
inverse the inverse image along the inverse isomorphism. -/
theorem le_comap_iff_comap_inv_le {I : Y.IdealSheafData} {J : X.IdealSheafData} :
    J ≤ I.comap φ ↔ J.comap (inv φ) ≤ I := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa only [comap_comap_inv] using comap_mono (inv φ) h
  · simpa only [← comap_comp, IsIso.hom_inv_id, comap_id] using comap_mono φ h

/-- **The inverse image along an isomorphism of a reduced closed subscheme is the reduced closed
subscheme on the inverse image of its support.** Both sides are characterized by the Galois
connection between supports and vanishing ideals, which inverse image along an isomorphism
respects because it is an order isomorphism compatible with taking supports. -/
theorem comap_vanishingIdeal (Z : Closeds Y) :
    (vanishingIdeal Z).comap φ = vanishingIdeal (Z.preimage φ.continuous) := by
  apply le_antisymm
  · rw [← le_support_iff_le_vanishingIdeal, support_comap]
    exact fun x hx => (le_support_iff_le_vanishingIdeal.mpr (le_refl (vanishingIdeal Z))) hx
  · rw [le_comap_iff_comap_inv_le, ← le_support_iff_le_vanishingIdeal, support_comap]
    intro x hx
    refine (le_support_iff_le_vanishingIdeal.mpr
      (le_refl (vanishingIdeal (Z.preimage φ.continuous)))) ?_
    change φ.base ((inv φ).base x) ∈ Z
    rwa [base_inv_base]

end Scheme.IdealSheafData

/-- The global functions on the two sides of an isomorphism of schemes are isomorphic. -/
private noncomputable def appTopIso {A B : Scheme.{u}} (e : A ≅ B) : Γ(B, ⊤) ≅ Γ(A, ⊤) :=
  Scheme.Γ.mapIso e.op

/-- The base change of an isomorphism along any morphism is an isomorphism. -/
theorem isIso_pullback_snd_of_isIso {X Y Z : Scheme.{u}} (φ : X ⟶ Y) [IsIso φ]
    (i : Z ⟶ Y) : IsIso (pullback.snd φ i) :=
  MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u})
    (IsPullback.of_hasPullback φ i) (MorphismProperty.isomorphisms.infer_property φ)

/-- **The inverse image of a closed subscheme along an isomorphism of the ambient scheme is
isomorphic to it.** -/
noncomputable def comapSubschemeIso {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsIso φ]
    (I : Y.IdealSheafData) : (I.comap φ).subscheme ≅ I.subscheme :=
  letI := isIso_pullback_snd_of_isIso φ I.subschemeι
  I.comapIso φ ≪≫ asIso (pullback.snd φ I.subschemeι)

/-- The identification of a closed subscheme with its inverse image along an isomorphism is
compatible with the two closed immersions. -/
theorem comapSubschemeIso_hom_subschemeι {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsIso φ]
    (I : Y.IdealSheafData) :
    (comapSubschemeIso φ I).hom ≫ I.subschemeι = (I.comap φ).subschemeι ≫ φ := by
  let := isIso_pullback_snd_of_isIso φ I.subschemeι
  dsimp [comapSubschemeIso]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

private theorem comapSubschemeIso_inv_subschemeι {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsIso φ]
    (I : Y.IdealSheafData) :
    (comapSubschemeIso φ I).inv ≫ (I.comap φ).subschemeι = I.subschemeι ≫ inv φ := by
  rw [← cancel_mono φ, Category.assoc, Category.assoc,
    ← comapSubschemeIso_hom_subschemeι φ I, Iso.inv_hom_id_assoc,
    IsIso.inv_hom_id, Category.comp_id]

/-- The relative degree of one closed subscheme in another depends on the two closed subschemes
only through their values. -/
private theorem finrank_globalSections_congr {Y : Scheme.{u}} {I I' J J' : Y.IdealSheafData}
    (h : I ≤ J) (h' : I' ≤ J') (e : I = I') (e' : J = J') :
    letI : Algebra Γ(I.subscheme, ⊤) Γ(J.subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion h).appTop.hom.toAlgebra
    letI : Algebra Γ(I'.subscheme, ⊤) Γ(J'.subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion h').appTop.hom.toAlgebra
    Module.finrank Γ(I.subscheme, ⊤) Γ(J.subscheme, ⊤)
      = Module.finrank Γ(I'.subscheme, ⊤) Γ(J'.subscheme, ⊤) := by
  subst e e'
  rfl

/-- **The relative degree of one closed subscheme in another is unchanged by an isomorphism of
the ambient scheme.** For `I ≤ J` closed subschemes of `Y` and `φ : X ⟶ Y` an isomorphism, the
dimension of the global functions of the inverse image of `J` over those of the inverse image of
`I` equals the dimension of the global functions of `J` over those of `I`.

The isomorphism is not assumed to lie over anything, so the comparison of global functions is
only an isomorphism of rings; `Module.finrank` is insensitive to that, which is what makes the
statement useful for the self-maps of a base change attached to automorphisms of the extension
field. -/
theorem finrank_globalSections_comap_of_isIso {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsIso φ]
    {I J : Y.IdealSheafData} (h : I ≤ J) (h' : I.comap φ ≤ J.comap φ) :
    letI : Algebra Γ(I.subscheme, ⊤) Γ(J.subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion h).appTop.hom.toAlgebra
    letI : Algebra Γ((I.comap φ).subscheme, ⊤) Γ((J.comap φ).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion h').appTop.hom.toAlgebra
    Module.finrank Γ((I.comap φ).subscheme, ⊤) Γ((J.comap φ).subscheme, ⊤)
      = Module.finrank Γ(I.subscheme, ⊤) Γ(J.subscheme, ⊤) := by
  let : Algebra Γ(I.subscheme, ⊤) Γ(J.subscheme, ⊤) :=
    (Scheme.IdealSheafData.inclusion h).appTop.hom.toAlgebra
  let : Algebra Γ((I.comap φ).subscheme, ⊤) Γ((J.comap φ).subscheme, ⊤) :=
    (Scheme.IdealSheafData.inclusion h').appTop.hom.toAlgebra
  have hsq : Scheme.IdealSheafData.inclusion h ≫ (comapSubschemeIso φ I).inv =
      (comapSubschemeIso φ J).inv ≫ Scheme.IdealSheafData.inclusion h' := by
    rw [← cancel_mono (I.comap φ).subschemeι, Category.assoc, Category.assoc,
      comapSubschemeIso_inv_subschemeι, Scheme.IdealSheafData.inclusion_subschemeι,
      ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι,
      comapSubschemeIso_inv_subschemeι]
  refine Algebra.finrank_eq_of_equiv_equiv
    (appTopIso (comapSubschemeIso φ I)).symm.commRingCatIsoToRingEquiv
    (appTopIso (comapSubschemeIso φ J)).symm.commRingCatIsoToRingEquiv ?_
  have happ := congrArg (fun t : J.subscheme ⟶ (I.comap φ).subscheme => t.appTop) hsq
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at happ
  ext x
  exact congrArg (fun t : Γ((I.comap φ).subscheme, ⊤) ⟶ Γ(J.subscheme, ⊤) => t.hom x) happ

/-- **The degree of the intersection with the complementary curve is unchanged by an isomorphism
of the ambient scheme.** This is `AlgebraicGeometry.finrank_globalSections_comap_of_isIso` at the
pair `C ≤ C ∩ X'`, which is not a pair of fixed closed subschemes: the larger one is built from
the smaller, and that construction commutes with inverse image along an isomorphism by
`AlgebraicGeometry.intersectionWithComplementaryCurveIdeal_comap`. -/
theorem finrank_intersectionWithComplementaryCurve_comap_of_isIso {X Y : Scheme.{u}}
    (φ : X ⟶ Y) [IsIso φ] (I : Y.IdealSheafData)
    [QuasiCompact (Scheme.Opens.ι I.support.compl)] :
    letI : Algebra Γ((I.comap φ).subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal (I.comap φ)).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : I.comap φ ≤
          intersectionWithComplementaryCurveIdeal (I.comap φ))).appTop.hom.toAlgebra
    letI : Algebra Γ(I.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal I).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : I ≤ intersectionWithComplementaryCurveIdeal I)).appTop.hom.toAlgebra
    Module.finrank Γ((I.comap φ).subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal (I.comap φ)).subscheme, ⊤)
      = Module.finrank Γ(I.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal I).subscheme, ⊤) := by
  exact (finrank_globalSections_congr
    (le_sup_left : I.comap φ ≤ intersectionWithComplementaryCurveIdeal (I.comap φ))
    (Scheme.IdealSheafData.comap_mono φ
      (le_sup_left : I ≤ intersectionWithComplementaryCurveIdeal I))
    rfl (intersectionWithComplementaryCurveIdeal_comap I φ)).trans
    (finrank_globalSections_comap_of_isIso φ
      (le_sup_left : I ≤ intersectionWithComplementaryCurveIdeal I) _)

/-- An automorphism of a scheme carries the reduced structure on a closed set to the reduced
structure on its image. -/
theorem vanishingIdeal_comap_of_image_eq {Y : Scheme.{u}} (φ : Y ⟶ Y) [IsIso φ]
    (S T : Closeds Y) (h : φ.base '' (S : Set Y) = (T : Set Y)) :
    Scheme.IdealSheafData.vanishingIdeal S =
      (Scheme.IdealSheafData.vanishingIdeal T).comap φ := by
  rw [Scheme.IdealSheafData.comap_vanishingIdeal]
  congr 1
  ext1
  change (S : Set Y) = φ.base ⁻¹' (T : Set Y)
  have hinj : Function.Injective φ.base :=
    Function.LeftInverse.injective (g := (inv φ).base) fun a =>
      congrArg (fun g : Y ⟶ Y => g.base a) (IsIso.hom_inv_id φ)
  rw [← h, Set.preimage_image_eq _ hinj]

/-- An automorphism of a scheme carries the reduced structure on one irreducible component to the
reduced structure on its image. -/
theorem componentIdealSheafData_comap {Y : Scheme.{u}} (φ : Y ⟶ Y) [IsIso φ]
    (Z W : irreducibleComponents Y) (h : φ.base '' Z.1 = W.1) :
    Stacks.AffineNoProperComponent.componentIdealSheafData Z =
      (Stacks.AffineNoProperComponent.componentIdealSheafData W).comap φ :=
  vanishingIdeal_comap_of_image_eq φ _ _ h

/-- **Two reduced closed subschemes carried onto one another by an automorphism of the ambient
scheme have the same complementary degree.** The degree is that of the intersection with the
scheme-theoretic closure of the complement, taken over the global functions of the subscheme:
clause (4) of `AlgebraicGeometry.IsRationalBridge`.

Stated for the reduced structure on a closed set rather than for an irreducible component,
because the descent in Tag 0E65 needs it at the connected components of a union of components,
not only at a single one. -/
theorem finrank_intersectionWithComplementaryCurve_vanishingIdeal_eq_of_image_eq
    {Y : Scheme.{u}} [IsNoetherian Y] (φ : Y ⟶ Y) [IsIso φ] (S T : Closeds Y)
    (h : φ.base '' (S : Set Y) = (T : Set Y)) :
    letI IS := Scheme.IdealSheafData.vanishingIdeal S
    letI IT := Scheme.IdealSheafData.vanishingIdeal T
    letI : Algebra Γ(IS.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IS).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : IS ≤ intersectionWithComplementaryCurveIdeal IS)).appTop.hom.toAlgebra
    letI : Algebra Γ(IT.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IT).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : IT ≤ intersectionWithComplementaryCurveIdeal IT)).appTop.hom.toAlgebra
    Module.finrank Γ(IS.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IS).subscheme, ⊤)
      = Module.finrank Γ(IT.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IT).subscheme, ⊤) := by
  set IS := Scheme.IdealSheafData.vanishingIdeal S
  set IT := Scheme.IdealSheafData.vanishingIdeal T
  have hcomap : IS = IT.comap φ := vanishingIdeal_comap_of_image_eq φ S T h
  exact (finrank_globalSections_congr
    (le_sup_left : IS ≤ intersectionWithComplementaryCurveIdeal IS)
    (le_sup_left : IT.comap φ ≤ intersectionWithComplementaryCurveIdeal (IT.comap φ))
    hcomap (congrArg intersectionWithComplementaryCurveIdeal hcomap)).trans
    (finrank_intersectionWithComplementaryCurve_comap_of_isIso φ IT)

/-- **Two irreducible components carried onto one another by an automorphism of the ambient
scheme have the same complementary degree.** The degree is that of the intersection of the
component with the scheme-theoretic closure of its complement, over the global functions of the
component: clause (4) of `AlgebraicGeometry.IsRationalBridge`. -/
theorem finrank_intersectionWithComplementaryCurve_component_eq_of_image_eq
    {Y : Scheme.{u}} [IsNoetherian Y] (φ : Y ⟶ Y) [IsIso φ]
    (Z W : irreducibleComponents Y) (h : φ.base '' Z.1 = W.1) :
    letI IZ := Stacks.AffineNoProperComponent.componentIdealSheafData Z
    letI IW := Stacks.AffineNoProperComponent.componentIdealSheafData W
    letI : Algebra Γ(IZ.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IZ).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : IZ ≤ intersectionWithComplementaryCurveIdeal IZ)).appTop.hom.toAlgebra
    letI : Algebra Γ(IW.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IW).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : IW ≤ intersectionWithComplementaryCurveIdeal IW)).appTop.hom.toAlgebra
    Module.finrank Γ(IZ.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IZ).subscheme, ⊤)
      = Module.finrank Γ(IW.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IW).subscheme, ⊤) :=
  finrank_intersectionWithComplementaryCurve_vanishingIdeal_eq_of_image_eq φ
    ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
    ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ h

/-- **Conjugate irreducible components of a base change have the same complementary degree.**
Let `X` be a scheme over a field `k`, let `K/k` be a field extension and let `σ : K ≃ₐ[k] K`.
The self-map of `X_K` attached to `σ` is an isomorphism over `X`
(`AlgebraicGeometry.galoisBaseChangeMap`, `AlgebraicGeometry.isIso_galoisBaseChangeMap`), so if it
carries one irreducible component of `X_K` onto another, the two have the same degree of
intersection with the closure of their complements.

By Tag 04KY (`AlgebraicGeometry.fiber_irreducibleComponentsBaseChangeMap_eq_orbit`) every fibre
of the map on irreducible components is such an orbit, so for an irreducible `X` all the
components of `X_K` have one and the same complementary degree. That is the symmetry input Tag
0E65 needs and the counting over the base cannot give; see the module documentation. -/
theorem finrank_intersectionWithComplementaryCurve_eq_of_galoisBaseChangeMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsNoetherian (pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))]
    (σ : K ≃ₐ[k] K)
    (Z W : irreducibleComponents (pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (h : (galoisBaseChangeMap k K X f σ).base '' Z.1 = W.1) :
    letI IZ := Stacks.AffineNoProperComponent.componentIdealSheafData Z
    letI IW := Stacks.AffineNoProperComponent.componentIdealSheafData W
    letI : Algebra Γ(IZ.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IZ).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : IZ ≤ intersectionWithComplementaryCurveIdeal IZ)).appTop.hom.toAlgebra
    letI : Algebra Γ(IW.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IW).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : IW ≤ intersectionWithComplementaryCurveIdeal IW)).appTop.hom.toAlgebra
    Module.finrank Γ(IZ.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IZ).subscheme, ⊤)
      = Module.finrank Γ(IW.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IW).subscheme, ⊤) := by
  have := isIso_galoisBaseChangeMap k K X f σ
  exact finrank_intersectionWithComplementaryCurve_component_eq_of_image_eq
    (galoisBaseChangeMap k K X f σ) Z W h

/-- **All irreducible components of a base change lying over one irreducible component of the
original scheme have the same complementary degree.** By Tag 04KY the fibres of the map on
irreducible components are the orbits of `K ≃ₐ[k] K`, which act through isomorphisms of `X_K`
over `X`, and the complementary degree is an isomorphism invariant.

Normality of `K/k` is what makes the fibres orbits; it is a hypothesis on the extension used to
compute, not on the extension one is interested in. For an arbitrary extension `L/k` one applies
this at a separably closed `Ω ⊇ L`, whose separable closure over `k` is normal over `k`, and
transports the degrees back along the base change `Ω/L`, which does not change them. -/
theorem finrank_intersectionWithComplementaryCurve_eq_of_baseChangeMap_eq
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Normal k K]
    (X : Over (Spec (.of k)))
    [IsNoetherian (pullback (C := Scheme.{u}) X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))]
    (Z W : (galoisActionOnGeometricIrreducibleComponents k K X).V)
    (h : irreducibleComponentsBaseChangeMap k K X Z =
      irreducibleComponentsBaseChangeMap k K X W) :
    letI IZ := Stacks.AffineNoProperComponent.componentIdealSheafData Z
    letI IW := Stacks.AffineNoProperComponent.componentIdealSheafData W
    letI : Algebra Γ(IZ.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IZ).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : IZ ≤ intersectionWithComplementaryCurveIdeal IZ)).appTop.hom.toAlgebra
    letI : Algebra Γ(IW.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IW).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : IW ≤ intersectionWithComplementaryCurveIdeal IW)).appTop.hom.toAlgebra
    Module.finrank Γ(IZ.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IZ).subscheme, ⊤)
      = Module.finrank Γ(IW.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal IW).subscheme, ⊤) := by
  obtain ⟨σ, hσ⟩ :=
    exists_algEquiv_image_eq_of_irreducibleComponentsBaseChangeMap_eq k K X Z W h
  refine finrank_intersectionWithComplementaryCurve_eq_of_galoisBaseChangeMap k K
    X.left X.hom σ Z W ?_
  rw [← hσ]
  rfl

end AlgebraicGeometry

end
