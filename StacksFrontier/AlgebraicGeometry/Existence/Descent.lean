module

public import StacksFrontier.AlgebraicGeometry.LimitSmallDominantIndex.Descent

/-!
# Factoring a morphism out of an affine dominant cofiltered limit, at a free index universe

Mathlib's `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` — the
surjective half of (1) ⇒ (3) of Stacks 01ZC — is stated for an index category at the scheme
universe, and
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall`
(`StacksFrontier/AlgebraicGeometry/LimitUniverse/AffineTransitionLimit.lean`) frees the coupling
only at the cost of `CategoryTheory.InitiallySmall.{u}` on the index.

`StacksFrontier/AlgebraicGeometry/LimitSmallDominantIndex/Descent.lean` does for the *injective*
half what this file does for the surjective one: replace that smallness hypothesis by hypotheses
on the system — affineness over a fixed base and quasi-compact scheme-theoretically dominant
limit projections — under which `AlgebraicGeometry.exists_small_limit_of_affine_of_dominant`
produces a `u`-small subsystem with the same limit, so that Mathlib's statement applies to the
subsystem and transports back verbatim.

## Main results

* `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant_over`,
  for a system of schemes in an overcategory.
* `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant'`,
  the same for a system of plain schemes with a natural family of affine morphisms to a fixed
  base. The unprimed name belongs to the variant in
  `StacksFrontier/AlgebraicGeometry/Limits/SmallDominantIndex.lean`, which asks instead that the
  transition morphisms be affine.
* `AlgebraicGeometry.Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant`: precomposing with a
  scheme-theoretically dominant morphism does not change the kernel ideal sheaf.
* `AlgebraicGeometry.IsClosedImmersion.liftOfDominant`: a morphism factors through a closed
  subscheme of its target as soon as its restriction along a scheme-theoretically dominant
  morphism does.

## Implementation notes

The base `S` over which the system is affine and the base `T` over which the target is of finite
presentation are kept distinct: in the application to Stacks 0CNR they are, respectively, the
base change of the model of the source's good diagram to the common stage and the stage of the
target's good diagram.

The hypotheses of the second form are explicit arguments rather than instance arguments, for the
reason recorded in
`AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant`: at a
consumer the system is a whiskered diagram and instance search does not reduce through
`CategoryTheory.Limits.Cone.whisker`.

No index is designated, so the seeding family of
`AlgebraicGeometry.exists_small_limit_of_affine_of_dominant` is discarded: unlike the injective
half, which must produce a transition out of two *given* stages, this statement is free to
produce whichever stage the subsystem offers.

## References

* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC), the surjective half of
  (1) ⇒ (3).
* [Stacks Project, Tag 01R9](https://stacks.math.columbia.edu/tag/01R9), whose consequence
  `AlgebraicGeometry.IsClosedImmersion.liftOfDominant` is.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- **Stacks 01ZC, surjective half, for an affine dominant system at a free index universe.**
Let `D` be an inverse system of schemes affine over `S`, indexed by the opposite of a directed
preorder `I` at a universe independent of the scheme universe, with quasi-compact
scheme-theoretically dominant limit projections and quasi-compact quasi-separated stages, and
let `g : W ⟶ T` be locally of finite presentation. A morphism from the limit vertex to `W`
compatible with a natural family of morphisms to `T` factors through some stage.

This is Mathlib's
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` with the index
universes freed and *no* smallness hypothesis on the index. -/
public theorem Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant_over
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffineHom (D.obj i).hom] [IsAffineHom c.pt.hom]
    [∀ i, QuasiCompact (c.π.app i).left]
    [∀ i, IsSchemeTheoreticallyDominant (c.π.app i).left]
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    {T W : Scheme.{u}} (τ : D ⋙ Over.forget S ⟶ (Functor.const Iᵒᵖ).obj T)
    (g : W ⟶ T) [LocallyOfFinitePresentation g]
    (a : c.pt.left ⟶ W) (ha : ∀ x, (c.π.app x).left ≫ τ.app x = a ≫ g) :
    ∃ (i : I) (h : (D.obj (op i)).left ⟶ W),
      (c.π.app (op i)).left ≫ h = a ∧ h ≫ g = τ.app (op i) := by
  classical
  obtain ⟨J, hJ, hne, hd, e, _, -, ⟨hlim⟩⟩ :=
    exists_small_limit_of_affine_of_dominant (α := PUnit.{u + 1})
      (fun _ => Classical.arbitrary I) D c hc
  let := hJ
  let := hne
  let := hd
  let E := e.monotone.functor.op
  let A : Jᵒᵖ ⥤ Scheme.{u} := (E ⋙ D) ⋙ Over.forget S
  let c' : Cone A := (Over.forget S).mapCone (c.whisker E)
  have hc' : IsLimit c' := isLimitOfPreserves (Over.forget S) hlim
  have hAff : ∀ {x y : Jᵒᵖ} (b : x ⟶ y), IsAffineHom (A.map b) := by
    intro x y b
    change IsAffineHom ((D.map (E.map b)).left)
    have : IsAffineHom ((D.map (E.map b)).left ≫ (D.obj (E.obj y)).hom) := by
      rw [(D.map (E.map b)).w]
      infer_instance
    exact IsAffineHom.of_comp _ (D.obj (E.obj y)).hom
  have hCpt : ∀ x : Jᵒᵖ, CompactSpace (A.obj x) := fun x =>
    inferInstanceAs (CompactSpace (D.obj (E.obj x)).left)
  have hQS : ∀ x : Jᵒᵖ, QuasiSeparatedSpace (A.obj x) := fun x =>
    inferInstanceAs (QuasiSeparatedSpace (D.obj (E.obj x)).left)
  let τ' : A ⟶ (Functor.const Jᵒᵖ).obj T :=
    { app x := τ.app (E.obj x)
      naturality := fun x y b => τ.naturality (E.map b) }
  obtain ⟨m, h, hm₁, hm₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    A τ' g c' hc' a (by ext x; exact ha (E.obj x))
  exact ⟨e (unop m), h, hm₁, hm₂⟩

attribute [local instance] IsCofiltered.isConnected in
/-- **Stacks 01ZC, surjective half, for an affine dominant system at a free index universe.**
The same statement as
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant_over`
for a system of plain schemes together with a natural family `ρ` of affine morphisms to a fixed
base `S`, compatible with an affine morphism `ρc` out of the limit vertex.

The prime distinguishes this from
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant` in
`StacksFrontier/AlgebraicGeometry/Limits/SmallDominantIndex.lean`, which reaches the same
conclusion from affineness of the *transition* morphisms, supplied by instance search, and
indexes the stage it produces by `Iᵒᵖ` rather than by `I`. Neither form subsumes the other at a
consumer: here the system arrives as a whiskered diagram, through which instance search does
not reduce, which is why every hypothesis below is an explicit argument. -/
public theorem Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant'
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (ρ : D ⟶ (Functor.const Iᵒᵖ).obj S) (ρc : c.pt ⟶ S)
    (hρc : ∀ x, c.π.app x ≫ ρ.app x = ρc)
    (hAff : ∀ x, IsAffineHom (ρ.app x)) (hAffc : IsAffineHom ρc)
    (hqc : ∀ x, QuasiCompact (c.π.app x))
    (hdom : ∀ x, IsSchemeTheoreticallyDominant (c.π.app x))
    (hcpt : ∀ x, CompactSpace (D.obj x))
    (hqs : ∀ x, QuasiSeparatedSpace (D.obj x))
    {T W : Scheme.{u}} (τ : D ⟶ (Functor.const Iᵒᵖ).obj T)
    (g : W ⟶ T) (hg : LocallyOfFinitePresentation g)
    (a : c.pt ⟶ W) (ha : ∀ x, c.π.app x ≫ τ.app x = a ≫ g) :
    ∃ (i : I) (h : D.obj (op i) ⟶ W),
      c.π.app (op i) ≫ h = a ∧ h ≫ g = τ.app (op i) := by
  classical
  let := hg
  let D' : Iᵒᵖ ⥤ Over S :=
    { obj x := Over.mk (ρ.app x)
      map {x y} a := Over.homMk (D.map a) (by simp)
      map_id x := Over.OverMorphism.ext (by simp)
      map_comp a b := Over.OverMorphism.ext (by simp) }
  let c' : Cone D' :=
    { pt := Over.mk ρc
      π :=
        { app x := Over.homMk (c.π.app x) (hρc x)
          naturality := fun x y a => Over.OverMorphism.ext (c.w a).symm } }
  have hc' : IsLimit c' := isLimitOfReflects (Over.forget S) hc
  have h₁ : ∀ x, IsAffineHom (D'.obj x).hom := hAff
  have h₂ : IsAffineHom c'.pt.hom := hAffc
  have h₃ : ∀ x, QuasiCompact (c'.π.app x).left := hqc
  have h₄ : ∀ x, IsSchemeTheoreticallyDominant (c'.π.app x).left := hdom
  have h₅ : ∀ x, CompactSpace (D'.obj x).left := hcpt
  have h₆ : ∀ x, QuasiSeparatedSpace (D'.obj x).left := hqs
  let τ' : D' ⋙ Over.forget S ⟶ (Functor.const Iᵒᵖ).obj T :=
    { app x := τ.app x
      naturality := fun x y a => τ.naturality a }
  exact Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant_over D' c' hc' τ' g
    a ha

/-! ### Factoring through a closed subscheme across a dominant morphism -/

/-- Precomposition with a scheme-theoretically dominant morphism does not change the kernel
ideal sheaf. -/
public lemma Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant {A B C : Scheme.{u}}
    (p : A ⟶ B) (u : B ⟶ C) [IsSchemeTheoreticallyDominant p] :
    (p ≫ u).ker = u.ker := by
  rw [Scheme.Hom.ker_comp, p.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- **Factoring across a dominant morphism.** Let `p : A ⟶ B` be scheme-theoretically dominant,
`u : B ⟶ C` arbitrary and `i : Z ⟶ C` a closed immersion. If `p ≫ u` factors through `i`, then
so does `u`. -/
public noncomputable def IsClosedImmersion.liftOfDominant {A B C Z : Scheme.{u}}
    (i : Z ⟶ C) [IsClosedImmersion i] (u : B ⟶ C) (p : A ⟶ B)
    [IsSchemeTheoreticallyDominant p] (w : A ⟶ Z) (hw : p ≫ u = w ≫ i) :
    B ⟶ Z :=
  IsClosedImmersion.lift i u (by
    have h : i.ker ≤ (w ≫ i).ker := w.le_ker_comp i
    rw [← hw, Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant] at h
    exact h)

/-- The factorization `IsClosedImmersion.liftOfDominant i u p w hw` composed with `i` is `u`. -/
@[reassoc (attr := simp)]
public lemma IsClosedImmersion.liftOfDominant_fac {A B C Z : Scheme.{u}}
    (i : Z ⟶ C) [IsClosedImmersion i] (u : B ⟶ C) (p : A ⟶ B)
    [IsSchemeTheoreticallyDominant p] (w : A ⟶ Z) (hw : p ≫ u = w ≫ i) :
    IsClosedImmersion.liftOfDominant i u p w hw ≫ i = u :=
  IsClosedImmersion.lift_fac _ _ _

end AlgebraicGeometry

end
