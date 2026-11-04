module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineProductClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Separation of an algebraic space from its affine intersections

An algebraic space `X` over a scheme `S` is separated — that is, its absolute diagonal is a
closed immersion — exactly when for every pair of objects `U`, `V` of the big fppf site with
affine underlying scheme and every pair of morphisms `h_U ⟶ X`, `h_V ⟶ X`, the fibre product
`U ×_X V` has affine underlying scheme and the canonical map

```
Γ(U, ⊤) ⊗_ℤ Γ(V, ⊤) ⟶ Γ(U ×_X V, ⊤)
```

is surjective. This is Stacks 0AHS. It is quasi-separated — that is, its absolute diagonal is
quasi-compact — exactly when `U ×_X V` is quasi-compact for every such pair, and equivalently
for every pair with `U`, `V` merely quasi-compact. This is Stacks 0AHR.

## Main definitions

* `AlgebraicGeometry.Space.HasAffineIntersections` is the right-hand side of the criterion of
  Stacks 0AHS: the affineness and surjectivity condition on every representing object of a
  fibre product of two affine objects over `X`.
* `AlgebraicGeometry.Space.HasQuasiCompactIntersections` is the right-hand side of the
  criterion of Stacks 0AHR, with the condition imposed on the two factors left as a parameter
  so that both conditions (2) and (3) of that statement are instances of it.

## Main results

* `AlgebraicGeometry.Space.preservesBinaryProducts_toScheme_terminal`: the functor to schemes
  from the big fppf site over the terminal scheme preserves binary products.
* `AlgebraicGeometry.Space.isClosedImmersion_toScheme_map_prodLift_iff`: over the terminal
  scheme, the morphism of schemes underlying a morphism into a product of two objects with
  affine underlying scheme is a closed immersion exactly when the source is affine and the
  induced map on global sections is surjective.
* `AlgebraicGeometry.Space.quasiCompact_toScheme_map_prodLift_iff`: over the terminal scheme,
  the morphism of schemes underlying a morphism into a product of two objects with affine
  underlying scheme is quasi-compact exactly when its source is quasi-compact.
* `AlgebraicGeometry.Space.isAbsolutelySeparated_iff_hasAffineIntersections`: Stacks 0AHS.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_tfae`: Stacks 0AHR.

## Implementation notes

The condition is phrased by quantifying over *every* cartesian square of Yoneda presheaves
exhibiting the fibre product, rather than over a chosen one, so that it does not depend on a
choice of representing object; affineness of the underlying scheme and surjectivity of the map
on global sections are invariant under isomorphism, so the two readings agree.

Both directions pass to the absolute situation, over the terminal scheme `Spec ℤ`, along the
presheaf-level relocalization functor: it preserves fibre products, carries representable
presheaves to representable presheaves, and presents every morphism from a representable
presheaf into a relocalized presheaf as the relocalization of such a morphism. Over the
terminal scheme the functor to schemes preserves binary products, because a product in the
slice category is a fibre product over the base and the base is the terminal scheme; that is
what turns the product of two objects of the site into the absolute product
`U ×_{Spec ℤ} V` of the Stacks statement.

The sufficiency direction tests the diagonal only on objects of the site with affine underlying
scheme, which is enough because being a closed immersion is Zariski local at the target:
this is
`AlgebraicGeometry.Space.presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`. For an
affine test object the two morphisms into the relocalized presheaf come from two morphisms
over `S` whose sources have the *same* underlying scheme as the test object, so both are
affine and the criterion applies to them.

Stacks 0AHR runs the same two arguments with quasi-compactness of a morphism of schemes in
place of being a closed immersion. The only scheme-level inputs change: the product of two
objects of the site over the terminal scheme is the absolute product of their underlying
schemes, so it is affine when both are and quasi-compact when both are, and a morphism of
schemes into a quasi-compact scheme has quasi-compact source while a morphism out of a
quasi-compact scheme into an *affine* one is quasi-compact — the latter being
`AlgebraicGeometry.quasiCompact_of_compactSpace_of_isAffine`. The sufficiency direction uses
`AlgebraicGeometry.Space.presheaf_of_affineBaseChange` rather than
`AlgebraicGeometry.Space.presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`, because the
representing object of a fibre product of two affine objects over `X` is quasi-compact but
need not be affine.

Conditions (2) and (3) of Stacks 0AHR differ only in the condition imposed on the two factors,
so `AlgebraicGeometry.Space.HasQuasiCompactIntersections` takes that condition as a parameter;
(1) implies both at once, and (2) follows from (3) because an affine scheme is quasi-compact.

## References

* [Stacks Project, Tag 0AHR](https://stacks.math.columbia.edu/tag/0AHR)
* [Stacks Project, Tag 0AHS](https://stacks.math.columbia.edu/tag/0AHS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek

universe v w u

namespace AlgebraicGeometry.Space

/-! ### Two general facts about diagonals and relocalization -/

/-- **The relocalization of a cartesian square whose two middle corners are representable.**
If `h_P ⟶ h_A ⟶ X ⟵ h_{A'} ⟵ h_P` is cartesian, then applying the relocalization functor along
`f : V ⟶ U` and identifying the relocalizations of the three representable presheaves with the
presheaves represented by their images under `Over.map f` gives a cartesian square again.

This is `CategoryTheory.OverShriek.isPullback_relocalize_atlas` for a pair of morphisms with
possibly distinct sources. -/
private theorem isPullback_map_relocalize_yoneda {C : Type w} [Category.{v} C] {U V : C}
    (f : V ⟶ U) {X : (Over V)ᵒᵖ ⥤ Type v} {P A A' : Over V} {p : P ⟶ A} {q : P ⟶ A'}
    {a : yoneda.obj A ⟶ X} {b : yoneda.obj A' ⟶ X}
    (h : IsPullback (yoneda.map p) (yoneda.map q) a b) :
    IsPullback (yoneda.map ((Over.map f).map p)) (yoneda.map ((Over.map f).map q))
      (((relocalizeYonedaIso f).app A).inv ≫ (relocalizePresheafFunctor f).map a)
      (((relocalizeYonedaIso f).app A').inv ≫ (relocalizePresheafFunctor f).map b) :=
  (h.map (relocalizePresheafFunctor f)).of_iso ((relocalizeYonedaIso f).app P)
    ((relocalizeYonedaIso f).app A) ((relocalizeYonedaIso f).app A') (Iso.refl _)
    ((relocalizeYonedaIso f).hom.naturality p) ((relocalizeYonedaIso f).hom.naturality q)
    (by simp) (by simp)

/-- **A cartesian square of two morphisms out of representable presheaves is a base change of
the absolute diagonal.** If `h_P ⟶ h_A ⟶ F ⟵ h_{A'} ⟵ h_P` is cartesian, then `h_P` is the
base change of the diagonal `F ⟶ F ⨯ F` along the morphism `h_{A ⨯ A'} ⟶ F ⨯ F` assembled from
the two given ones, and the second projection of that base change is the Yoneda image of
`prod.lift p q : P ⟶ A ⨯ A'`.

This is `Stacks.Spaces.isPullback_diag_prodMap` with the presheaf product of the two
representables replaced by the presheaf represented by the product, along the comparison
isomorphism of `CategoryTheory.Limits.PreservesLimitPair.iso`. -/
private theorem isPullback_diag_yoneda_prodLift {C : Type w} [Category.{v} C]
    [HasBinaryProducts C] {F : Cᵒᵖ ⥤ Type v} {A A' P : C}
    {a : yoneda.obj A ⟶ F} {b : yoneda.obj A' ⟶ F} {p : P ⟶ A} {q : P ⟶ A'}
    (h : IsPullback (yoneda.map p) (yoneda.map q) a b) :
    IsPullback (yoneda.map p ≫ a) (yoneda.map (prod.lift p q)) (diag F)
      (prodComparison yoneda A A' ≫ prod.map a b) := by
  have he : yoneda.map (prod.lift p q) ≫ prodComparison yoneda A A' =
      prod.lift (yoneda.map p) (yoneda.map q) := by
    refine prod.hom_ext ?_ ?_ <;> simp [← Functor.map_comp]
  refine (Stacks.Spaces.isPullback_diag_prodMap h).of_iso (Iso.refl _) (Iso.refl _)
    (PreservesLimitPair.iso yoneda A A').symm (Iso.refl _) (by simp) ?_ (by simp) ?_
  · rw [Iso.symm_hom, Iso.refl_hom, Category.id_comp, ← he, Category.assoc,
      ← PreservesLimitPair.iso_hom, Iso.hom_inv_id, Category.comp_id]
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, ← Category.assoc,
      ← PreservesLimitPair.iso_hom, Iso.inv_hom_id, Category.id_comp]

/-- **Base change of the diagonal along a morphism out of a representable presheaf.** If the two
components of `g : h_A ⟶ F ⨯ F` have fibre product `h_W` with projections `p`, `q`, then the base
change of the diagonal of `F` along `g` is the pullback of `prod.lift p q` along the diagonal
of `A`, under the Yoneda embedding. -/
private theorem isPullback_diag_yoneda_pullback_prodLift {C : Type w} [Category.{v} C]
    [HasBinaryProducts C] [HasPullbacks C] {F : Cᵒᵖ ⥤ Type v} {A W : C}
    (g : yoneda.obj A ⟶ F ⨯ F) {p q : W ⟶ A}
    (hpb : IsPullback (yoneda.map p) (yoneda.map q) (g ≫ prod.fst) (g ≫ prod.snd)) :
    IsPullback (yoneda.map (pullback.fst (prod.lift p q) (diag A)) ≫
        yoneda.map p ≫ g ≫ prod.fst)
      (yoneda.map (pullback.snd (prod.lift p q) (diag A))) (diag F) g := by
  have hd : yoneda.map (diag A) ≫ prodComparison yoneda A A = diag (yoneda.obj A) := by
    refine prod.hom_ext ?_ ?_ <;> rw [Category.assoc] <;> simp [← Functor.map_comp]
  have hg : g = yoneda.map (diag A) ≫ prodComparison yoneda A A ≫
      prod.map (g ≫ prod.fst) (g ≫ prod.snd) := by
    rw [← Category.assoc, hd]
    exact prod.hom_ext (by simp) (by simp)
  have hpaste := ((IsPullback.of_hasPullback (prod.lift p q) (diag A)).map yoneda).paste_horiz
    (isPullback_diag_yoneda_prodLift hpb)
  rwa [← hg] at hpaste

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### Products over the terminal scheme -/

/-- **The functor to schemes from the big fppf site over the terminal scheme preserves binary
products.** A product in the slice category is a fibre product over the base, the functor
preserves fibre products, and it carries the terminal object of the slice to the terminal
scheme. -/
theorem preservesBinaryProducts_toScheme_terminal :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ) :=
  have _ : PreservesLimit (Functor.empty.{0} (BigFppfOver B (⊤_ Scheme.{u}) hZ))
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ) :=
    preservesTerminal_of_iso _ (toSchemeTerminalIso B (⊤_ Scheme.{u}) hZ)
  have _ : PreservesLimitsOfShape (Discrete.{0} PEmpty)
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  preservesBinaryProducts_of_preservesTerminal_and_pullbacks _

/-- **The criterion for a morphism into a product of two affine objects of the site over the
terminal scheme to be a closed immersion of schemes.** The underlying morphism of schemes of
`prod.lift p q : W ⟶ U ⨯ V` is the morphism `W ⟶ U ×_{Spec ℤ} V` determined by the underlying
morphisms of `p` and `q`, so `AlgebraicGeometry.isClosedImmersion_pullbackLift_terminal_iff`
applies to it. -/
theorem isClosedImmersion_toScheme_map_prodLift_iff
    {W U V : BigFppfOver B (⊤_ Scheme.{u}) hZ} (p : W ⟶ U) (q : W ⟶ V)
    [IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj U)]
    [IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)] :
    _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (prod.lift p q)) ↔
      IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W) ∧
        Function.Surjective (globalSectionsTensorLift
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map p)
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map q)) := by
  have _ := preservesBinaryProducts_toScheme_terminal B hZ
  set T := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ
  set eAbs : T.obj (U ⨯ V) ≅ pullback (terminal.from (T.obj U)) (terminal.from (T.obj V)) :=
    PreservesLimitPair.iso T U V ≪≫ prodIsoPullback (T.obj U) (T.obj V) with heAbs
  have hfst : eAbs.hom ≫ pullback.fst (terminal.from (T.obj U)) (terminal.from (T.obj V)) =
      T.map (prod.fst : U ⨯ V ⟶ U) := by
    rw [heAbs, Iso.trans_hom, Category.assoc, prodIsoPullback_hom_fst,
      PreservesLimitPair.iso_hom, prodComparison_fst]
  have hsnd : eAbs.hom ≫ pullback.snd (terminal.from (T.obj U)) (terminal.from (T.obj V)) =
      T.map (prod.snd : U ⨯ V ⟶ V) := by
    rw [heAbs, Iso.trans_hom, Category.assoc, prodIsoPullback_hom_snd,
      PreservesLimitPair.iso_hom, prodComparison_snd]
  have hmap : T.map (prod.lift p q) ≫ eAbs.hom =
      pullback.lift (T.map p) (T.map q) (terminal.hom_ext _ _) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, ← T.map_comp, prod.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, hsnd, ← T.map_comp, prod.lift_snd, pullback.lift_snd]
  have earrow : Arrow.mk (T.map (prod.lift p q)) ≅
      Arrow.mk (pullback.lift (T.map p) (T.map q) (terminal.hom_ext _ _)) :=
    Arrow.isoMk (Iso.refl (T.obj W)) eAbs
      (by simp only [Arrow.mk_hom, Iso.refl_hom]; exact hmap.symm)
  rw [MorphismProperty.arrow_mk_iso_iff
    (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}) earrow]
  exact isClosedImmersion_pullbackLift_terminal_iff (T.map p) (T.map q)


/-! ### The affine-intersection condition -/

/-- **The affine-intersection condition of Stacks 0AHS.** For every pair of objects `U`, `V` of
the big fppf site of `S` with affine underlying scheme and every pair of morphisms
`h_U ⟶ X`, `h_V ⟶ X`, every object of the site representing the fibre product `U ×_X V` has
affine underlying scheme, and the canonical map `Γ(U, ⊤) ⊗_ℤ Γ(V, ⊤) ⟶ Γ(U ×_X V, ⊤)` of
`AlgebraicGeometry.globalSectionsTensorLift` is surjective. -/
abbrev HasAffineIntersections (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (U V P : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ X)
    (p : P ⟶ U) (q : P ⟶ V),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
    IsPullback (yoneda.map p) (yoneda.map q) a b →
    IsAffine ((BigFppfOver.toScheme B S hS).obj P) ∧
      Function.Surjective (globalSectionsTensorLift ((BigFppfOver.toScheme B S hS).map p)
        ((BigFppfOver.toScheme B S hS).map q))

/-- **A pair of morphisms from an affine object into the relocalized presheaf comes from a
fibre product over `S`.** The two morphisms `a`, `b` are relocalizations of morphisms
`σ : h_U ⟶ X`, `τ : h_V ⟶ X` over `S`, whose sources are affine because they have the same
underlying scheme as `A`. The fibre product `P` of `σ` and `τ` exists since the diagonal of `X`
is representable, and its relocalization is a fibre product of `a` and `b` with the same
underlying morphisms of schemes. -/
private theorem exists_isPullback_of_relocalize_isAffine
    (γ : B.obj hS ⟶ B.obj hZ) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (A : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A))
    (a b : yoneda.obj A ⟶ (relocalizePresheafFunctor γ).obj X) :
    ∃ (U V P : BigFppfOver B S hS) (σ : yoneda.obj U ⟶ X) (τ : yoneda.obj V ⟶ X)
      (p : P ⟶ U) (q : P ⟶ V) (p' q' : (Over.map γ).obj P ⟶ A),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsPullback (yoneda.map p) (yoneda.map q) σ τ ∧
      IsPullback (yoneda.map p') (yoneda.map q') a b ∧
      (Function.Surjective (globalSectionsTensorLift ((BigFppfOver.toScheme B S hS).map p)
          ((BigFppfOver.toScheme B S hS).map q)) →
        Function.Surjective (globalSectionsTensorLift
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map p')
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map q'))) := by
  obtain ⟨ψ, hψ, σ, hσ⟩ := exists_eq_relocalizeYonedaFactorIso_comp γ a
  obtain ⟨χ, hχ, τ, hτ⟩ := exists_eq_relocalizeYonedaFactorIso_comp γ b
  have hrep : yoneda.relativelyRepresentable σ :=
    Functor.relativelyRepresentable.of_diag hX.diagonal_representable σ
  have hpb : IsPullback (yoneda.map (hrep.fst' τ)) (yoneda.map (hrep.snd τ)) σ τ :=
    hrep.isPullback' τ
  have ha : a = yoneda.map (relocalizeFactorIso γ hψ).hom ≫
      (((relocalizeYonedaIso γ).app (Over.mk ψ)).inv ≫ (relocalizePresheafFunctor γ).map σ) := by
    rw [hσ]; simp [relocalizeYonedaFactorIso]
  have hb : b = yoneda.map (relocalizeFactorIso γ hχ).hom ≫
      (((relocalizeYonedaIso γ).app (Over.mk χ)).inv ≫ (relocalizePresheafFunctor γ).map τ) := by
    rw [hτ]; simp [relocalizeYonedaFactorIso]
  refine ⟨Over.mk ψ, Over.mk χ, hrep.pullback τ, σ, τ, hrep.fst' τ, hrep.snd τ,
    (Over.map γ).map (hrep.fst' τ) ≫ (relocalizeFactorIso γ hψ).inv,
    (Over.map γ).map (hrep.snd τ) ≫ (relocalizeFactorIso γ hχ).inv, hA, hA, hpb, ?_, ?_⟩
  · refine (isPullback_map_relocalize_yoneda γ hpb).of_iso (Iso.refl _)
      (yoneda.mapIso (relocalizeFactorIso γ hψ)).symm
      (yoneda.mapIso (relocalizeFactorIso γ hχ)).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [← Functor.map_comp]
    · simp [← Functor.map_comp]
    · simp [ha]
    · simp [hb]
  · have hp : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
        ((Over.map γ).map (hrep.fst' τ) ≫ (relocalizeFactorIso γ hψ).inv) =
        (BigFppfOver.toScheme B S hS).map (hrep.fst' τ) := by
      simp [relocalizeFactorIso]
    have hq : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
        ((Over.map γ).map (hrep.snd τ) ≫ (relocalizeFactorIso γ hχ).inv) =
        (BigFppfOver.toScheme B S hS).map (hrep.snd τ) := by
      simp [relocalizeFactorIso]
    intro h
    rwa [hp, hq]

/-- **A pair of morphisms from an affine object into the relocalized presheaf has an affine
intersection, closed in the product.** Let `A` be an object of the big fppf site over the
terminal scheme with affine underlying scheme and let `a`, `b` be two morphisms from `h_A` into
the relocalization of `X` along `γ`. Then the fibre product of `a` and `b` is represented by an
object `W` of the site, and the morphism `W ⟶ A ⨯ A` assembled from the two projections is a
closed immersion on underlying schemes.

Both `a` and `b` are relocalizations of morphisms `h_U ⟶ X`, `h_V ⟶ X` over `S` whose sources
have the same underlying scheme as `A`, hence are affine; the affine-intersection condition
therefore applies to them, and
`AlgebraicGeometry.Space.isClosedImmersion_toScheme_map_prodLift_iff` converts its conclusion
into the closed immersion. -/
private theorem exists_closedImmersion_prodLift_of_isAffine
    (γ : B.obj hS ⟶ B.obj hZ) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXaff : HasAffineIntersections B S hS X)
    (A : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A))
    (a b : yoneda.obj A ⟶ (relocalizePresheafFunctor γ).obj X) :
    ∃ (W : BigFppfOver B (⊤_ Scheme.{u}) hZ) (p q : W ⟶ A),
      IsPullback (yoneda.map p) (yoneda.map q) a b ∧
        _root_.AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (prod.lift p q)) := by
  obtain ⟨U, V, P, σ, τ, p, q, p', q', hU, hV, hpb, hpb', hsurj'⟩ :=
    exists_isPullback_of_relocalize_isAffine B S hS hZ γ hX A hA a b
  obtain ⟨hPaff, hsurj⟩ := hXaff U V P σ τ p q hU hV hpb
  have _ := hA
  refine ⟨_, p', q', hpb', ?_⟩
  rw [isClosedImmersion_toScheme_map_prodLift_iff]
  exact ⟨hPaff, hsurj' hsurj⟩

/-- **The affine-intersection condition gives the diagonal on affine base changes.** For an
object `A` of the big fppf site over the terminal scheme with affine underlying scheme and a
morphism `g : h_A ⟶ F ⨯ F` into the square of the relocalized presheaf `F`, the base change of
the diagonal of `F` along `g` is represented by an object of the site with affine underlying
scheme whose projection to `A` is a closed immersion.

The two components of `g` have an affine intersection `W`, closed in `A ⨯ A`, by
`AlgebraicGeometry.Space.exists_closedImmersion_prodLift_of_isAffine`; the base change in
question is the further base change of `W ⟶ A ⨯ A` along the diagonal of `A`. -/
private theorem holdsOnAffineBaseChange_diag_relocalize
    (γ : B.obj hS ⟶ B.obj hZ) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXaff : HasAffineIntersections B S hS X) :
    HoldsOnAffineBaseChange B (⊤_ Scheme.{u}) hZ
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (diag ((relocalizePresheafFunctor γ).obj X)) := by
  intro A hA g
  obtain ⟨W, p, q, hpb, hclosed⟩ := exists_closedImmersion_prodLift_of_isAffine B S hS hZ γ hX
    hXaff A hA (g ≫ prod.fst) (g ≫ prod.snd)
  have hsnd : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
        (pullback.snd (prod.lift p q) (diag A))) :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback (prod.lift p q) (diag A)).map
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)) hclosed
  have _ : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A) := hA
  exact ⟨pullback (prod.lift p q) (diag A), pullback.snd (prod.lift p q) (diag A), _,
    isPullback_diag_yoneda_pullback_prodLift g hpb,
    (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
        (pullback.snd (prod.lift p q) (diag A)))).1, hsnd⟩

/-! ### Stacks 0AHS -/

/-- **Stacks 0AHS.** An algebraic space over `S` is separated if and only if for every pair of
objects of the big fppf site with affine underlying scheme mapping to it the fibre product has
affine underlying scheme and the canonical map from the tensor product over `ℤ` of the two
rings of global sections to the ring of global sections of the fibre product is surjective.

Necessity: the morphism from the fibre product to the product `U ×_{Spec ℤ} V` is a base change
of the absolute diagonal, hence a closed immersion; and a closed immersion into a product of
two affine schemes is exactly an affine source together with a surjective map on global
sections.

Sufficiency: being a closed immersion is Zariski local at the target, so the diagonal need only
be tested on objects of the site with affine underlying scheme, and over such an object the
criterion applies to the two morphisms the test factors through. -/
@[stacks 0AHS]
theorem isAbsolutelySeparated_iff_hasAffineIntersections
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    IsAbsolutelySeparated B S hS hZ X ↔ HasAffineIntersections B S hS X := by
  set γ : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  refine ⟨fun hsep U V P a b p q hU hV hpb ↦ ?_, fun hXaff ↦ ?_⟩
  · have _ : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((Over.map γ).obj U)) := hU
    have _ : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((Over.map γ).obj V)) := hV
    have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
          (prod.lift ((Over.map γ).map p) ((Over.map γ).map q))) :=
      hsep.property _ _ _
        (isPullback_diag_yoneda_prodLift (isPullback_map_relocalize_yoneda γ hpb))
    rwa [isClosedImmersion_toScheme_map_prodLift_iff] at hclosed
  · have hF := isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ) γ X hX
    exact presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B (⊤_ Scheme.{u}) hZ
      _root_.AlgebraicGeometry.IsClosedImmersion.isZariskiLocalAtTarget hF
      (isAlgebraicSpace_prod B (⊤_ Scheme.{u}) hZ hF hF)
      (holdsOnAffineBaseChange_diag_relocalize B S hS hZ γ hX hXaff)

/-! ### Quasi-compact intersections -/

/-- **The underlying scheme of a product of two objects of the big fppf site over the terminal
scheme is the absolute product of the two underlying schemes.** The functor to schemes
preserves binary products there, and a binary product of schemes is the fibre product over the
terminal scheme. -/
private noncomputable def toSchemeProdIsoPullbackTerminal
    (U V : BigFppfOver B (⊤_ Scheme.{u}) hZ) :
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (U ⨯ V) ≅
      pullback (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj U))
        (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)) :=
  have _ := preservesBinaryProducts_toScheme_terminal B hZ
  PreservesLimitPair.iso (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ) U V ≪≫
    prodIsoPullback _ _

/-- **A product of two objects of the big fppf site over the terminal scheme whose underlying
schemes are affine has affine underlying scheme.** It is the fibre product of two affine
schemes over the affine terminal scheme. -/
theorem isAffine_toScheme_obj_prod {U V : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (hU : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)) :
    IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (U ⨯ V)) :=
  have _ := hU
  have _ := hV
  _root_.AlgebraicGeometry.IsAffine.of_isIso (toSchemeProdIsoPullbackTerminal B hZ U V).hom

/-- **A product of two objects of the big fppf site over the terminal scheme whose underlying
schemes are quasi-compact has quasi-compact underlying scheme.** The structure morphism of a
quasi-compact scheme to the affine terminal scheme is quasi-compact, so its base change along
the structure morphism of the second factor is quasi-compact as well, and a morphism of schemes
with quasi-compact target has quasi-compact source. -/
theorem compactSpace_toScheme_obj_prod {U V : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (hU : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj U))
    (hV : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)) :
    CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (U ⨯ V)) := by
  set T := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ
  have _ := hU
  have _ := hV
  have hqc : QuasiCompact (pullback.snd (terminal.from (T.obj U)) (terminal.from (T.obj V))) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _)
      (_root_.AlgebraicGeometry.quasiCompact_of_compactSpace_of_isAffine
        (terminal.from (T.obj U)) inferInstance hU)
  have _ : CompactSpace
      ((pullback (terminal.from (T.obj U)) (terminal.from (T.obj V)) : Scheme.{u}) : Type u) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd (terminal.from (T.obj U)) (terminal.from (T.obj V)))
  exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
    (toSchemeProdIsoPullbackTerminal B hZ U V))).symm.compactSpace

/-- **A morphism into a product of two quasi-compact objects of the site over the terminal
scheme has quasi-compact source as soon as it is quasi-compact.** The product has quasi-compact
underlying scheme by `AlgebraicGeometry.Space.compactSpace_toScheme_obj_prod`. -/
theorem compactSpace_of_quasiCompact_toScheme_map_prodLift
    {W U V : BigFppfOver B (⊤_ Scheme.{u}) hZ} (p : W ⟶ U) (q : W ⟶ V)
    (hU : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj U))
    (hV : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V))
    (h : QuasiCompact ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (prod.lift p q))) :
    CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W) :=
  have _ := compactSpace_toScheme_obj_prod B hZ hU hV
  have _ := h
  QuasiCompact.compactSpace_of_compactSpace
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (prod.lift p q))

/-- **The criterion for a morphism into a product of two affine objects of the site over the
terminal scheme to be quasi-compact.** The product has affine underlying scheme, so the
morphism is quasi-compact exactly when its source is quasi-compact. -/
theorem quasiCompact_toScheme_map_prodLift_iff
    {W U V : BigFppfOver B (⊤_ Scheme.{u}) hZ} (p : W ⟶ U) (q : W ⟶ V)
    (hU : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)) :
    QuasiCompact ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (prod.lift p q)) ↔
      CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W) :=
  have haff := isAffine_toScheme_obj_prod B hZ hU hV
  have _ := hU
  have _ := hV
  ⟨compactSpace_of_quasiCompact_toScheme_map_prodLift B hZ p q
      (Scheme.compactSpace_of_isAffine _) (Scheme.compactSpace_of_isAffine _),
    fun h ↦ _root_.AlgebraicGeometry.quasiCompact_of_compactSpace_of_isAffine _ haff h⟩

/-- **The intersection condition of Stacks 0AHR.** For every pair of objects `U`, `V` of the
big fppf site of `S` whose underlying schemes satisfy `P` and every pair of morphisms
`h_U ⟶ X`, `h_V ⟶ X`, every object of the site representing the fibre product `U ×_X V` has
quasi-compact underlying scheme.

Condition (2) of Stacks 0AHR is this with `P` quasi-compactness of the underlying scheme and
condition (3) is this with `P` affineness of it. -/
abbrev HasQuasiCompactIntersections (P : Scheme.{u} → Prop)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (U V Q : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ X)
    (p : Q ⟶ U) (q : Q ⟶ V),
    P ((BigFppfOver.toScheme B S hS).obj U) →
    P ((BigFppfOver.toScheme B S hS).obj V) →
    IsPullback (yoneda.map p) (yoneda.map q) a b →
    CompactSpace ((BigFppfOver.toScheme B S hS).obj Q)

/-- **A pair of morphisms from a quasi-compact object into the relocalized presheaf has a
quasi-compact intersection, quasi-compact over the product.** Let `A` be an object of the big
fppf site over the terminal scheme whose underlying scheme is quasi-compact and let `a`, `b` be
two morphisms from `h_A` into the relocalization of `X` along `γ`. Then the fibre product of
`a` and `b` is represented by an object `W` of the site, and the morphism `W ⟶ A ⨯ A` assembled
from the two projections is quasi-compact on underlying schemes.

Both `a` and `b` are relocalizations of morphisms `h_U ⟶ X`, `h_V ⟶ X` over `S` whose sources
have the same underlying scheme as `A`, hence are affine, so the intersection condition applies
to them; its conclusion is quasi-compactness of `W`, and `A ⨯ A` has affine underlying scheme,
so a morphism of schemes from `W` to it is quasi-compact. -/
private theorem exists_quasiCompact_prodLift_of_isAffine
    (γ : B.obj hS ⟶ B.obj hZ) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hXqc : HasQuasiCompactIntersections B S hS (fun Z : Scheme.{u} ↦ IsAffine Z) X)
    (A : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A))
    (a b : yoneda.obj A ⟶ (relocalizePresheafFunctor γ).obj X) :
    ∃ (W : BigFppfOver B (⊤_ Scheme.{u}) hZ) (p q : W ⟶ A),
      IsPullback (yoneda.map p) (yoneda.map q) a b ∧
        QuasiCompact ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (prod.lift p q)) := by
  obtain ⟨U, V, P, σ, τ, p, q, p', q', hU, hV, hpb, hpb', -⟩ :=
    exists_isPullback_of_relocalize_isAffine B S hS hZ γ hX A hA a b
  exact ⟨_, p', q', hpb', (quasiCompact_toScheme_map_prodLift_iff B hZ _ _ hA hA).2
    (hXqc U V P σ τ p q hU hV hpb)⟩

/-- **The intersection condition gives the diagonal on affine base changes.** For an object `A`
of the big fppf site over the terminal scheme with affine underlying scheme and a morphism
`g : h_A ⟶ F ⨯ F` into the square of the relocalized presheaf `F`, the base change of the
diagonal of `F` along `g` is represented by an object of the site whose projection to `A` is
quasi-compact.

The two components of `g` have a quasi-compact intersection `W`, quasi-compact over `A ⨯ A`, by
`AlgebraicGeometry.Space.exists_quasiCompact_prodLift_of_isAffine`; the base change in
question is the further base change of `W ⟶ A ⨯ A` along the diagonal of `A`. -/
private theorem affineBaseChange_diag_relocalize_quasiCompact
    (γ : B.obj hS ⟶ B.obj hZ) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hXqc : HasQuasiCompactIntersections B S hS (fun Z : Scheme.{u} ↦ IsAffine Z) X)
    (A : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A))
    (g : yoneda.obj A ⟶ (relocalizePresheafFunctor γ).obj X ⨯
      (relocalizePresheafFunctor γ).obj X) :
    ∃ (W : BigFppfOver B (⊤_ Scheme.{u}) hZ) (p : W ⟶ A)
      (m : yoneda.obj W ⟶ (relocalizePresheafFunctor γ).obj X),
      IsPullback m (yoneda.map p) (diag ((relocalizePresheafFunctor γ).obj X)) g ∧
        QuasiCompact ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map p) := by
  obtain ⟨W, p, q, hpb, hqc⟩ := exists_quasiCompact_prodLift_of_isAffine B S hS hZ γ hX
    hXqc A hA (g ≫ prod.fst) (g ≫ prod.snd)
  exact ⟨pullback (prod.lift p q) (diag A), pullback.snd (prod.lift p q) (diag A), _,
    isPullback_diag_yoneda_pullback_prodLift g hpb,
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback (prod.lift p q) (diag A)).map
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)) hqc⟩

/-! ### Stacks 0AHR -/

/-- **Stacks 0AHR.** For an algebraic space `X` over `S` the following are equivalent: `X` is a
quasi-separated algebraic space; for every pair of morphisms into `X` from objects of the big
fppf site with quasi-compact underlying scheme the fibre product has quasi-compact underlying
scheme; and the same for every pair of morphisms from objects with affine underlying scheme.

Condition (1) implies condition (2) because the fibre product maps to the product of the two
factors by a base change of the absolute diagonal, so that morphism is quasi-compact, and the
product of two quasi-compact objects over the terminal scheme is quasi-compact. Condition (2)
implies condition (3) because an affine scheme is quasi-compact. Condition (3) implies
condition (1) because quasi-compactness is Zariski local at the target, so the diagonal need
only be tested on objects of the site with affine underlying scheme, and over such an object
the criterion applies to the two morphisms the test factors through. -/
@[stacks 0AHR]
theorem isAbsolutelyQuasiSeparated_tfae (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) :
    List.TFAE
      [ IsAbsolutelyQuasiSeparated B S hS hZ X,
        HasQuasiCompactIntersections B S hS
          (fun Z : Scheme.{u} ↦ CompactSpace (Z : Type u)) X,
        HasQuasiCompactIntersections B S hS (fun Z : Scheme.{u} ↦ IsAffine Z) X ] := by
  set γ : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  tfae_have 1 → 2 := by
    intro hqs U V Q a b p q hU hV hpb
    have hU' : CompactSpace
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj ((Over.map γ).obj U) : Type u) := hU
    have hV' : CompactSpace
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj ((Over.map γ).obj V) : Type u) := hV
    exact compactSpace_of_quasiCompact_toScheme_map_prodLift B hZ ((Over.map γ).map p)
      ((Over.map γ).map q) hU' hV'
      (hqs.property _ _ _
        (isPullback_diag_yoneda_prodLift (isPullback_map_relocalize_yoneda γ hpb)))
  tfae_have 2 → 3 := by
    intro h U V Q a b p q hU hV hpb
    have _ := hU
    have _ := hV
    exact h U V Q a b p q (Scheme.compactSpace_of_isAffine _)
      (Scheme.compactSpace_of_isAffine _) hpb
  tfae_have 3 → 1 := by
    intro hXqc
    have hF := isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ) γ X hX
    exact presheaf_of_affineBaseChange B (⊤_ Scheme.{u}) hZ
      (MorphismProperty.IsLocalAtTarget.of_le
        Scheme.zariskiPrecoverage_le_fppfPrecoverage) hF
      (isAlgebraicSpace_prod B (⊤_ Scheme.{u}) hZ hF hF)
      fun A hA g ↦ affineBaseChange_diag_relocalize_quasiCompact B S hS hZ γ hX hXqc A hA g
  tfae_finish

end AlgebraicGeometry.Space

end
