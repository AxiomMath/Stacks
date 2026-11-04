module

public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteStratification
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap

/-!
# Base change of a Fitting ideal sheaf, and invariance of the Fitting stratification

The Fitting ideal sheaves of `f_* 𝒪_X`, for `f` a finite morphism, are compatible with base
change: along any affine morphism `g` the inverse image of the `k`th Fitting ideal sheaf of
`f_* 𝒪_X` is the `k`th Fitting ideal sheaf of the pushforward of the structure sheaf along the
base change of `f`.

This is what makes each member of the Fitting stratification of a groupoid scheme invariant.
The source and target maps of a groupoid scheme are two *different* base changes of the source
map, along the target and along the source respectively, and both of them are realized by the
*same* morphism out of the scheme of composable pairs: the second projection
`R ×_{s, U, t} R ⟶ R` sits in the two lower squares of the diagram of Stacks Tag 04LF, both of
which are cartesian. Hence both inverse images are the same Fitting ideal sheaf on `R`.

## Main results

* `Stacks.Morphisms.isPushout_appLE_of_isPullback`: for a cartesian square of schemes one of
  whose legs out of the base is affine, the sections over an affine open of the base, over its
  preimage, over an affine open lying above it and over the preimage of the latter in the fibre
  product form a pushout square of rings. `Stacks.Morphisms.isPushout_app_of_isPullback` is the
  case of the preimage of an affine open under an affine morphism.
* `Stacks.Fitting.comap_idealSheaf_pushforward_of_isPullback`: base change of the Fitting ideal
  sheaf of the pushforward of a structure sheaf along a finite morphism.
* `Stacks.Groupoids.finiteStratification_invariant`: every member of the Fitting stratification
  of a groupoid scheme with finite source and target is invariant.

## Implementation notes

The two affine covers of `R` relevant to the two inverse images — the preimages of the affine
opens of `U` under the source map and under the target map — have no common refinement by opens
of either shape, so the two closed subschemes cannot be compared open by open. Instead each is
compared, on its own cover, with the single ideal sheaf
`Stacks.Fitting.idealSheaf (pushforwardStructureSheaf (pullback.snd G.source G.target).left) k`,
whose ideals are available on *every* affine open of `R` because the second projection is again
finite. Two equalities against that common third object give the invariance.

The base change statement is proved on the cover of the target of `g` by the preimages of the
affine opens of the base, using `AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top`. On
such an open the inverse image of an ideal sheaf is computed by
`Stacks.IdealSheaf.ideal_comap_of_isAffineHom` and the Fitting ideal sheaf by
`Stacks.Fitting.ideal_idealSheaf_pushforward`, which reduces the statement to the
module-theoretic base change of Fitting ideals from `fittingIdeal_basic_properties`. The
identification of the sections of the fibre product as a tensor product is
`Stacks.Morphisms.isPushout_app_of_isPullback`: restricting the cartesian square to the
preimages of an affine open with `AlgebraicGeometry.Scheme.Hom.isPullback_resLE` gives a
cartesian square of affine schemes, whose global sections form a pushout of rings by
`AlgebraicGeometry.isPushout_appTop_of_isPullback`, and `CommRingCat.isPushout_iff_isPushout`
turns that pushout into the base change property `Algebra.IsPushout`.

## References

* [Stacks Project, Tag 0AB9](https://stacks.math.columbia.edu/tag/0AB9)
* [Stacks Project, Tag 04LF](https://stacks.math.columbia.edu/tag/04LF)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
* [Stacks Project, Tag 02YE](https://stacks.math.columbia.edu/tag/02YE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Morphisms

/-- The map on global sections induced by a restriction `f.resLE U W` of a morphism of schemes
is the map on sections `f.appLE U W`, conjugated by the identifications of the global sections
of an open subscheme with the sections over that open. -/
theorem appTop_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (W : X.Opens)
    (e : W ≤ f ⁻¹ᵁ U) :
    (f.resLE U W e).appTop = U.topIso.hom ≫ f.appLE U W e ≫ W.topIso.inv := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.appLE, Scheme.Opens.topIso_hom,
    Scheme.Opens.topIso_inv]

/-- The previous lemma in the shape of a commuting square, which is how it enters a transport
of a pushout square along the identifications of global sections. -/
theorem topIso_symm_hom_comp_appTop_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (W : X.Opens) (e : W ≤ f ⁻¹ᵁ U) :
    U.topIso.symm.hom ≫ (f.resLE U W e).appTop = f.appLE U W e ≫ W.topIso.symm.hom := by
  rw [Iso.symm_hom, Iso.symm_hom, appTop_resLE, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- For a cartesian square of schemes whose morphism `f` to the base is affine, an affine open
`V` of the base and an affine open `V'` of the other factor lying over it, the sections over
`V`, over `f ⁻¹ᵁ V`, over `V'` and over the preimage of `V'` in the fibre product form a pushout
square of rings. The other morphism `g` to the base need not be affine: affineness of the fibre
product over `V'` comes from that of `f ⁻¹ᵁ V` over `V`. -/
theorem isPushout_appLE_of_isPullback {P X T U : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ U}
    {g : T ⟶ U} (h : IsPullback p q f g) [IsAffineHom f] (V : U.affineOpens)
    (V' : T.affineOpens) (hV' : V'.1 ≤ g ⁻¹ᵁ V.1)
    (e : q ⁻¹ᵁ V'.1 ≤ p ⁻¹ᵁ (f ⁻¹ᵁ V.1)) :
    IsPushout (f.app V.1) (g.appLE V.1 V'.1 hV')
      (p.appLE (f ⁻¹ᵁ V.1) (q ⁻¹ᵁ V'.1) e) (q.app V'.1) := by
  have hsq := Scheme.Hom.isPullback_resLE h (US := V.1) (UT := V'.1)
    (UX := f ⁻¹ᵁ V.1) hV' le_rfl (inf_eq_right.mpr e).symm
  have h1 : IsAffine (V.1).toScheme := V.2
  have h2 : IsAffine (f ⁻¹ᵁ V.1).toScheme := V.2.preimage f
  have h3 : IsAffine (V'.1).toScheme := V'.2
  rw [← Scheme.Hom.appLE_eq_app (f := f) (U := V.1),
    ← Scheme.Hom.appLE_eq_app (f := q) (U := V'.1)]
  exact (isPushout_appTop_of_isPullback hsq).of_iso' V.1.topIso.symm (f ⁻¹ᵁ V.1).topIso.symm
    V'.1.topIso.symm (q ⁻¹ᵁ V'.1).topIso.symm (topIso_symm_hom_comp_appTop_resLE f V.1 _ le_rfl)
    (topIso_symm_hom_comp_appTop_resLE g V.1 _ hV')
    (topIso_symm_hom_comp_appTop_resLE p (f ⁻¹ᵁ V.1) _ e)
    (topIso_symm_hom_comp_appTop_resLE q V'.1 _ le_rfl)

/-- The previous lemma on the preimage of an affine open of the base under an affine
morphism `g`, which is the shape the base change of a Fitting ideal sheaf uses. -/
theorem isPushout_app_of_isPullback {P X T U : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ U}
    {g : T ⟶ U} (h : IsPullback p q f g) [IsAffineHom f] [IsAffineHom g] (V : U.affineOpens)
    (e : q ⁻¹ᵁ (g ⁻¹ᵁ V.1) ≤ p ⁻¹ᵁ (f ⁻¹ᵁ V.1)) :
    IsPushout (f.app V.1) (g.app V.1)
      (p.appLE (f ⁻¹ᵁ V.1) (q ⁻¹ᵁ (g ⁻¹ᵁ V.1)) e) (q.app (g ⁻¹ᵁ V.1)) := by
  rw [← Scheme.Hom.appLE_eq_app (f := g) (U := V.1)]
  exact isPushout_appLE_of_isPullback h V ⟨g ⁻¹ᵁ V.1, V.2.preimage g⟩ le_rfl e

end Stacks.Morphisms

namespace Stacks.Fitting

open Stacks.IdealSheaf Stacks.Morphisms

/-- **Stacks Project, Tag 07ZA** for a finite pushforward, at the level of ideal sheaves: the
inverse image along an affine morphism `g` of the `k`th Fitting ideal sheaf of `f_* 𝒪_X`, for
`f` finite, is the `k`th Fitting ideal sheaf of the pushforward of the structure sheaf along the
base change of `f` by `g`. -/
theorem comap_idealSheaf_pushforward_of_isPullback {P X T U : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ T}
    {f : X ⟶ U} {g : T ⟶ U} (h : IsPullback p q f g) [IsFinite f] [IsAffineHom g] (k : ℤ) :
    (idealSheaf (pushforwardStructureSheaf f) k).comap g =
      idealSheaf (pushforwardStructureSheaf q) k := by
  have hq : IsFinite q := MorphismProperty.of_isPullback (P := @IsFinite) h ‹IsFinite f›
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun V : U.affineOpens ↦ (⟨g ⁻¹ᵁ V.1, V.2.preimage g⟩ : T.affineOpens))
    (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top U)) fun V ↦ ?_
  have hfinCD : Module.Finite Γ(T, (⟨g ⁻¹ᵁ V.1, V.2.preimage g⟩ : T.affineOpens).1)
      Γ(pushforwardStructureSheaf q, (⟨g ⁻¹ᵁ V.1, V.2.preimage g⟩ : T.affineOpens).1) :=
    module_finite_pushforwardStructureSheaf q ⟨g ⁻¹ᵁ V.1, V.2.preimage g⟩
  rw [ideal_comap_of_isAffineHom, ideal_idealSheaf_pushforward, ideal_idealSheaf_pushforward]
  rcases lt_or_ge k 0 with hk | hk
  · rw [fittingIdeal_eq_bot_of_lt_zero hk, Ideal.map_bot, fittingIdeal_eq_bot_of_lt_zero hk]
  lift k to ℕ using hk with m
  have e : q ⁻¹ᵁ (g ⁻¹ᵁ V.1) ≤ p ⁻¹ᵁ (f ⁻¹ᵁ V.1) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h.w]
  have hpo := isPushout_app_of_isPullback h V e
  let _ : Algebra Γ(U, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  let _ : Algebra Γ(U, V.1) Γ(T, g ⁻¹ᵁ V.1) := (g.app V.1).hom.toAlgebra
  let _ : Algebra Γ(T, g ⁻¹ᵁ V.1) Γ(P, q ⁻¹ᵁ (g ⁻¹ᵁ V.1)) := (q.app (g ⁻¹ᵁ V.1)).hom.toAlgebra
  let _ : Algebra Γ(X, f ⁻¹ᵁ V.1) Γ(P, q ⁻¹ᵁ (g ⁻¹ᵁ V.1)) :=
    (p.appLE (f ⁻¹ᵁ V.1) (q ⁻¹ᵁ (g ⁻¹ᵁ V.1)) e).hom.toAlgebra
  let _ : Algebra Γ(U, V.1) Γ(P, q ⁻¹ᵁ (g ⁻¹ᵁ V.1)) :=
    (g.app V.1 ≫ q.app (g ⁻¹ᵁ V.1)).hom.toAlgebra
  have ht1 : IsScalarTower Γ(U, V.1) Γ(T, g ⁻¹ᵁ V.1) Γ(P, q ⁻¹ᵁ (g ⁻¹ᵁ V.1)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have ht2 : IsScalarTower Γ(U, V.1) Γ(X, f ⁻¹ᵁ V.1) Γ(P, q ⁻¹ᵁ (g ⁻¹ᵁ V.1)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom hpo.w.symm
  have hpo' : IsPushout (CommRingCat.ofHom (algebraMap Γ(U, V.1) Γ(X, f ⁻¹ᵁ V.1)))
      (CommRingCat.ofHom (algebraMap Γ(U, V.1) Γ(T, g ⁻¹ᵁ V.1)))
      (CommRingCat.ofHom (algebraMap Γ(X, f ⁻¹ᵁ V.1) Γ(P, q ⁻¹ᵁ (g ⁻¹ᵁ V.1))))
      (CommRingCat.ofHom (algebraMap Γ(T, g ⁻¹ᵁ V.1) Γ(P, q ⁻¹ᵁ (g ⁻¹ᵁ V.1)))) := by
    simpa [RingHom.algebraMap_toAlgebra] using hpo
  have hbc := (CommRingCat.isPushout_iff_isPushout.mp hpo').symm.out
  have hfinCD' : Module.Finite Γ(T, g ⁻¹ᵁ V.1) Γ(P, q ⁻¹ᵁ (g ⁻¹ᵁ V.1)) := hfinCD
  have hfinBA : Module.Finite Γ(U, V.1) Γ(X, f ⁻¹ᵁ V.1) :=
    module_finite_pushforwardStructureSheaf f V
  have hfinT : Module.Finite Γ(T, g ⁻¹ᵁ V.1)
      (TensorProduct Γ(U, V.1) Γ(T, g ⁻¹ᵁ V.1) Γ(X, f ⁻¹ᵁ V.1)) :=
    Module.Finite.equiv hbc.equiv.symm
  exact ((fittingIdeal_basic_properties.{u, u, u, u} (R := Γ(U, V.1))
    (M := Γ(X, f ⁻¹ᵁ V.1))).2.2.1 Γ(T, g ⁻¹ᵁ V.1) m).symm.trans
    (fittingIdeal_eq_of_linearEquiv hbc.equiv m)

end Stacks.Fitting

namespace Stacks.Groupoids

/-- Every member of the Fitting stratification is invariant under the groupoid.

The second projection of the scheme of composable pairs is simultaneously the base change of
source along target and the base change of source along source, by the two cartesian lower
squares of the diagram of Stacks Tag 04LF. So both inverse images of a member of the
stratification are the Fitting ideal sheaf of the pushforward of the structure sheaf along that
single projection. -/
@[stacks 0AB9 "invariance"]
theorem finiteStratification_invariant {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    IsInvariantClosedSubscheme G (finiteStratification G n) := by
  have hLeft : IsPullback (pullback.fst G.source G.target).left
      (pullback.snd G.source G.target).left G.source.left G.target.left :=
    (IsPullback.of_hasPullback G.source G.target).map (Over.forget S)
  have hRight : IsPullback G.comp.left (pullback.snd G.source G.target).left
      G.source.left G.source.left :=
    G.comp_source_isPullback.map (Over.forget S)
  rw [IsInvariantClosedSubscheme, finiteStratification,
    Fitting.comap_idealSheaf_pushforward_of_isPullback hLeft (n : ℤ),
    Fitting.comap_idealSheaf_pushforward_of_isPullback hRight (n : ℤ)]

end Stacks.Groupoids

end
