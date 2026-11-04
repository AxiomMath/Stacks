module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceTheta
public import StacksFrontier.AlgebraicGeometry.Spaces.PointFamilyDescent

/-!
# The chart maps `χ_w` of `θ` of Stacks 0D2Z along morphisms of scheme points

For a pair `(ℒ, ψ)` on the small étale site of an algebraic space `X` over the algebraic space
`Y` of Situation 0849, the chart maps `χ_w : w^*(r^*𝒪(d)) ⟶ w^*(ℒ^{⊗ d}|_{U(ψ)})` at the scheme
points `w` of `U(ψ)` (`…InvertibleTwistingRestriction.chartMap`) are each a composite of three
factors: the identification of the source with the module attached to `c_w^*𝒪(d)`, the module
attached to `θ` of [Stacks, Tag 01O9] on `W`, and the identification of the module attached to
`(w^*ℒ)^{⊗ d}` with the target.  Along a morphism `τ : T' ⟶ T` of test schemes, each factor
forms a square with its counterpart at `w ∘ τ`.

This file proves **the square of the target identification**: the coherence of Stacks 03LU behind
it, at variables, the naturality of `x^*(ℒ^{⊗ n}) ≅ ((x^*ℒ)^{⊗ n})^a` in the scheme point for any
`x' = x ∘ τ`, and their instance at the scheme points of `U(ψ)`.

## Main results

* `AlgebraicGeometry.Space.modulePullback_map_comp_comp_eq_of_square`,
  `AlgebraicGeometry.Space.modulePullback_map_eq_of_square`: the abstract coherence (Stacks 03LU)
  behind the target square, with the factors as variables.
* `AlgebraicGeometry.Space.pointTargetIso_hom_naturality`,
  `AlgebraicGeometry.Space.pointTargetIso_hom_naturality_of_eq`: the naturality of
  `x^*(ℒ^{⊗ n}) ≅ ((x^*ℒ)^{⊗ n})^a` in the scheme point, with the identification read as one
  morphism, for a scheme point `x'` equal to `x ∘ τ`.
* `AlgebraicGeometry.Space.pullbackTransportSquare_of_squares`: the square of a three-factor
  composite from the squares of its factors.
* `…InvertibleTwistingRestriction.map_comp_locusPoint`: the scheme point of `X` under `w ∘ τ`.
* `…InvertibleTwistingRestriction.chartSection_comp_of_liesOver`: the sections `c_x` are natural in
  the scheme point.
* `…InvertibleTwistingRestriction.chartTarget_square`: **the square of the target factor of the
  chart maps** along `τ : T' ⟶ T`.

## Implementation notes

The factors of the composites are variables with their values as equations: the same
equations written for concrete composites exhaust the kernel (an `rfl` unfolding
`(t.symm ≪≫ eqToIso h ≪≫ (c.app M).symm).hom` already does), and substituting an equation
`q = p ≫ ι` for a morphism `q` occurring in the type of an isomorphism does too.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space

section Coherence

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X U Y Z : AlgebraicSpaces B S hS}

/-- The transport along `r ≫ p ≫ ι = (r ≫ p) ≫ ι` is the identity. -/
theorem pullbackTransport_assoc_eq_id {W : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) (r : W ⟶ Y) (p : Y ⟶ U) (ι : U ⟶ X)
    (h : r ≫ p ≫ ι = (r ≫ p) ≫ ι) :
    pullbackTransport M h = 𝟙 _ :=
  (rfl : pullbackTransport M (rfl : r ≫ p ≫ ι = r ≫ p ≫ ι) = 𝟙 _)

/-- The associativity coherence of Stacks 03LU, with the inner comparison inverted. -/
theorem modulePullback_map_inv_comp_modulePullbackCompIso_hom_app {W : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) (r : W ⟶ Y) (p : Y ⟶ U) (ι : U ⟶ X) :
    (modulePullback B S hS r).map ((modulePullbackCompIso B S hS p ι).inv.app M) ≫
        (modulePullbackCompIso B S hS r p).hom.app ((modulePullback B S hS ι).obj M) =
      (modulePullbackCompIso B S hS r (p ≫ ι)).hom.app M ≫
        (modulePullbackCompIso B S hS (r ≫ p) ι).inv.app M := by
  refine (Iso.eq_comp_inv ((modulePullbackCompIso B S hS (r ≫ p) ι).app M)).2 ?_
  have ha := modulePullbackCompIso_assoc_app B S hS r p ι M
  simp only [Iso.app_hom, Category.assoc]
  rw [ha, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

/-- The associativity coherence of Stacks 03LU along `r ≫ p = p'`, with transports. -/
theorem modulePullback_map_inv_comp_modulePullbackCompIso_hom_app_comp_pullbackTransport
    {W : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2) (r : W ⟶ Y) (p : Y ⟶ U)
    {p' : W ⟶ U} (ι : U ⟶ X) (hp : r ≫ p = p') (hrq : r ≫ p ≫ ι = p' ≫ ι) :
    (modulePullback B S hS r).map ((modulePullbackCompIso B S hS p ι).inv.app M) ≫
        (modulePullbackCompIso B S hS r p).hom.app ((modulePullback B S hS ι).obj M) ≫
          pullbackTransport ((modulePullback B S hS ι).obj M) hp =
      (modulePullbackCompIso B S hS r (p ≫ ι)).hom.app M ≫ pullbackTransport M hrq ≫
        (modulePullbackCompIso B S hS p' ι).inv.app M := by
  subst hp
  rw [pullbackTransport_assoc_eq_id M r p ι hrq, Category.id_comp,
    ← modulePullback_map_inv_comp_modulePullbackCompIso_hom_app M r p ι]
  simp [pullbackTransport]

/-- The comparison `r^*q^* ≅ (r ≫ q)^*` of Stacks 03LU transported along `q = q₂`. -/
theorem modulePullbackCompIso_hom_app_comp_pullbackTransport {W : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) (r : W ⟶ Y) {q q₂ : Y ⟶ X} (hq : q = q₂)
    (h : r ≫ q = r ≫ q₂) :
    (modulePullbackCompIso B S hS r q).hom.app M ≫ pullbackTransport M h =
      (modulePullback B S hS r).map (pullbackTransport M hq) ≫
        (modulePullbackCompIso B S hS r q₂).hom.app M := by
  subst hq
  simp [pullbackTransport]

/-- The core of `AlgebraicGeometry.Space.modulePullback_map_trans_hom_comp_eq_of_square`. -/
theorem modulePullback_map_pullbackTransport_comp_eq {W : AlgebraicSpaces B S hS} (ι : U ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (r : W ⟶ Y) {q : Y ⟶ X} {q' : W ⟶ X}
    (hrq : r ≫ q = q') (p : Y ⟶ U) (p' : W ⟶ U) (hp : r ≫ p = p') (hq : q = p ≫ ι)
    (hq' : q' = p' ≫ ι) :
    (modulePullback B S hS r).map (pullbackTransport M hq) ≫
        (modulePullback B S hS r).map ((modulePullbackCompIso B S hS p ι).inv.app M) ≫
          (modulePullbackCompIso B S hS r p).hom.app ((modulePullback B S hS ι).obj M) ≫
            pullbackTransport ((modulePullback B S hS ι).obj M) hp =
      (modulePullbackCompIso B S hS r q).hom.app M ≫ pullbackTransport M hrq ≫
        pullbackTransport M hq' ≫ (modulePullbackCompIso B S hS p' ι).inv.app M := by
  have hrq₂ : r ≫ p ≫ ι = p' ≫ ι := (congrArg (r ≫ ·) hq).symm.trans (hrq.trans hq')
  have e1 := modulePullback_map_inv_comp_modulePullbackCompIso_hom_app_comp_pullbackTransport M r p
    ι hp hrq₂
  have e2 := modulePullbackCompIso_hom_app_comp_pullbackTransport M r hq (congrArg (r ≫ ·) hq)
  have e3 := pullbackTransport_comp M (congrArg (r ≫ ·) hq) hrq₂ (hrq.trans hq')
  have e4 := pullbackTransport_comp M hrq hq' (hrq.trans hq')
  rw [e1, reassoc_of% e2.symm, reassoc_of% e3, ← reassoc_of% e4]

/-- **The abstract coherence behind the square of the target identification** (Stacks 03LU):
for `ι : U ⟶ X`, points `p : Y ⟶ U`, `p' : Z ⟶ U` with `r ≫ p = p'`, and identifications
`t : q^*M ≅ E`, `t' : q'^*M ≅ E'` along `q = p ≫ ι`, `q' = p' ≫ ι`, a square
`r^*t ≫ c = (r^*q^* ≅ q'^*) ≫ t'` gives the square along `r` of the composites
`E ≅ q^*M ≅ (p ≫ ι)^*M ≅ p^*(ι^*M)` and `E' ≅ q'^*M ≅ (p' ≫ ι)^*M ≅ p'^*(ι^*M)`.  The factors of
the composites are variables `a, b, i` (and `a', b', i'`) with their values as equations, so
that the lemma applies to any spelling of them. -/
theorem modulePullback_map_comp_comp_eq_of_square (ι : U ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (r : Z ⟶ Y) {q : Y ⟶ X} {q' : Z ⟶ X}
    {E : Modules.{u, u} B S hS Y.1 Y.2} {E' : Modules.{u, u} B S hS Z.1 Z.2}
    (t : (modulePullback B S hS q).obj M ≅ E) (t' : (modulePullback B S hS q').obj M ≅ E')
    (c : (modulePullback B S hS r).obj E ⟶ E') (hrq : r ≫ q = q')
    (hN : (modulePullback B S hS r).map t.hom ≫ c =
      ((modulePullbackCompIso B S hS r q).hom.app M ≫ pullbackTransport M hrq) ≫ t'.hom)
    (p : Y ⟶ U) (p' : Z ⟶ U) (hp : r ≫ p = p') (hq : q = p ≫ ι) (hq' : q' = p' ≫ ι)
    (a : E ⟶ (modulePullback B S hS q).obj M) (ha : a = t.inv)
    (b : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS (p ≫ ι)).obj M)
    (hb : b = pullbackTransport M hq)
    (i : (modulePullback B S hS (p ≫ ι)).obj M ⟶
      (modulePullback B S hS p).obj ((modulePullback B S hS ι).obj M))
    (hi : i = (modulePullbackCompIso B S hS p ι).inv.app M)
    (a' : E' ⟶ (modulePullback B S hS q').obj M) (ha' : a' = t'.inv)
    (b' : (modulePullback B S hS q').obj M ⟶ (modulePullback B S hS (p' ≫ ι)).obj M)
    (hb' : b' = pullbackTransport M hq')
    (i' : (modulePullback B S hS (p' ≫ ι)).obj M ⟶
      (modulePullback B S hS p').obj ((modulePullback B S hS ι).obj M))
    (hi' : i' = (modulePullbackCompIso B S hS p' ι).inv.app M) :
    (modulePullback B S hS r).map (a ≫ b ≫ i) ≫
        ((modulePullbackCompIso B S hS r p).hom.app ((modulePullback B S hS ι).obj M) ≫
          pullbackTransport ((modulePullback B S hS ι).obj M) hp) =
      c ≫ a' ≫ b' ≫ i' := by
  subst ha hb hi ha' hb' hi'
  have hc := (Iso.eq_inv_comp ((modulePullback B S hS r).mapIso t)).2 hN
  have core := modulePullback_map_pullbackTransport_comp_eq ι M r hrq p p' hp hq hq'
  rw [hc, Functor.mapIso_inv, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [core, Iso.hom_inv_id_assoc]

/-- The value of the composite `E ≅ q^*M ≅ (p ≫ ι)^*M ≅ p^*(ι^*M)`. -/
theorem trans_eqToIso_trans_symm_hom (ι : U ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2)
    {q : Y ⟶ X} {E : Modules.{u, u} B S hS Y.1 Y.2} (t : (modulePullback B S hS q).obj M ≅ E)
    (p : Y ⟶ U) (hq : q = p ≫ ι) :
    (t.symm ≪≫ eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) hq) ≪≫
        ((modulePullbackCompIso B S hS p ι).app M).symm).hom =
      t.inv ≫ pullbackTransport M hq ≫ (modulePullbackCompIso B S hS p ι).inv.app M := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Iso.app_inv, eqToIso.hom,
    ← pullbackTransport_eq_eqToHom]

/-- `AlgebraicGeometry.Space.modulePullback_map_comp_comp_eq_of_square` for the composites given
as the isomorphisms `E ≅ q^*M ≅ (p ≫ ι)^*M ≅ p^*(ι^*M)`, through variables `x`, `x'` equal to
them. -/
theorem modulePullback_map_eq_of_square (ι : U ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (r : Z ⟶ Y) {q : Y ⟶ X} {q' : Z ⟶ X}
    {E : Modules.{u, u} B S hS Y.1 Y.2} {E' : Modules.{u, u} B S hS Z.1 Z.2}
    (t : (modulePullback B S hS q).obj M ≅ E) (t' : (modulePullback B S hS q').obj M ≅ E')
    (c : (modulePullback B S hS r).obj E ⟶ E') (hrq : r ≫ q = q')
    (hN : (modulePullback B S hS r).map t.hom ≫ c =
      ((modulePullbackCompIso B S hS r q).hom.app M ≫ pullbackTransport M hrq) ≫ t'.hom)
    (p : Y ⟶ U) (p' : Z ⟶ U) (hp : r ≫ p = p') (hq : q = p ≫ ι) (hq' : q' = p' ≫ ι)
    (x : E ⟶ (modulePullback B S hS p).obj ((modulePullback B S hS ι).obj M))
    (hx : x = (t.symm ≪≫ eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) hq) ≪≫
        ((modulePullbackCompIso B S hS p ι).app M).symm).hom)
    (x' : E' ⟶ (modulePullback B S hS p').obj ((modulePullback B S hS ι).obj M))
    (hx' : x' = (t'.symm ≪≫ eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) hq') ≪≫
        ((modulePullbackCompIso B S hS p' ι).app M).symm).hom) :
    (modulePullback B S hS r).map x ≫
        ((modulePullbackCompIso B S hS r p).hom.app ((modulePullback B S hS ι).obj M) ≫
          pullbackTransport ((modulePullback B S hS ι).obj M) hp) = c ≫ x' := by
  rw [hx, hx', trans_eqToIso_trans_symm_hom, trans_eqToIso_trans_symm_hom]
  exact modulePullback_map_comp_comp_eq_of_square ι M r t t' c hrq hN p p' hp hq hq' _ rfl _ rfl
    _ rfl _ rfl _ rfl _ rfl

/-- A square read through a factorisation of its first and last morphisms: if
`F(z) ≫ F(l) ≫ c ≫ t = κ ≫ z' ≫ l'`, then `F(T) ≫ c ≫ t = κ ≫ T'` for `T = z ≫ l` and
`T' = z' ≫ l'`. -/
theorem map_comp_comp_eq_of_factor {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b e : C} {a₁ a₂ a₃ a₄ : D} (z : a ⟶ b) (l : b ⟶ e) (T : a ⟶ e) (hT : T = z ≫ l)
    (c : F.obj e ⟶ a₁) (t : a₁ ⟶ a₂) (κ : F.obj a ⟶ a₃) (z' : a₃ ⟶ a₄) (l' : a₄ ⟶ a₂)
    (T' : a₃ ⟶ a₂) (hT' : T' = z' ≫ l') (h : F.map z ≫ F.map l ≫ c ≫ t = κ ≫ z' ≫ l') :
    F.map T ≫ c ≫ t = κ ≫ T' := by
  subst hT hT'
  rw [F.map_comp, Category.assoc]
  exact h

/-- **A square of a three-factor composite from the squares of its factors**: if
`c = s ≫ m ≫ t` and `c' = s' ≫ m' ≫ t'` along `f : Z ⟶ Y` with `f ≫ x = x'`, and `f^*s`, `f^*m`,
`f^*t` form squares with `s'`, `m'`, `t'` through `β`, `γ` and the comparisons of Stacks 03LU
followed by the transports along `f ≫ x = x'`, then `c` and `c'` form a
`AlgebraicGeometry.Space.PullbackTransportSquare`.  The composites are variables with their values
as equations. -/
theorem pullbackTransportSquare_of_squares (f : Z ⟶ Y)
    (x : Y ⟶ X) (x' : Z ⟶ X) (h : f ≫ x = x') (G H : Modules.{u, u} B S hS X.1 X.2)
    {A₁ A₂ : Modules.{u, u} B S hS Y.1 Y.2} {A₁' A₂' : Modules.{u, u} B S hS Z.1 Z.2}
    (s : (modulePullback B S hS x).obj G ⟶ A₁) (m : A₁ ⟶ A₂)
    (t : A₂ ⟶ (modulePullback B S hS x).obj H)
    (s' : (modulePullback B S hS x').obj G ⟶ A₁') (m' : A₁' ⟶ A₂')
    (t' : A₂' ⟶ (modulePullback B S hS x').obj H)
    (β : (modulePullback B S hS f).obj A₁ ⟶ A₁') (γ : (modulePullback B S hS f).obj A₂ ⟶ A₂')
    (hs : (modulePullback B S hS f).map s ≫ β =
      ((modulePullbackCompIso B S hS f x).hom.app G ≫ pullbackTransport G h) ≫ s')
    (hm : (modulePullback B S hS f).map m ≫ γ = β ≫ m')
    (ht : (modulePullback B S hS f).map t ≫
        ((modulePullbackCompIso B S hS f x).hom.app H ≫ pullbackTransport H h) = γ ≫ t')
    (c : (modulePullback B S hS x).obj G ⟶ (modulePullback B S hS x).obj H)
    (c' : (modulePullback B S hS x').obj G ⟶ (modulePullback B S hS x').obj H)
    (hc : c = s ≫ m ≫ t) (hc' : c' = s' ≫ m' ≫ t') :
    PullbackTransportSquare f x x' h G H c c' := by
  refine ⟨?_⟩
  subst hc hc'
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ht,
    ← Category.assoc ((modulePullback B S hS f).map m), hm, Category.assoc,
    ← Category.assoc ((modulePullback B S hS f).map s), hs, Category.assoc]

end Coherence

section Target

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (L : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  [hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B S hS X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L]
  {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)

/-- **The naturality of `x^*(ℒ^{⊗ n}) ≅ ((x^*ℒ)^{⊗ n})^a` in the scheme point**
(`AlgebraicGeometry.Space.pointTargetIso_naturality`), with the identification read as one
morphism: `τ^*` of the identification at `x`, followed by `τ^*(M^a) ≅ (τ^*M)^a` and the module
attached to `τ^*((x^*ℒ)^{⊗ n}) ⟶ ((x ∘ τ)^*ℒ)^{⊗ n}`, is the comparison of Stacks 03LU followed by
the identification at `x ∘ τ`. -/
theorem pointTargetIso_hom_naturality (n : ℤ) :
    (modulePullback B S hS (representedSpaceMap B S hS τ)).map (pointTargetIso L T x n).hom ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS τ (pointLaurentPieceQcoh L T x n)).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map
            (pointLaurentPiecePullbackHom L τ x n)).hom =
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom x)).hom.app _ ≫
          pullbackTransport _ (pointHom_comp τ rfl)) ≫
        (pointTargetIso L T' (yoneda.map τ ≫ x) n).hom :=
  map_comp_comp_eq_of_factor _ _ _ _ (pointTargetIso_hom L T x n) _ _ _ _ _ _
    (pointTargetIso_hom L T' (yoneda.map τ ≫ x) n) (pointTargetIso_naturality L τ x n)

/-- `AlgebraicGeometry.Space.pointTargetIso_hom_naturality` for a scheme point `x'` equal to
`x ∘ τ` and any morphism `ρ` which is the comparison followed by the transport of
`((x ∘ τ)^*ℒ)^{⊗ n}` along `x ∘ τ = x'`. -/
theorem pointTargetIso_hom_naturality_of_eq (x' : yoneda.obj T' ⟶ X.1)
    (e : yoneda.map τ ≫ x = x') (n : ℤ)
    (ρ : quasicoherentPullbackObj B S hS τ (pointLaurentPieceQcoh L T x n) ⟶
      pointLaurentPieceQcoh L T' x' n)
    (hρ : ρ = pointLaurentPiecePullbackHom L τ x n ≫
      eqToHom (congrArg (fun k => pointLaurentPieceQcoh L T' k n) e)) :
    (modulePullback B S hS (representedSpaceMap B S hS τ)).map (pointTargetIso L T x n).hom ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS τ (pointLaurentPieceQcoh L T x n)).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map ρ).hom =
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom x)).hom.app _ ≫
          pullbackTransport _ (pointHom_comp τ e)) ≫
        (pointTargetIso L T' x' n).hom := by
  subst e
  obtain rfl : ρ = pointLaurentPiecePullbackHom L τ x n := hρ.trans (by simp)
  exact pointTargetIso_hom_naturality L τ x n

end Target

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  {T T' : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase} (τ : T' ⟶ T)
  {w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj}
  {w' : yoneda.obj T' ⟶ (locusSpaceOfUnitalHom s f L ψ).obj} (hw : yoneda.map τ ≫ w = w')

include hw in
/-- The scheme points of `X` underlying `w` and `w ∘ τ`:
`locusPoint (w ∘ τ) = locusPoint w ∘ τ`. -/
theorem map_comp_locusPoint : yoneda.map τ ≫ locusPoint w = locusPoint w' :=
  congrArg (fun k => k.hom) ((pointHom_comp τ rfl).symm.trans
    ((congrArg (representedSpaceMap _ _ _ τ ≫ ·) (pointHom_locusPoint w)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ locusInclusionOfUnitalHom s f L ψ) (pointHom_comp τ hw)).trans
          (pointHom_locusPoint w').symm))))

include hw in
/-- **The square of the target factor of the chart maps along `τ : T' ⟶ T`**: for scheme points
`w` of `U(ψ)` at `T` and `w' = w ∘ τ` at `T'`, `τ^*` of the target factor
`((w^*ℒ)^{⊗ d})^a ≅ w^*(ℒ^{⊗ d}) = (ι ∘ w)^*(ℒ^{⊗ d}) ≅ w^*(ℒ^{⊗ d}|_{U(ψ)})` of `χ_w`
(the inverse of `AlgebraicGeometry.Space.pointTargetIso`, the transport along
`…InvertibleTwistingRestriction.pointHom_locusPoint` and the comparison of Stacks 03LU for `w`
and the inclusion `ι : U(ψ) ⟶ X`), followed by the comparison of Stacks 03LU for `τ` and `w` and
the transport along `w ∘ τ = w'`, is `τ^*(M^a) ≅ (τ^*M)^a` followed by the module attached to
`τ^*((w^*ℒ)^{⊗ d}) ⟶ ((w ∘ τ)^*ℒ)^{⊗ d}` and the target factor of `χ_{w'}`.

The statement is the instance of
`AlgebraicGeometry.Space.modulePullback_map_comp_comp_eq_of_square` (`type_of%`), so that the
target factor is spelled as that lemma spells it: a definition of the factor would have its nested
proofs (`s.shrink.containsBase`, the algebraicity of the represented spaces) abstracted into
auxiliary lemmas, and its unfolding never matches a statement. -/
theorem chartTarget_square (d : ℤ) :
    type_of% (modulePullback_map_comp_comp_eq_of_square
    (locusInclusionOfUnitalHom s f L ψ) _ (representedSpaceMap _ _ _ τ)
    (pointTargetIso L T (locusPoint w) d) (pointTargetIso L T' (locusPoint w') d) _
    (pointHom_comp τ (map_comp_locusPoint τ hw))
    (pointTargetIso_hom_naturality_of_eq L τ (locusPoint w) (locusPoint w')
      (map_comp_locusPoint τ hw) d _ rfl)
    (pointHom w) (pointHom w') (pointHom_comp τ hw) (pointHom_locusPoint w)
    (pointHom_locusPoint w') _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl) :=
  modulePullback_map_comp_comp_eq_of_square
    (locusInclusionOfUnitalHom s f L ψ) _ (representedSpaceMap _ _ _ τ)
    (pointTargetIso L T (locusPoint w) d) (pointTargetIso L T' (locusPoint w') d) _
    (pointHom_comp τ (map_comp_locusPoint τ hw))
    (pointTargetIso_hom_naturality_of_eq L τ (locusPoint w) (locusPoint w')
      (map_comp_locusPoint τ hw) d _ rfl)
    (pointHom w) (pointHom w') (pointHom_comp τ hw) (pointHom_locusPoint w)
    (pointHom_locusPoint w') _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

section ChartSection

variable {s : RelativeProjSituation.{u, m}}
  {X : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {f : X ⟶ s.space.1}
  (R : s.InvertibleTwistingRestriction f)

/-- **The sections `c_x : T ⟶ T ×_Y Proj_Y(𝒜)` of the scheme points of `U(ψ)` are natural**: for
`τ : T' ⟶ T`, scheme points `x` at `T` and `x' = x ∘ τ` at `T'` of `U(ψ)` and a morphism
`y : T' ×_Y Proj_Y(𝒜) ⟶ T ×_Y Proj_Y(𝒜)` lying over `τ`, `y ∘ c_{x'} = c_x ∘ τ`. -/
theorem chartSection_comp_of_liesOver {T T' : BigFppfOver s.site s.base s.containsBase}
    (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X) (hx : R.locusOpen T x = ⊤) (x' : yoneda.obj T' ⟶ X)
    (hx' : R.locusOpen T' x' = ⊤) (hxx' : x' = yoneda.map τ ≫ x)
    (y : s.relativeProjPoints.fibre T' (x' ≫ f) ⟶ s.relativeProjPoints.fibre T (x ≫ f))
    (hy : s.relativeProjPoints.LiesOver y τ) :
    R.chartSection x' hx' ≫ y = τ ≫ R.chartSection x hx := by
  refine s.relativeProjPoints.fibre_hom_ext ?_ ?_
  · rw [Category.assoc, hy.1, ← Category.assoc, R.chartSection_fibreHom, Category.id_comp,
      Category.assoc, R.chartSection_fibreHom, Category.comp_id]
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hy.2,
      R.map_chartSection_fibreToSpace, R.map_chartSection_fibreToSpace,
      R.map_comp_point τ x hx x' hx' hxx']

end ChartSection

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
