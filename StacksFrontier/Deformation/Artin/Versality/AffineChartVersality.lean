module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityAffineOpenBase
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal

/-!
# Versality at a point, compared with versality of the formal object over an affine chart

[Stacks, Tag 0CXK] compares versality of `x` at a finite type point `u₀` with versality of the
formal object `ξ` attached to a complete local restriction of `x` there, and it states the
latter relative to one and only one base ring: the local ring `𝒪_{S,s}` of `S` at the image of
`u₀`. The criterion of [Stacks, Tag 06IU] is what one wants to apply to `ξ`, but the data it is
applied to in [Stacks, Tag 07YM] — the morphism `ξ : E ⟶ NL_{A/Λ}` and the conditions (i) and
(ii) it satisfies — lives over the ring `Λ` of an affine open `Spec Λ ⊆ S`, not over the local
ring.

This file closes that gap. `Deformation.Artin.liftsAtResiduePoint_iff_isVersal` is the
`Λ`-generic core of [Stacks, Tag 0CXK]: it compares versality of `ξ` relative to an arbitrary
`Λ` with the lifting property at the residue field of the complete local base.
`Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_affineOpen` is the other half: versality
at `u₀` is the lifting property with the ring of an affine open as deformation base. The two
are joined here by the identification of the residue field of `U` at `u₀` with the residue
field of the complete local base.

## Main results

* `Deformation.Artin.liftsAtResiduePoint_iff_completionResiduePoint` — the lifting property at
  the canonical residue-field point of `u₀` and the lifting property at the residue field of a
  presentation of the completed local ring are the same property, over any base ring whose
  morphism to `S` is a monomorphism compatible with the residue point.
* `Deformation.Artin.isVersalAt_iff_isVersal_affineChart` — **versality at `u₀` is versality of
  the formal object over the ring of an affine open.** This is the bridge the direction
  `(2) ⇒ (1)` of [Stacks, Tag 07YM] runs along: the conditions of [Stacks, Tag 06IU] are
  proved for the formal object over `𝒞_Λ`, and this turns the resulting versality back into
  versality of `x` at the point.

## Implementation notes

The identification of the two residue fields is `Deformation.Artin.completionResidueEquiv`,
and that it is `Λ`-linear is not an extra hypothesis: it follows from the compatibility
`hcompat` of the residue point with `Spec Λ ⟶ S`, which
`Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_affineOpen` already asks for, together
with the factorizations `hΛ` and `hbase` of the structure morphism of the complete local base.
The only thing used of `Spec Λ ⟶ S` for that step is that it is a monomorphism; being an open
immersion is used once more, to produce the germ map `Λ ⟶ 𝒪_{S,s}` that
`Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_affineOpen` needs.

`IsLocallyNoetherian U.left` is a hypothesis rather than a consequence: the comparison of the
residue fields goes through the completed local ring, which is formed under that assumption.
In the application `U` is affine of finite type over a locally Noetherian `S`.

## References

* [Stacks Project, Tag 0CXK](https://stacks.math.columbia.edu/tag/0CXK)
* [Stacks Project, Tag 0CXJ](https://stacks.math.columbia.edu/tag/0CXJ)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

section Comparison

variable {Λ : Type u} [CommRing Λ] {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
  (U : Over S) [IsLocallyNoetherian U.left]
  {F : Type v} [Category.{w} F] (q : F ⥤ Over S)
  (u₀ : U.left) (x : F) (hx : q.obj x = U)
  {R : Type u} [CommRing R] [IsLocalRing R] [Algebra Λ R]
  (e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* R)
  (g : Spec (.of R) ⟶ U.left)
  (hg : g = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
      (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫ U.left.fromSpecStalk u₀)

include e hg in
/-- **The residue field of `U` at `u₀` is the residue field of the complete local
presentation, `Λ`-linearly.** The underlying ring equivalence is
`Deformation.Artin.completionResidueEquiv`; that it commutes with the two structure maps from
`Λ` is forced, `Spec Λ ⟶ S` being a monomorphism, by the compatibility of the residue point
with `Spec Λ ⟶ S` and the factorization of the structure morphism of `Spec R`. -/
public def completionResidueAlgEquiv [Mono iΛ]
    [algk : Algebra Λ (U.left.residueField u₀)]
    (hcompat : Spec.map (CommRingCat.ofHom (algebraMap Λ (U.left.residueField u₀))) ≫ iΛ =
      U.left.fromSpecResidueField u₀ ≫ U.hom)
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ = g ≫ U.hom) :
    U.left.residueField u₀ ≃ₐ[Λ] ResidueField R :=
  let E := completionResidueEquiv U.left u₀ e
  have hE : Spec.map (CommRingCat.ofHom E.toRingHom) ≫ U.left.fromSpecResidueField u₀ =
      Spec.map (CommRingCat.ofHom (residue R)) ≫ g := by
    simpa only [hg] using completionResidueEquiv_spec U.left u₀ e
  have hc : E.toRingHom.comp (algebraMap Λ (U.left.residueField u₀)) =
      algebraMap Λ (ResidueField R) := by
    have hring : (algebraMap Λ (ResidueField R)) = (residue R).comp (algebraMap Λ R) := by
      ext l
      rfl
    have h : Spec.map (CommRingCat.ofHom
          (E.toRingHom.comp (algebraMap Λ (U.left.residueField u₀)))) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField R))) ≫ iΛ := by
      rw [show CommRingCat.ofHom (E.toRingHom.comp (algebraMap Λ (U.left.residueField u₀))) =
          CommRingCat.ofHom (algebraMap Λ (U.left.residueField u₀)) ≫
            CommRingCat.ofHom E.toRingHom from rfl,
        Spec.map_comp, Category.assoc, hcompat, ← Category.assoc, hE, Category.assoc, ← hbase,
        hring, show CommRingCat.ofHom ((residue R).comp (algebraMap Λ R)) =
          CommRingCat.ofHom (algebraMap Λ R) ≫ CommRingCat.ofHom (residue R) from rfl,
        Spec.map_comp]
      exact (Category.assoc _ _ _).symm
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono iΛ).mp h))
  { __ := E, commutes' := DFunLike.congr_fun hc }

include e hg in
/-- **The lifting property at the residue point of `u₀` is the lifting property at the residue
field of a complete local presentation there.** Both are read over the same base ring `Λ`;
`Deformation.Artin.liftsAtResiduePoint_iff_changeResidueField` moves between them along
`Deformation.Artin.completionResidueAlgEquiv`. -/
public theorem liftsAtResiduePoint_iff_completionResiduePoint [Mono iΛ]
    [algk : Algebra Λ (U.left.residueField u₀)]
    (hcompat : Spec.map (CommRingCat.ofHom (algebraMap Λ (U.left.residueField u₀))) ≫ iΛ =
      U.left.fromSpecResidueField u₀ ≫ U.hom)
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ = g ≫ U.hom) :
    LiftsAtResiduePoint (Λ := Λ) (k := U.left.residueField u₀) iΛ q U x hx
        (U.left.fromSpecResidueField u₀) ↔
      LiftsAtResiduePoint (Λ := Λ) (k := ResidueField R) (alg := ResidueField.algebra R)
        iΛ q U x hx (Spec.map (CommRingCat.ofHom (residue R)) ≫ g) := by
  have hE : Spec.map (CommRingCat.ofHom
        (completionResidueAlgEquiv iΛ U u₀ e g hg hcompat hbase).toAlgHom.toRingHom) ≫
      U.left.fromSpecResidueField u₀ =
        Spec.map (CommRingCat.ofHom (residue R)) ≫ g := by
    conv_rhs => rw [hg]
    exact completionResidueEquiv_spec U.left u₀ e
  have h := liftsAtResiduePoint_iff_changeResidueField
    (completionResidueAlgEquiv iΛ U u₀ e g hg hcompat hbase) iΛ q U x hx
    (U.left.fromSpecResidueField u₀)
  rwa [hE] at h

end Comparison

section AffineChart

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F]
  (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (U : Over S) (x : F) (hx : (p ⋙ Over.post B.inclusion).obj x = U)
  (u₀ : U.left) [IsLocallyNoetherian U.left]
  (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
  (ξ : Deformation.Artin.FormalObject B S hS p)
  (hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
  (e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* ξ.base.R)
  (g : Spec (.of ξ.base.R) ⟶ U.left)
  (hg : g = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap (U.left.presheaf.stalk u₀)
        (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
    U.left.fromSpecStalk u₀)
  (hbase : ξ.base.toS = g ≫ U.hom)
  (r : xR.obj.1 ⟶ x)
  (hr : p.IsCartesian (p.map r) r)
  (hrbase : HEq
    ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
      p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) g)
  (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R]
  (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
  (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)

include xR hξ e g hg hbase r hr hrbase in
/-- **Versality at a point is versality of the formal object, over the ring of an affine
open.** Let `x` be an object over `U`, let `u₀` be a point of `U` whose image in `S` lies in
an affine open `Spec Λ`, and let `ξ` be the formal object attached by the approximation functor
of [Stacks, Tag 07X6] to a Cartesian restriction of `x` over a presentation of the completed
local ring at `u₀`, with the structure morphism of its base factored through `Spec Λ`. Then `x`
is versal at `u₀` exactly when `ξ` is versal relative to `Λ` in the sense of
[Stacks, Tag 0CXJ].

This is [Stacks, Tag 0CXK] with the base ring moved off the local ring `𝒪_{S,s}` and onto the
ring of an affine open: `Deformation.Artin.liftsAtResiduePoint_iff_isVersal` is the right-hand
comparison, `Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_affineOpen` the left-hand
one, and `Deformation.Artin.liftsAtResiduePoint_iff_completionResiduePoint` identifies the two
residue-field points they are stated at.

The point `t` of `Spec Λ` and the equation `iΛ t = basePoint U u₀` are the statement that the
structure morphism of `U` carries `u₀` into the affine open, and `hcompat` is the
compatibility of the residue point of `u₀` with that factorization. Both are what the
left-hand comparison asks of an affine chart; nothing further is assumed of `Λ`. -/
public theorem isVersalAt_iff_isVersal_affineChart
    (t : Spec (.of Λ)) (ht : iΛ t = Deformation.Artin.basePoint U u₀)
    [Algebra Λ (U.left.residueField u₀)]
    (hcompat : Spec.map (CommRingCat.ofHom (algebraMap Λ (U.left.residueField u₀))) ≫ iΛ =
      U.left.fromSpecResidueField u₀ ≫ U.hom) :
    Deformation.Artin.IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx ↔
      Deformation.Artin.FormalObject.IsVersal B S hS p hp ξ Λ iΛ hΛ := by
  have hmono : Mono iΛ := inferInstance
  refine ((isVersalAt_iff_liftsAtResiduePoint_affineOpen iΛ U (p ⋙ Over.post B.inclusion) u₀ x hx
    t ht hcompat).trans ?_).trans
      (liftsAtResiduePoint_iff_isVersal B S hS p hp U x hx u₀ xR ξ hξ e g hg hbase r hr hrbase
        Λ iΛ hΛ)
  exact liftsAtResiduePoint_iff_completionResiduePoint iΛ U (p ⋙ Over.post B.inclusion) u₀ x hx
    e g hg hcompat (hΛ.trans hbase)

end AffineChart

end Deformation.Artin

end
