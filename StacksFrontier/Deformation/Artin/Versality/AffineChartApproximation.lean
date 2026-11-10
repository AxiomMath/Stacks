module

public import StacksFrontier.Deformation.Artin.Versality.AffineChartVersality
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation

/-!
# Versality at a finite type point of an affine chart, from versality of an approximation

The direction `(2) ⇒ (1)` of [Stacks, Tag 07YM] is proved for a formal object over the ring `Λ`
of an affine open `Spec Λ ⊆ S`, by way of the criterion of [Stacks, Tag 06IU]. What has to come
out of it is versality of the given object `x` at the given finite type point `u₀` of the
affine scheme `Spec A` it lives over. `Deformation.Artin.isVersalAt_iff_isVersal_affineChart`
is the comparison that turns the one into the other, but it asks for a long list of geometric
data at `u₀`: a complete local object restricting `x`, a presentation of the completed local
ring by the base of the associated formal object, the factorizations of the structure
morphisms, the point of `Spec Λ` under `u₀`, and the `Λ`-algebra structure on the residue
field. This file constructs all of it, once, and hands it to the caller.

## Main results

* `Deformation.Artin.exists_ringHom_comp_fromSpecResidueField_of_isOpenImmersion` — the
  residue-field analogue of
  `Deformation.Artin.exists_ringHom_comp_fromSpecStalk_of_isOpenImmersion`: a point of a
  scheme over `S` whose image lies in an affine open `Spec Λ` has a `Λ`-algebra structure on
  its residue field, compatible with the factorization through the affine open.
* `Deformation.Artin.isVersalAt_of_forall_approximation` — **versality at a finite type point
  of an affine chart is versality of any approximation formal object over the ring of the
  affine open.** An eliminator: the geometric setup at `u₀` is constructed in the proof and
  passed to the hypothesis `H`, so the caller of the theorem only has to prove
  `Deformation.Artin.FormalObject.IsVersal` for formal objects it is handed, together with
  everything known about them.

## Implementation notes

The hypotheses of
`Deformation.Artin.exists_completeLocalObject_of_isFiniteTypePoint` — that `Spec A` is locally
Noetherian, and that its structure morphism to `S` is locally of finite type and quasi-compact
— are derived rather than assumed: `A` is Noetherian because it is of finite type over the
Noetherian `Λ`, so `Spec A` is a Noetherian topological space and every morphism out of it is
quasi-compact, and the structure morphism factors as a finite type morphism of affines
followed by an open immersion.

Site containment of `Spec 𝒪_{Spec A, u₀}^∧` is the one hypothesis that remains: membership of
the big fppf site is a bound on the size of a scheme, which no geometric hypothesis supplies.

The `Λ`-algebra structure on the base ring of the formal object is obtained by reading the ring
map `A ⟶ R` off the morphism of affine schemes `Spec R ⟶ Spec A` and composing with
`algebraMap Λ A`. It is introduced once, with `letI`, and passed by name: `RingHom.toAlgebra`
replaces the scalar action by multiplication, so a second copy built the same way is a
different instance and the statements proved about the first do not typecheck against it.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 0CXK](https://stacks.math.columbia.edu/tag/0CXK)
* [Stacks Project, Tag 07X6](https://stacks.math.columbia.edu/tag/07X6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

/-! ### The residue field of a point whose image lies in an affine open -/

/-- **The ring map `Λ ⟶ κ(u₀)` of an affine open containing the image of `u₀`.** For an open
immersion `iΛ : Spec Λ ⟶ S`, a morphism `f : X ⟶ S` and a point `u₀` of `X` whose image is the
image of a point `t` of `Spec Λ`, there is a ring map `Λ ⟶ κ(u₀)` whose spectrum, composed with
`iΛ`, is the canonical morphism `Spec κ(u₀) ⟶ X ⟶ S`.

This is the residue-field analogue of
`Deformation.Artin.exists_ringHom_comp_fromSpecStalk_of_isOpenImmersion`, and it is built the
same way: the topological image of `Spec κ(u₀) ⟶ X ⟶ S` is the single point `iΛ t`, so the
universal property of open immersions lifts the morphism through `iΛ`, and the lift is the
spectrum of a ring map because both its source and its target are affine. -/
public theorem exists_ringHom_comp_fromSpecResidueField_of_isOpenImmersion
    {Λ : Type u} [CommRing Λ] {S : Scheme.{u}} (iΛ : Spec (CommRingCat.of Λ) ⟶ S)
    [IsOpenImmersion iΛ] {X : Scheme.{u}} (f : X ⟶ S) (u₀ : X)
    (t : Spec (CommRingCat.of Λ)) (ht : iΛ t = f u₀) :
    ∃ g : Λ →+* X.residueField u₀,
      Spec.map (CommRingCat.ofHom g) ≫ iΛ = X.fromSpecResidueField u₀ ≫ f := by
  have H : Set.range (X.fromSpecResidueField u₀ ≫ f) ⊆ Set.range iΛ := by
    rintro y ⟨z, rfl⟩
    exact ⟨t, by rw [ht, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩
  refine ⟨ringHom_of_schemeMap (A := Λ) (C := (X.residueField u₀ : Type u))
    (IsOpenImmersion.lift iΛ (X.fromSpecResidueField u₀ ≫ f) H), ?_⟩
  rw [specMap_ringHom_of_schemeMap]
  exact IsOpenImmersion.lift_fac iΛ (X.fromSpecResidueField u₀ ≫ f) H

/-! ### Versality at a finite type point from versality of an approximation -/

/-- **Versality at a finite type point of an affine chart is versality of any approximation
formal object over the ring of the affine open.**

Let `Spec A` be affine of finite type over an affine open `Spec Λ ⊆ S` with `Λ` Noetherian, let
`x` be an object of a category fibred in groupoids over `Spec A`, and let `u₀` be a finite type
point of `Spec A`. Then `x` is versal at `u₀` as soon as *every* formal object `ξ` arising as
the approximation ([Stacks, Tag 07X6]) of a complete local object restricting `x` along a
presentation of `𝒪_{Spec A, u₀}^∧` is versal relative to `Λ` in the sense of
[Stacks, Tag 0CXJ].

The hypothesis `H` is the eliminator form: the proof constructs the complete local object `xR`,
the formal object `ξ`, the presentation `e` of the completed local ring by `ξ.base.R`, the
morphism `g : Spec ξ.base.R ⟶ Spec A` it presents, the Cartesian restriction `r : xR ⟶ x`, and
the `Λ`-algebra structure on `ξ.base.R`, and hands all of it — with every compatibility it
satisfies — to `H`. In particular `hAR` identifies the structure map `Λ ⟶ ξ.base.R` with the
ring map read off `g` precomposed with `Λ ⟶ A`, which is what lets the conditions of
[Stacks, Tag 06IU] be checked on the ring map `A ⟶ ξ.base.R`.

This is the shape in which the direction `(2) ⇒ (1)` of [Stacks, Tag 07YM] consumes
`Deformation.Artin.isVersalAt_iff_isVersal_affineChart`. -/
public theorem isVersalAt_of_forall_approximation
    (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
    [IsNoetherianRing Λ] [Algebra.FiniteType Λ A]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (toS : Spec (CommRingCat.of A) ⟶ S)
    (iΛ : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ = toS)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (x : F) (hx : (p ⋙ Over.post B.inclusion).obj x = Over.mk toS)
    (u₀ : Spec (CommRingCat.of A))
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hC : B.Contains (Spec (CommRingCat.of
      (AlgebraicGeometry.Scheme.completedLocalRing (Spec (CommRingCat.of A)) u₀))))
    (H : ∀ (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
           (ξ : Deformation.Artin.FormalObject B S hS p),
           ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR →
           ∀ (e : AlgebraicGeometry.Scheme.completedLocalRing (Spec (CommRingCat.of A)) u₀
                  ≃+* ξ.base.R)
           (g : Spec (CommRingCat.of ξ.base.R) ⟶ Spec (CommRingCat.of A)),
           g = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
                 Spec.map (CommRingCat.ofHom (algebraMap
                   ((Spec (CommRingCat.of A)).presheaf.stalk u₀)
                   (AlgebraicGeometry.Scheme.completedLocalRing
                     (Spec (CommRingCat.of A)) u₀))) ≫
                 (Spec (CommRingCat.of A)).fromSpecStalk u₀ →
           ξ.base.toS = g ≫ toS →
           ξ.base.toS (IsLocalRing.closedPoint ξ.base.R) =
                 Deformation.Artin.basePoint (Over.mk toS) u₀ →
           ∀ (r : xR.obj.1 ⟶ x), p.IsCartesian (p.map r) r →
           HEq ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
                   p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) g →
           ∀ [Algebra Λ ξ.base.R]
           (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS),
           (algebraMap Λ ξ.base.R) =
                  (Deformation.Artin.ringHom_of_schemeMap g).comp (algebraMap Λ A) →
         Deformation.Artin.FormalObject.IsVersal B S hS p hp ξ Λ iΛ hΛ) :
    Deformation.Artin.IsVersalAt (Over.mk toS) (p ⋙ Over.post B.inclusion) u₀ x hx := by
  -- The geometric hypotheses on the affine chart, from finite type over a Noetherian ring.
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing Λ A
  have hLN : IsLocallyNoetherian (Over.mk toS).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of A)))
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hLFT : LocallyOfFiniteType (Over.mk toS).hom := by
    change LocallyOfFiniteType toS
    rw [← hbase]
    infer_instance
  have hNS : TopologicalSpace.NoetherianSpace (Over.mk toS).left :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (Spec (CommRingCat.of A)))
  have hQC : QuasiCompact (Over.mk toS).hom :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  -- Step 1: a complete local object at `u₀` restricting `x`, over the chosen complete base.
  obtain ⟨xR, r, e₀, hr, hrbase₀, hbase₀⟩ :=
    exists_completeLocalObject_of_isFiniteTypePoint B S hS p hp (Over.mk toS) x hx u₀ hu₀ hC
  -- Step 2: its approximation, a formal object.
  let ξ : Deformation.Artin.FormalObject B S hS p :=
    (Deformation.Artin.approximationFunctor B S hS p hp).obj xR
  have hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR := rfl
  -- Step 3: transport the presentation from the chosen base to the base of the approximation.
  obtain ⟨e, hrbase, hbase', hclosed⟩ := exists_approximationBase_presentation B S hS p hp
    (Over.mk toS) x hx u₀ xR ξ hξ r e₀ hrbase₀ hbase₀
  -- Step 4: the morphism of affine schemes the presentation gives.
  let g : Spec (CommRingCat.of ξ.base.R) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of A)).presheaf.stalk u₀)
        (AlgebraicGeometry.Scheme.completedLocalRing (Spec (CommRingCat.of A)) u₀))) ≫
      (Spec (CommRingCat.of A)).fromSpecStalk u₀
  have hg : g = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of A)).presheaf.stalk u₀)
        (AlgebraicGeometry.Scheme.completedLocalRing (Spec (CommRingCat.of A)) u₀))) ≫
      (Spec (CommRingCat.of A)).fromSpecStalk u₀ := rfl
  have hbase'' : ξ.base.toS = g ≫ toS := hbase'
  -- Step 5: the `Λ`-algebra structure on the base ring, read off `g`.
  let algR : Algebra Λ ξ.base.R :=
    ((Deformation.Artin.ringHom_of_schemeMap g).comp (algebraMap Λ A)).toAlgebra
  have hAR : (algebraMap Λ ξ.base.R) =
      (Deformation.Artin.ringHom_of_schemeMap g).comp (algebraMap Λ A) :=
    RingHom.algebraMap_toAlgebra _
  have hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS := by
    rw [hAR, show CommRingCat.ofHom
        ((Deformation.Artin.ringHom_of_schemeMap g).comp (algebraMap Λ A)) =
        CommRingCat.ofHom (algebraMap Λ A) ≫
          CommRingCat.ofHom (Deformation.Artin.ringHom_of_schemeMap g) from rfl,
      Spec.map_comp, specMap_ringHom_of_schemeMap, Category.assoc, hbase, hbase'']
  -- Step 6: the point of `Spec Λ` under `u₀`, and the `Λ`-structure on its residue field.
  have ht₀ : iΛ (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) u₀) = toS u₀ := by
    rw [← Scheme.Hom.comp_apply, hbase]
  obtain ⟨gκ, hgκ⟩ := exists_ringHom_comp_fromSpecResidueField_of_isOpenImmersion iΛ toS u₀
    (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) u₀) ht₀
  let algκ : Algebra Λ ((Over.mk toS).left.residueField u₀) := gκ.toAlgebra
  have hcompat : Spec.map (CommRingCat.ofHom
      (algebraMap Λ ((Over.mk toS).left.residueField u₀))) ≫ iΛ =
      (Over.mk toS).left.fromSpecResidueField u₀ ≫ (Over.mk toS).hom := by
    rwa [RingHom.algebraMap_toAlgebra]
  have ht : iΛ (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) u₀) =
      Deformation.Artin.basePoint (Over.mk toS) u₀ := by
    rwa [basePoint_eq_hom_apply]
  exact (isVersalAt_iff_isVersal_affineChart B S hS p hp (Over.mk toS) x hx u₀ xR ξ hξ e g hg
    hbase'' r hr hrbase Λ iΛ hΛ _ ht hcompat).mpr
      (H xR ξ hξ e g hg hbase'' hclosed r hr hrbase hΛ hAR)

end Deformation.Artin

end
