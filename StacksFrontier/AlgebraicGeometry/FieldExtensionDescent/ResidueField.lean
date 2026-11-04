module

public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.FiniteDegree

/-!
# Descent of ampleness along a base change by an algebra of finite type

Let `k` be a field, `A` a nonzero `k`-algebra of finite type and `X` a scheme over `k`. If
`Spec A ×_{Spec k} X` carries an ample invertible sheaf, then so does `X`: for a maximal ideal `m`
of `A` the residue field `A ⧸ m` is finite over `k` by the Hilbert Nullstellensatz, the ample sheaf
pulls back to `Spec (A ⧸ m) ×_{Spec k} X`, and ampleness descends along the finite base change
(`AlgebraicGeometry.exists_isAmple_of_finite_base_change`). These are the last two sentences of the
proof of [Stacks Project, Tag 0BDC].

## Main results

* `AlgebraicGeometry.exists_isAffineHom_pullback_of_comp`: base-changing along a composite
  `T' → T → S` factors through the base change along `T → S` by an affine morphism, when `T' → T`
  is affine.
* `AlgebraicGeometry.exists_isAmple_of_finiteType_base_change`: if `Spec A ×_{Spec k} X` carries an
  ample invertible sheaf for some nonzero `k`-algebra `A` of finite type, then so does `X`.

## References

* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
* [Stacks Project, Tag 01PU](https://stacks.math.columbia.edu/tag/01PU)
* [Stacks Project, Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)
* [Stacks Project, Tag 0BD4](https://stacks.math.columbia.edu/tag/0BD4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Base-changing a scheme along a composite `T' ⟶ T ⟶ S` factors through its base change along
`T ⟶ S`, by an affine morphism as soon as `T' ⟶ T` is affine. -/
public theorem exists_isAffineHom_pullback_of_comp {S T T' X : Scheme.{u}} (p : T' ⟶ T)
    (g : T ⟶ S) [IsAffineHom p] (f : X ⟶ S) :
    ∃ r : pullback (p ≫ g) f ⟶ pullback g f, IsAffineHom r := by
  have hsnd : IsAffineHom (pullback.snd p (pullback.fst g f)) :=
    let : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) (pullback.fst g f) :=
      ⟨fun sq H => isAffineHom_isStableUnderBaseChange.of_isPullback sq H⟩
    MorphismProperty.pullback_snd _ _ inferInstance
  exact ⟨(pullbackRightPullbackFstIso g f p).inv ≫ pullback.snd p (pullback.fst g f),
    inferInstance⟩

/-- If the base change of a scheme over a field `k` along the spectrum of a nonzero `k`-algebra `A`
of finite type carries an ample invertible sheaf, then so does the scheme itself. -/
public theorem exists_isAmple_of_finiteType_base_change (k A : Type u) [Field k] [CommRing A]
    [Nontrivial A] [Algebra k A] [Algebra.FiniteType k A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    (h : ∃ L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f).Modules,
        ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
          (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f).toRingedSpace.presheaf
          (structureSheafRing
            (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f).toRingedSpace).property L,
          Scheme.Modules.IsAmple
            (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f) L) :
    ∃ M : X.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M,
      Scheme.Modules.IsAmple X M := by
  obtain ⟨L, hL, hamp⟩ := h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  have hfin : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ m))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ m))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨r, hr⟩ := exists_isAffineHom_pullback_of_comp
    (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ m))))
    (Spec.map (CommRingCat.ofHom (algebraMap k A))) f
  obtain ⟨r', hr'⟩ : ∃ r' : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ m)))) f :
      Scheme.{u}) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f,
      IsAffineHom r' := ⟨(pullback.congrHom hspec rfl).hom ≫ r, inferInstance⟩
  have hcomp : CompactSpace
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f : Scheme.{u}) :=
    hamp.compactSpace
  have hcomp' : CompactSpace
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ m)))) f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace r'
  exact exists_isAmple_of_finite_base_change k (A ⧸ m) f
    ⟨_, Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback r'.toLRSHom.toShHom L,
      Scheme.Modules.isAmple_pullback_of_isAffineHom r' L hamp⟩

end AlgebraicGeometry

end
