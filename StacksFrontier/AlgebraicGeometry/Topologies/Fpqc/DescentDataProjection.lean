module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridge

/-!
# Effectivity delivers a descended scheme together with an invariant projection to it

`AlgebraicGeometry.DescentData.exists_descent_of_isEffective` takes a morphism `b` out of the
scheme of a descent datum as *input*, together with the invariance of `b` for the action, and
returns the descended scheme. For the applications which want to *measure* a descent datum
against the scheme it would descend to, the useful morphism is the projection to that scheme
itself, which cannot be supplied in advance because the scheme is produced by the theorem.

This file records that stronger form: effectivity produces the descended scheme `W₀`, the
comparison isomorphism `α₀ : X ×_S W₀ ≅ V`, and the invariance for the action of the
*projection* `α₀⁻¹ ≫ pr_{W₀}`. No hypothesis is required; the invariance that
`AlgebraicGeometry.DescentData.exists_descent_of_isEffective` asks of `b` is, for this
particular morphism, a theorem.

## Main results

* `AlgebraicGeometry.DescentData.exists_descent_proj_of_isEffective`: **an effective descent
  datum is the canonical one on a base change, compatibly with the projection to the descended
  scheme.**

## Implementation notes

The ingredients are the same as those of
`AlgebraicGeometry.DescentData.exists_descent_of_isEffective`:
`AlgebraicGeometry.DescentData.exists_iso_canonical_over`, which supplies the comparison
isomorphism of the canonical datum of `W` along with the invariance of its projection to `W`,
and `AlgebraicGeometry.DescentDatum.hom_comm_iff`, which says that the isomorphism of descent
data witnessing effectivity is equivariant. What is new is only the bookkeeping identifying
`α₀⁻¹ ≫ pr_{W₀}` with the projection of the canonical datum transported along that
isomorphism: the symmetry of the fibre product exchanges `pr_{W₀}` for
`CategoryTheory.Limits.pullback.fst`, which is the leg
`AlgebraicGeometry.DescentData.exists_iso_canonical_over` speaks about.

## References

* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.DescentData

variable {S X : Scheme.{u}} {g : X ⟶ S}

/-- **An effective descent datum relative to `g : X ⟶ S` is the canonical datum of a base
change, compatibly with the projection to the descended scheme.** There are a scheme `W₀`, a
morphism `w₀ : W₀ ⟶ S` and an isomorphism `α₀ : X ×_S W₀ ≅ V` over `X` whose inverse followed
by the projection to `W₀` is invariant for the action of the datum on generalized points.

Unlike `AlgebraicGeometry.DescentData.exists_descent_of_isEffective`, no invariant morphism out
of `V` is required as input: the projection to the descended scheme is one. -/
theorem exists_descent_proj_of_isEffective (D : DescentDatum g)
    (hEff : DescentData.IsEffective D) :
    ∃ (W₀ : Scheme.{u}) (w₀ : W₀ ⟶ S) (α₀ : pullback g w₀ ≅ D.over.left),
      α₀.hom ≫ D.over.hom = pullback.fst g w₀ ∧
      ∀ {Z : Over S} (v : Z ⟶ (Over.map g).obj D.over) (x : Z ⟶ Over.mk g),
        (D.act v x).left ≫ α₀.inv ≫ pullback.snd g w₀ =
          v.left ≫ α₀.inv ≫ pullback.snd g w₀ := by
  obtain ⟨W, ⟨ε⟩⟩ := hEff
  obtain ⟨ι, hπ⟩ := exists_iso_canonical_over g W
  -- `h` is the isomorphism of `X`-schemes underlying the witness of effectivity.
  set h := (DescentDatum.forget g).mapIso ε with hh
  have hεw : h.hom.left ≫ D.over.hom =
      (DescentDatum.over ((canonicalFunctor g).obj W)).hom := Over.w h.hom
  have hιw : ι.inv.left ≫ (DescentDatum.over ((canonicalFunctor g).obj W)).hom =
      pullback.snd W.hom g := Over.w ι.inv
  refine ⟨W.left, W.hom, pullbackSymmetry g W.hom ≪≫ ((Over.forget X).mapIso ι).symm ≪≫
    (Over.forget X).mapIso h, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Over.forget_map, Category.assoc]
    rw [hεw, hιw, pullbackSymmetry_hom_comp_snd]
  · intro Z v x
    have hequiv : ∀ {Z : Over S}
        (v : Z ⟶ (Over.map g).obj (DescentDatum.over ((canonicalFunctor g).obj W)))
        (x : Z ⟶ Over.mk g),
        DescentDatum.act ((canonicalFunctor g).obj W) v x ≫ (Over.map g).map h.hom =
          D.act (v ≫ (Over.map g).map h.hom) x :=
      (DescentDatum.hom_comm_iff ((canonicalFunctor g).obj W) D h.hom).mp (ε.hom.comm () ())
    have hhominv : h.hom.left ≫ h.inv.left = 𝟙 _ := by
      rw [← Over.comp_left, h.hom_inv_id]; rfl
    -- The point of the canonical datum corresponding to `v`.
    set v' : Z ⟶ (Over.map g).obj (DescentDatum.over ((canonicalFunctor g).obj W)) :=
      v ≫ (Over.map g).map h.inv with hv'
    have hback : v' ≫ (Over.map g).map h.hom = v := by
      rw [hv', Category.assoc, ← Functor.map_comp, h.inv_hom_id]
      simp
    have hact : (DescentDatum.act ((canonicalFunctor g).obj W) v' x).left ≫ h.hom.left =
        (D.act v x).left := by
      have := congrArg (fun t => Over.Hom.left t) (hequiv v' x)
      simp only [Over.comp_left, Over.map_map_left] at this
      rw [this, hback]
    have hproj : (D.act v x).left ≫ h.inv.left ≫ ι.hom.left ≫ pullback.fst W.hom g =
        v.left ≫ h.inv.left ≫ ι.hom.left ≫ pullback.fst W.hom g := by
      have hv'l : v'.left = v.left ≫ h.inv.left := by
        rw [hv', Over.comp_left, Over.map_map_left]
      rw [← hact, Category.assoc, ← Category.assoc h.hom.left, hhominv, Category.id_comp,
        hπ v' x, hv'l]
      simp only [Category.assoc]
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Over.forget_map, Category.assoc, pullbackSymmetry_inv_comp_snd]
    simpa only [Category.assoc] using hproj

end AlgebraicGeometry.DescentData

end
