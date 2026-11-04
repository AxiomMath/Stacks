module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving

/-!
# Transporting limit preservation

Limit preservation of a presheaf is a property of its values on a category of schemes, so
it is carried along an isomorphism of presheaves and along a change of the indexing
category by an equivalence compatible with the underlying-scheme functors.

## Main results

* `AlgebraicGeometry.limitPreserving_of_natIso` transports limit preservation along an
  isomorphism of presheaves.
* `AlgebraicGeometry.limitPreserving_whiskerEquivalence` transports limit preservation
  along an equivalence of the base categories.

## Implementation notes

Limit preservation only asserts that a comparison cocone is `Nonempty (IsColimit …)`, so
both transports are performed on a chosen colimit structure and the result is repackaged.
The equivalence version takes the compatibility of the two underlying-scheme functors as a
propositional equality, which is how it arises for the iterated slices of a big fppf site.

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w' z z' zC zD

namespace AlgebraicGeometry

/-- Limit preservation transports along an isomorphism of presheaves. -/
public theorem limitPreserving_of_natIso
    {C : Type z} [Category.{z', z} C] {toScheme : C ⥤ Scheme.{u}}
    {P Q : Cᵒᵖ ⥤ Type v} (e : P ≅ Q)
    (hP : LimitPreserving.{u, v, w, w', z, z'} toScheme P) :
    LimitPreserving.{u, v, w, w', z, z'} toScheme Q := by
  intro I instCat instCof D c hc hAffine hAffineLimit
  obtain ⟨hP⟩ := hP I D c hc hAffine hAffineLimit
  let eD : D.op ⋙ P ≅ D.op ⋙ Q := NatIso.ofComponents
    (fun i => e.app (Opposite.op (D.obj i.unop))) (by
      intro i j f
      simp)
  let cP := P.mapCocone c.op
  let cQ := Q.mapCocone c.op
  let E := Cocone.precomposeEquivalence eD
  have hIso : E.functor.obj cP ≅ cQ := Cocone.ext (e.app (Opposite.op c.pt)) (by
    intro i
    show e.inv.app (D.op.obj i) ≫ P.map (c.op.ι.app i) ≫
        e.hom.app c.op.pt = Q.map (c.op.ι.app i)
    rw [← Category.assoc, ← e.inv.naturality (c.op.ι.app i)]
    simp)
  have hMapped : IsColimit (E.functor.obj cP) := by
    refine IsColimit.mk (fun s => hP.desc ((Cocone.precompose eD.hom).obj s)) ?_ ?_
    · intro s i
      show e.inv.app (Opposite.op (D.obj i.unop)) ≫ cP.ι.app i ≫
        hP.desc ((Cocone.precompose eD.hom).obj s) = s.ι.app i
      calc
        _ = e.inv.app (Opposite.op (D.obj i.unop)) ≫
            ((Cocone.precompose eD.hom).obj s).ι.app i := by rw [hP.fac]
        _ = s.ι.app i := by simp [eD, Cocone.precompose]
    · intro s m hm
      let sP := (Cocone.precompose eD.hom).obj s
      exact hP.uniq sP m (by
        intro i
        have hi : e.inv.app (Opposite.op (D.obj i.unop)) ≫ cP.ι.app i ≫ m = s.ι.app i := hm i
        calc
          cP.ι.app i ≫ m =
              e.hom.app (Opposite.op (D.obj i.unop)) ≫
                (e.inv.app (Opposite.op (D.obj i.unop)) ≫ cP.ι.app i ≫ m) := by
                  simp
          _ = e.hom.app (Opposite.op (D.obj i.unop)) ≫ s.ι.app i := by rw [hi]
          _ = sP.ι.app i := by simp [sP, Cocone.precompose, eD])
  exact ⟨hMapped.ofIsoColimit hIso⟩

/-- Limit preservation transports along an equivalence of the base categories whose
underlying-scheme functors agree. -/
public theorem limitPreserving_whiskerEquivalence
    {C : Type z} [Category.{zC, z} C] {D : Type z'} [Category.{zD, z'} D]
    (e : C ≌ D) {toSchemeC : C ⥤ Scheme.{u}} {toSchemeD : D ⥤ Scheme.{u}}
    (hTo : toSchemeC = e.functor ⋙ toSchemeD)
    (F : Dᵒᵖ ⥤ Type v)
    (hF : LimitPreserving.{u, v, w, w', z', zD} toSchemeD F) :
    LimitPreserving.{u, v, w, w', z, zC} toSchemeC (e.functor.op ⋙ F) := by
  intro I instCat instCof D₀ c hc hAffine hAffineLimit
  cases hTo
  exact hF I (D₀ ⋙ e.functor) (e.functor.mapCone c)
    (hc.ofIsoLimit (Functor.mapConeMapCone (H := e.functor) (H' := toSchemeD) c).symm)
    hAffine hAffineLimit

end AlgebraicGeometry
