module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlasRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProductRefined
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas

/-!
# Charted relative products from a diagonal representable by algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `Z` be an fppf sheaf on the big
fppf site of `S` whose diagonal `Z ⟶ Z ⨯ Z` is representable **by algebraic spaces** — the
hypothesis **Stacks 0AJ2** places on the base of its fibre product. This file concludes that `Z`
has *charted* relative products, `AlgebraicGeometry.FormalSpace.HasChartedRelativeProducts`, and
hence that the set-theoretic condition of **Stacks 0AIS** holds for a fibre product over `Z`.

## What this settles, and what it does not

`Z` does **not** have representable relative products,
`AlgebraicGeometry.FormalSpace.HasRepresentableRelativeProducts`: the relative product
`h_a ×_Z h_b` of two scheme-valued points of `Z` is an algebraic space, and an algebraic space
is not in general a scheme, let alone an object of the chosen site. That predicate is strictly
stronger than what its consumer uses. Its only consumer,
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_pullback'`, is now stated at the
weaker hypothesis, and the weaker hypothesis is what is proved here.

So this closes the set-theoretic half of Stacks 0AJ2. It does **not** close Stacks 0AJ2, whose
remaining inputs are Stacks 05ZH for thickenings of algebraic spaces at arbitrary order and
Stacks 07VT.

## Main results

* `FormalSpace.hasChartedRelativeProducts_of_isRepresentableByAlgebraicSpacesULift_diag`:
  a sheaf whose diagonal is representable by algebraic spaces has charted relative products.
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_pullback_of_representableDiagonal`:
  the set-theoretic condition of **Stacks 0AIS** for a fibre product over such a sheaf.

## Implementation notes

The relative product is an algebraic space by **Stacks 03XY**: `h_a ×_Z h_b` is the base change
of `Δ_Z` along `h_a ⨯ h_b ⟶ Z ⨯ Z` (`CategoryTheory.Limits.isPullback_diag_prodMap`), and
`h_a ⨯ h_b` is the representable presheaf of the product `a ⨯ b` of the site, hence an algebraic
space, so `AlgebraicGeometry.Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift`
applies. The site's binary products come from its terminal object and its fibre products, and
the universe-lifted Yoneda embedding preserves them.

An algebraic space is then charted by an object of the site in both of the two senses the
predicate asks for. Its étale scheme atlas is an object of the site and is a surjection of
sheaves, `AlgebraicGeometry.FormalSpace.exists_epi_uliftYoneda_of_isAlgebraicSpaceULift`; and
its diagonal is representable by objects of the site, so every morphism to it out of a
representable is relatively representable, which is
`CategoryTheory.Functor.relativelyRepresentable.of_diag`. The latter is stated for presheaves,
where the algebraic-space condition lives, and
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_uliftYoneda_iff` together with
`AlgebraicGeometry.FormalSpace.relative_of_natIso` carries it to the sheaf-valued sheafified
Yoneda embedding in which this development states representability by objects of the site.

NO TAG IS ATTACHED. Stacks 0AJ2 is the formal-algebraic-space statement about the fibre product
itself, and that statement is not proved here; what is proved is one of its three inputs.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 02YQ](https://stacks.math.columbia.edu/tag/02YQ)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fibre product of two scheme-valued points of an fppf sheaf whose diagonal is representable
by algebraic spaces is an algebraic space (Stacks 03XY applied to the diagonal). -/
private theorem isAlgebraicSpaceULift_pullback_of_isRepresentableByAlgebraicSpacesULift_diag
    {Z : FppfSheaf B S hS}
    (hZ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (diag Z.obj))
    {a b : BigFppfOver B S hS}
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj a ⟶ Z)
    (h : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj b ⟶ Z) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback g h).obj := by
  classical
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let J := BigFppfOver.topology B S hS
  let K := sheafToPresheaf J (Type (u + 1))
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let gl : Sheaf.sheafifiedYoneda J ⋙ K ≅ uliftYoneda.{u + 1} := sheafifiedYonedaPresheafIso B S hS
  let ξa : uliftYoneda.{u + 1}.obj a ⟶ Z.obj := gl.inv.app a ≫ K.map g
  let ξb : uliftYoneda.{u + 1}.obj b ⟶ Z.obj := gl.inv.app b ≫ K.map h
  have hprod : Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (uliftYoneda.{u + 1}.obj a ⨯ uliftYoneda.{u + 1}.obj b) :=
    Space.isAlgebraicSpaceULift_of_iso B S hS
      (PreservesLimitPair.iso uliftYoneda.{u + 1} a b)
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (a ⨯ b))
  have hdsq : IsPullback (pullback.fst ξa ξb ≫ ξa)
      (prod.lift (pullback.fst ξa ξb) (pullback.snd ξa ξb)) (diag Z.obj)
      (prod.map ξa ξb) :=
    Stacks.Spaces.isPullback_diag_prodMap (IsPullback.of_hasPullback ξa ξb)
  have halg1 : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξa ξb) :=
    Space.isAlgebraicSpaceULift_of_iso B S hS hdsq.flip.isoPullback.symm
      (Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS
        (diag Z.obj) (prod.map ξa ξb) hZ hprod)
  have hc : ∀ {c} (k : (Sheaf.sheafifiedYoneda J).obj c ⟶ Z),
      gl.hom.app c ≫ gl.inv.app c ≫ K.map k = K.map k := fun k => gl.hom_inv_id_app_assoc _ _
  have hKsq : IsPullback (K.map (pullback.fst g h) ≫ gl.hom.app a)
      (K.map (pullback.snd g h) ≫ gl.hom.app b) ξa ξb :=
    ((IsPullback.of_hasPullback g h).map K).of_iso (Iso.refl _) (gl.app a) (gl.app b)
      (Iso.refl _) (by simp) (by simp)
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.app_hom]; exact (hc g).symm)
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.app_hom]; exact (hc h).symm)
  exact Space.isAlgebraicSpaceULift_of_iso B S hS hKsq.isoPullback.symm halg1

/-- **An fppf sheaf whose diagonal is representable by algebraic spaces has charted relative
products.** This is the hypothesis **Stacks 0AJ2** places on the base of its fibre product, and
`AlgebraicGeometry.FormalSpace.HasChartedRelativeProducts` is what the set-theoretic condition
of **Stacks 0AIS** needs of that base.

The relative product of two scheme-valued points of `Z` is a base change of `Δ_Z` along a
morphism out of the representable presheaf of a product of the site, hence an algebraic space
over `S` by Stacks 03XY. Its étale scheme atlas is an object of the site surjecting onto it, and
its representable diagonal makes that atlas relatively representable; those are exactly the two
clauses of the conclusion. -/
theorem hasChartedRelativeProducts_of_isRepresentableByAlgebraicSpacesULift_diag
    {Z : FppfSheaf B S hS}
    (hZ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (diag Z.obj)) :
    HasChartedRelativeProducts B S hS Z := by
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let K := sheafToPresheaf J (Type (u + 1))
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let gl : F ⋙ K ≅ uliftYoneda.{u + 1} := sheafifiedYonedaPresheafIso B S hS
  intro a b g h
  have halg := isAlgebraicSpaceULift_pullback_of_isRepresentableByAlgebraicSpacesULift_diag
    B S hS hZ g h
  obtain ⟨c, α, hα⟩ := exists_epi_uliftYoneda_of_isAlgebraicSpaceULift B S hS (pullback g h) halg
  let ee : J.uliftYoneda.{u + 1} ≅ F := Sheaf.uliftYonedaIsoSheafifiedYoneda J
  refine ⟨c, (ee.app c).inv ≫ α, inferInstance, ?_⟩
  have hφ : uliftYoneda.{u + 1}.relativelyRepresentable
      (gl.inv.app c ≫ K.map ((ee.app c).inv ≫ α)) :=
    Functor.relativelyRepresentable.of_diag halg.diagonal_representable _
  have hKe : uliftYoneda.{u + 1}.relativelyRepresentable (K.map ((ee.app c).inv ≫ α)) := by
    simpa using MorphismProperty.RespectsIso.precomp
      (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable
      (gl.hom.app c) _ hφ
  exact (relative_of_natIso ee ⊤ ((ee.app c).inv ≫ α)
    ⟨(relativelyRepresentable_uliftYoneda_iff B S hS _).mpr hKe, fun _ _ _ _ _ _ => trivial⟩).rep

/-- **The set-theoretic condition of Stacks 0AIS holds for the fibre product of two fppf sheaves
which satisfy it and have representable relative products, over an fppf sheaf whose diagonal is
representable by algebraic spaces.**

This is the set-theoretic half of **Stacks 0AJ2**, at the hypothesis Stacks 0AJ2 places on its
base. It is not Stacks 0AJ2: the conclusion there is that the fibre product is a formal
algebraic space, which needs in addition a directed presentation by affine schemes along
thickenings. -/
theorem satisfiesSetTheoreticCondition_pullback_of_representableDiagonal
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (diag Z.obj))
    (hXset : SatisfiesSetTheoreticCondition B S hS X)
    (hXrep : HasRepresentableRelativeProducts B S hS X)
    (hYset : SatisfiesSetTheoreticCondition B S hS Y)
    (hYrep : HasRepresentableRelativeProducts B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS (pullback p q) :=
  satisfiesSetTheoreticCondition_pullback_of_hasChartedRelativeProducts B S hS p q
    (hasChartedRelativeProducts_of_isRepresentableByAlgebraicSpacesULift_diag B S hS hZ)
    hXset hXrep hYset hYrep

end AlgebraicGeometry.FormalSpace

end
