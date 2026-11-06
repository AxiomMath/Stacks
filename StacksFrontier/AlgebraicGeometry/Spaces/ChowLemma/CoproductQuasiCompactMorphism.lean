module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# A morphism out of a finite coproduct of algebraic spaces is quasi-compact

Let a sheaf `P` on the big fppf site over `S` be the coproduct of finitely many algebraic
spaces over `S` with legs `ι i`, and let `f : P ⟶ Y` be a morphism to an algebraic space over
`S`. If every restriction `ι i ≫ f` is quasi-compact in the sense of Stacks 03HE, then so is
`f`.

This is the quasi-compactness half of the finite-type clause of properness for a morphism out
of a coproduct; the locally-of-finite-type half is
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isColimit_cofan`, so the two together give
`AlgebraicGeometry.Space.IsFiniteType` of such a morphism.

The proof is the universality of coproducts of fppf sheaves: a base change of `P` decomposes as
the coproduct of the base changes of the summands
(`AlgebraicGeometry.Space.isColimitCofanMkPullback`), each of which is quasi-compact by
hypothesis, and a finite coproduct of quasi-compact algebraic spaces is quasi-compact by
Stacks 040T.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_isColimit_cofan`: the statement above.
* `AlgebraicGeometry.Space.isFiniteType_of_isColimit_cofan`: the finite-type consequence.

Properness is separatedness, finite type and universal closedness. The finite-type clause is
settled here, the universally-closed clause in
`StacksFrontier/AlgebraicGeometry/Spaces/ChowLemma/CoproductUniversallyClosed.lean` and the
separatedness clause in `StacksFrontier/AlgebraicGeometry/Spaces/ChowLemma/CoproductSeparated.lean`,
where the three are combined into `AlgebraicGeometry.Space.isProper_of_isColimit_cofan`.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 040T](https://stacks.math.columbia.edu/tag/040T)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] AlgebraicGeometry.BigFppfOver.hasSheafify_type

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **A morphism out of a finite coproduct of algebraic spaces over `S` is quasi-compact as
soon as its restrictions to the summands are.** -/
theorem isQuasiCompact_of_isColimit_cofan {I : Type v} [Finite I] [Small.{u} I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, F i ⟶ P) (hP : IsColimit (Cofan.mk P ι))
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i).obj)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : P.obj ⟶ Y)
    (hf : ∀ i, IsQuasiCompact B S hS ((ι i).hom ≫ f)) :
    IsQuasiCompact B S hS f := by
  intro Z hZ hZqc g
  let gs : (⟨Z, hZ.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
    ⟨Y, hY.isSheaf⟩ := ObjectProperty.homMk g
  let fs : P ⟶ (⟨Y, hY.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    ObjectProperty.homMk f
  let t : pullback gs fs ⟶ P := pullback.snd gs fs
  have hsq : IsPullback (pullback.fst gs fs).hom t.hom g f :=
    isPullback_hom_of_sheaf (IsPullback.of_hasPullback gs fs)
  have eA : pullback g f ≅ (pullback gs fs).obj :=
    (IsPullback.of_hasPullback g f).isoIsPullback _ _ hsq
  have hpaste : ∀ i, IsPullback ((pullback.snd (ι i) t).hom ≫ (pullback.fst gs fs).hom)
      (pullback.fst (ι i) t).hom g ((ι i).hom ≫ f) := fun i =>
    (isPullback_hom_of_sheaf (IsPullback.of_hasPullback (ι i) t)).flip.paste_horiz hsq
  have eP : ∀ i, pullback g ((ι i).hom ≫ f) ≅ (pullback (ι i) t).obj := fun i =>
    (IsPullback.of_hasPullback g ((ι i).hom ≫ f)).isoIsPullback _ _ (hpaste i)
  have hialg : ∀ i, IsAlgebraicSpace B S hS (pullback (ι i) t).obj := fun i =>
    (isAlgebraicSpace_pullback B S hS g ((ι i).hom ≫ f) hZ (hF i) hY).of_iso (eP i)
  have hqci : ∀ i, IsQuasiCompactSpace B S hS (pullback (ι i) t).obj := fun i =>
    IsQuasiCompactSpace.of_iso B S hS (hf i Z hZ hZqc g) (eP i)
  have hcofan : IsColimit (Cofan.mk (pullback gs fs) fun i ↦ pullback.snd (ι i) t) :=
    isColimitCofanMkPullback B S hS ι hP t
  exact IsQuasiCompactSpace.of_iso B S hS
    (isQuasiCompactSpace_finiteCoproduct B S hS (fun i ↦ (pullback (ι i) t).obj) hialg hqci
      (pullback gs fs) (fun i ↦ pullback.snd (ι i) t) hcofan) eA.symm

/-- **A morphism out of a finite coproduct of algebraic spaces over `S` is of finite type as
soon as its restrictions to the summands are.** The locally-of-finite-type clause is
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isColimit_cofan` and the quasi-compactness
clause is `AlgebraicGeometry.Space.isQuasiCompact_of_isColimit_cofan`. -/
theorem isFiniteType_of_isColimit_cofan {I : Type v} [Finite I] [Small.{u} I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, F i ⟶ P) (hP : IsColimit (Cofan.mk P ι))
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i).obj)
    (hPalg : IsAlgebraicSpace B S hS P.obj)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : P.obj ⟶ Y)
    (hf : ∀ i, IsFiniteType B S hS ((ι i).hom ≫ f)) :
    IsFiniteType B S hS f :=
  ⟨isLocallyOfFiniteType_of_isColimit_cofan B S hS ι hP hF hPalg hY f fun i ↦ (hf i).1,
    isQuasiCompact_of_isColimit_cofan B S hS ι hP hF hY f fun i ↦ (hf i).2⟩

end AlgebraicGeometry.Space

end
