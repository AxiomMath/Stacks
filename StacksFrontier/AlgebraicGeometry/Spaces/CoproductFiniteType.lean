module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# Local finite type of a morphism out of a coproduct

Being locally of finite type is local on the source of a morphism of algebraic spaces over a
scheme `S`: if the source is covered by open subspaces on which the morphism is locally of
finite type, then so is the morphism. Applied to the pieces of a coproduct — which are open
subspaces jointly covering it — this says that a morphism out of a coproduct is locally of
finite type as soon as its restriction to each summand is.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isZariskiCover`: local finite type is
  Zariski local on the source.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isColimit_cofan`: a morphism out of a
  coproduct of sheaves which are algebraic spaces over `S`.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isColimit_cofan_over`: the same for a
  countable coproduct in the slice of the algebraic spaces over a fixed one.

## Implementation notes

Locality on the source is read off the pointwise criterion
`AlgebraicGeometry.Space.IsFiniteTypeAt`: a Zariski covering of the source by open subspaces
covers its points by `AlgebraicGeometry.Space.isZariskiCover_iff_iUnion_points`, and a member
containing a given point is exactly the open neighbourhood that the pointwise criterion asks
for. No locality statement for the fppf or étale topology is needed.

For a coproduct the covering is the family of ranges of the legs, which are open subspaces by
`AlgebraicGeometry.Space.isOpenSubspace_range_cofan_inj` and jointly locally surjective by
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_of_range_le`. A leg is a monomorphism, so
it is an isomorphism onto its range, and that isomorphism — which is étale by
`AlgebraicGeometry.Space.isEtale_of_isIso`, hence locally of finite type — is what transfers
the hypothesis on the leg to the inclusion of the range.

In the slice over an algebraic space the coproduct is computed on underlying sheaves — the
inclusion of the algebraic spaces into the sheaves and the forgetful functor of the slice both
create countable coproducts — so the slice statement follows from the sheaf statement by
transporting the colimit cofan along their composite.

## References

* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Being locally of finite type is Zariski local on the source.** If the source of a
morphism of algebraic spaces over `S` carries a Zariski covering by open subspaces on each of
which the morphism restricts to one which is locally of finite type, then the morphism is
locally of finite type.

This is conditions (9) and (2) of Stacks 040Y in the special case of a one-member covering of
the target: a point of the source lies in some member of the covering, which is then the open
neighbourhood required by `AlgebraicGeometry.Space.IsFiniteTypeAt`. -/
theorem isLocallyOfFiniteType_of_isZariskiCover
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type u} {W : I → Subfunctor X} (hW : IsZariskiCover B S hS I W)
    (hf : ∀ i, IsLocallyOfFiniteType B S hS ((W i).ι ≫ f)) :
    IsLocallyOfFiniteType B S hS f := by
  refine isLocallyOfFiniteType_of_isFiniteTypeAt B S hS hX hY f fun x ↦ ?_
  have hx : x ∈ ⋃ i, Set.range (pointsMap B S hS (W i).toFunctor (W i).ι) := by
    rw [(isZariskiCover_iff_iUnion_points B S hS X hX I W hW.1).mp hW]
    exact Set.mem_univ x
  obtain ⟨i, x', hx'⟩ := Set.mem_iUnion.mp hx
  exact ⟨W i, hW.1 i, x', hx', hf i⟩

/-- **A morphism out of a coproduct is locally of finite type as soon as its restrictions
are.** Let a sheaf `P` on the big fppf site over `S` be the coproduct of a family of algebraic
spaces over `S` with legs `ι i`, and let `f` be a morphism from `P` to an algebraic space over
`S`. If each `ι i ≫ f` is locally of finite type then so is `f`. -/
theorem isLocallyOfFiniteType_of_isColimit_cofan {I : Type v} [Small.{u} I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, F i ⟶ P) (hP : IsColimit (Cofan.mk P ι))
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i).obj)
    (hPalg : IsAlgebraicSpace B S hS P.obj)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : P.obj ⟶ Y)
    (hf : ∀ i, IsLocallyOfFiniteType B S hS ((ι i).hom ≫ f)) :
    IsLocallyOfFiniteType B S hS f := by
  classical
  -- Reindex by a type of the working universe, which is where Zariski coverings are indexed.
  let e : Shrink.{u} I ≃ I := (equivShrink I).symm
  let ι' : ∀ j : Shrink.{u} I, F (e j) ⟶ P := fun j ↦ ι (e j)
  have hP' : IsColimit (Cofan.mk P ι') :=
    (Cofan.isColimitEquivOfEquiv e (Cofan.mk P ι)) hP
  let W : Shrink.{u} I → Subfunctor P.obj := fun j ↦ Subfunctor.range (ι' j).hom
  have hWopen (j) : IsOpenSubspace B S hS (W j) :=
    isOpenSubspace_range_cofan_inj ι' hP' j (hF (e j))
  refine isLocallyOfFiniteType_of_isZariskiCover B S hS hPalg hY f
    (W := W) ⟨hWopen, CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_of_range_le _ ι' hP'
      (fun j ↦ (W j).ι) fun j ↦ by rw [Subfunctor.range_ι]⟩ fun j ↦ ?_
  -- A leg is a monomorphism, hence an isomorphism onto its range.
  have hmono : Mono (ι' j).hom := AlgebraicGeometry.Sheaf.mono_hom_cofan_inj ι' hP' j
  let d : (F (e j)).obj ⟶ (W j).toFunctor := Subfunctor.toRange (ι' j).hom
  have hinv : CategoryTheory.inv d ≫ (ι' j).hom = (W j).ι :=
    (IsIso.inv_comp_eq d).mpr (Subfunctor.toRange_ι (ι' j).hom).symm
  have hcomp := isLocallyOfFiniteType_comp B S hS (hWopen j).1 (hF (e j)) hY
    (CategoryTheory.inv d) ((ι' j).hom ≫ f)
    (isLocallyOfFiniteType_of_isEtale B S hS (hF (e j))
      (isEtale_of_isIso B S hS (CategoryTheory.inv d))) (hf (e j))
  rwa [← Category.assoc, hinv] at hcomp

/-- **A morphism out of a countable coproduct of algebraic spaces over a fixed one is locally
of finite type as soon as its restrictions are.** The coproduct in the slice is computed on
underlying sheaves, so this is
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isColimit_cofan`. -/
theorem isLocallyOfFiniteType_of_isColimit_cofan_over {I : Type v} [Small.{u} I] [Countable I]
    {Z : AlgebraicSpaces B S hS} {F : I → Over Z} {Q Y : Over Z} (ι : ∀ i, F i ⟶ Q)
    (hQ : IsColimit (Cofan.mk Q ι)) (f : Q ⟶ Y)
    (hf : ∀ i, IsLocallyOfFiniteType B S hS (ι i ≫ f).left.hom) :
    IsLocallyOfFiniteType B S hS f.left.hom := by
  let G : Over Z ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    Over.forget Z ⋙ algebraicSpacesToSheaf B S hS
  exact isLocallyOfFiniteType_of_isColimit_cofan B S hS _
    (isColimitCofanMkObjOfIsColimit G _ ι hQ)
    (fun i ↦ (F i).left.property) Q.left.property Y.left.property f.left.hom hf

end AlgebraicGeometry.Space

end
