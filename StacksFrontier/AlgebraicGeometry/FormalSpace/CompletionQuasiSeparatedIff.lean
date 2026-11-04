module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionQuasiCompactIff
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSeparated
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiSeparatedMorphism

/-!
# Quasi-separatedness of a modification and of its completion

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a locally Noetherian algebraic
space over `S`, let `T ⊆ |X|` be a closed subset and let `U ⊂ X` be the open subspace with
`|U| = |X| ∖ T`. **Stacks 0ARV** says that if a morphism `f : X' ⟶ X` of algebraic spaces,
locally of finite type and an isomorphism over `U`, corresponds to `g : W ⟶ X_{/T}` under the
equivalence of Stacks 0ARB, then `f` is quasi-separated if and only if `g` is.

## Main results

* `AlgebraicGeometry.Space.isIso_pullback_snd_diagonal_of_factors`: in any category with fibre
  products, if `f : X' ⟶ X` is an isomorphism over `k : U ⟶ X`, then its relative diagonal is
  an isomorphism over every `j : V ⟶ X' ×_X X'` whose composite to `X` factors through `k`.
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_completionSheafMap_iff`: for every
  morphism `f` of presheaves and every set `T` of points, `f_{/T}` is quasi-separated
  (Stacks 0ARN, part (2)) exactly when the completion `(Δ_f)_{/T''}` of the relative diagonal
  of `f` is quasi-compact (Stacks 0AJC).
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_completionSheafMap_of_isQuasiSeparated`:
  the completion of a quasi-separated morphism of algebraic spaces is quasi-separated in the
  sense of Stacks 0ARN, part (2).
* `AlgebraicGeometry.FormalSpace.isQuasiSeparated_of_hasQuasiCompactDiagonal_completionSheafMap`:
  the converse, for `f` locally of finite type and an isomorphism over `U`, with `X` locally
  Noetherian and `T` closed.
* `AlgebraicGeometry.FormalSpace.isQuasiSeparated_iff_hasQuasiCompactDiagonal_of_overIso`:
  **Stacks 0ARV**.

## Implementation notes

*The notions.* Quasi-separatedness of `f` is Stacks 03HL, part (3),
`AlgebraicGeometry.Space.IsQuasiSeparated`: the relative diagonal is quasi-compact.
Quasi-separatedness of `g` is Stacks 0ARN, part (2),
`AlgebraicGeometry.FormalSpace.HasQuasiCompactDiagonal`: the relative diagonal of `g` is a
quasi-compact morphism of formal algebraic spaces in the sense of Stacks 0AJC.

*The correspondence.* The equivalence of Stacks 0ARB is
`AlgebraicGeometry.FormalSpace.isEquivalence_completionModificationFunctor`, for the functor
`AlgebraicGeometry.FormalSpace.completionModificationFunctor` of Stacks 0AR5 sending `f` to
`f_{/T}`. So `g` corresponds to `f` exactly when `g` is isomorphic over `X_{/T}` to `f_{/T}`,
and every object `g` of the right-hand category corresponds in this way to some `f`. The
statement is made for an arbitrary `g` with such an isomorphism, as is Stacks 0ARU,
`AlgebraicGeometry.FormalSpace.isQuasiCompact_iff_isQuasiCompact_of_overIso`.

*The proof.* By Stacks 0GDF the relative diagonal of `f_{/T}` is, up to isomorphisms on both
sides, the completion `(Δ_f)_{/T''}` of the relative diagonal `Δ_f : X' ⟶ X' ×_X X'` along the
set `T''` of points of `X' ×_X X'` lying over `T`. So the statement is that `Δ_f` is
quasi-compact exactly when `(Δ_f)_{/T''}` is, and this is Stacks 0ARU for `Δ_f` in place of
`f`. The forward direction is Stacks 0GDE in the form of Stacks 0AJC, as in Stacks 0GDG. For
the converse, the converse of Stacks 0ARU applies to `Δ_f` and `T''`: the space `X' ×_X X'` is
locally Noetherian, being locally of finite type over `X`; `T''` is closed; and `Δ_f` is an
isomorphism over the complement of `T''`, because `f` is an isomorphism over `U`. The source
instead checks quasi-compactness of `V_j ×_{X'} V_{j'}` over an affine étale chart of `X`
directly, by the same decomposition into the part over `U` and the part over `T` that the
converse of Stacks 0ARU makes; the reduction to that converse avoids repeating it.

## References

* [Stacks Project, Tag 0ARV](https://stacks.math.columbia.edu/tag/0ARV)
* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0ARU](https://stacks.math.columbia.edu/tag/0ARU)
* [Stacks Project, Tag 0GDF](https://stacks.math.columbia.edu/tag/0GDF)
* [Stacks Project, Tag 0GDG](https://stacks.math.columbia.edu/tag/0GDG)
* [Stacks Project, Tag 0ARN](https://stacks.math.columbia.edu/tag/0ARN)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-! ### The diagonal of a morphism which is an isomorphism over a subobject -/

namespace Space

/-- Let `f : X' ⟶ X` be a morphism in a category with fibre products which is an isomorphism
over `k : U ⟶ X`, that is, `X' ×_X U ⟶ U` is an isomorphism. Then the relative diagonal
`Δ_f : X' ⟶ X' ×_X X'` is an isomorphism over every `j : V ⟶ X' ×_X X'` whose composite to `X`
factors through `k`: the two projections of `j` then lift to the same morphism into
`X' ×_X U`, so `j` factors through the monomorphism `Δ_f`. -/
theorem isIso_pullback_snd_diagonal_of_factors {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X' X U V : C} (f : X' ⟶ X) (k : U ⟶ X) [IsIso (pullback.snd f k)]
    (j : V ⟶ pullback f f) (m : V ⟶ U) (hm : j ≫ pullback.fst f f ≫ f = m ≫ k) :
    IsIso (pullback.snd (pullback.diagonal f) j) := by
  have ha : (j ≫ pullback.fst f f) ≫ f = m ≫ k := by rw [Category.assoc, hm]
  have hb : (j ≫ pullback.snd f f) ≫ f = m ≫ k := by
    rw [Category.assoc, ← pullback.condition, hm]
  have hab : j ≫ pullback.fst f f = j ≫ pullback.snd f f := by
    have hl : pullback.lift _ _ ha = pullback.lift _ _ hb :=
      (cancel_mono (pullback.snd f k)).1 (by rw [pullback.lift_snd, pullback.lift_snd])
    simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst f k) hl
  have hj : (j ≫ pullback.fst f f) ≫ pullback.diagonal f = 𝟙 V ≫ j := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.id_comp, hab]
  have hpb : IsPullback (j ≫ pullback.fst f f) (𝟙 V) (pullback.diagonal f) j :=
    IsPullback.of_vert_isIso_mono ⟨hj⟩
  have h : pullback.snd (pullback.diagonal f) j = hpb.isoPullback.inv := by
    rw [← Iso.hom_comp_eq_id, IsPullback.isoPullback_hom_snd]
  rw [h]
  infer_instance

end Space

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

/-! ### The diagonal of a completed morphism -/

/-- Quasi-compactness of a morphism of fppf sheaves in the sense of Stacks 0AJC is unchanged
by composing with isomorphisms on either side: `e ≫ k ≫ i` is a base change of `k`. -/
theorem IsQuasiCompact.iso_comp_comp {W' W Z Z' : FppfSheaf B S hS} (e : W' ⟶ W) [IsIso e]
    (k : W ⟶ Z) (i : Z ⟶ Z') [IsIso i] (hk : IsQuasiCompact B S hS k) :
    IsQuasiCompact B S hS (e ≫ k ≫ i) :=
  IsQuasiCompact.of_isPullback B S hS
    (IsPullback.of_vert_isIso ⟨by rw [Category.assoc, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]⟩ : IsPullback (e ≫ k ≫ i) e (inv i) k) hk

/-- **The diagonal of a completion.** Let `f : X' ⟶ X` be a morphism of presheaves on the big
fppf site of `S` and `T` a set of points of `X`. The completion `f_{/T}` is quasi-separated in
the sense of Stacks 0ARN, part (2), exactly when the completion `(Δ_f)_{/T''}` of the relative
diagonal of `f` along the set `T''` of points of `X' ×_X X'` over `T` is quasi-compact in the
sense of Stacks 0AJC. By Stacks 0GDF the two morphisms differ by isomorphisms on both sides. -/
theorem hasQuasiCompactDiagonal_completionSheafMap_iff
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) (T : Set (Space.points B S hS X)) :
    HasQuasiCompactDiagonal B S hS (Space.completionSheafMap B S hS f T) ↔
      IsQuasiCompact B S hS (Space.completionSheafMap B S hS (pullback.diagonal f)
        (Space.pullbackPoints B S hS f f T)) := by
  let e := eqToHom (congrArg (Space.completionSheaf B S hS X')
    (Space.pointsMap_diagonal_preimage_pullbackPoints B S hS f T).symm)
  let i := (Space.isPullback_completionSheafPullback B S hS f f T).isoPullback
  let D := Space.completionSheafMap B S hS (pullback.diagonal f)
    (Space.pullbackPoints B S hS f f T)
  have hdiag : pullback.diagonal (Space.completionSheafMap B S hS f T) = e ≫ D ≫ i.hom := by
    rw [Space.pullback_diagonal_completionSheafMap B S hS f T,
      Space.completionSheafDiagonal_eq_completionSheafMap_diagonal, Category.assoc]
  show IsQuasiCompact B S hS (pullback.diagonal (Space.completionSheafMap B S hS f T)) ↔ _
  rw [hdiag]
  refine ⟨fun h ↦ ?_, fun h ↦ IsQuasiCompact.iso_comp_comp B S hS e D i.hom h⟩
  simpa only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
    using IsQuasiCompact.iso_comp_comp B S hS (inv e) (e ≫ D ≫ i.hom) i.inv h

/-! ### The forward direction -/

/-- **The forward direction of Stacks 0ARV.** Let `f : X' ⟶ X` be a quasi-separated morphism of
algebraic spaces over `S` and `T` a set of points of `X`. Then the completion
`f_{/T} : X'_{/T'} ⟶ X_{/T}` is quasi-separated in the sense of Stacks 0ARN, part (2): its
relative diagonal is, by Stacks 0GDF, the completion of the quasi-compact relative diagonal of
`f`, which is quasi-compact in the sense of Stacks 0AJC by Stacks 0GDE. -/
theorem hasQuasiCompactDiagonal_completionSheafMap_of_isQuasiSeparated
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X)) (hf : Space.IsQuasiSeparated B S hS f) :
    HasQuasiCompactDiagonal B S hS (Space.completionSheafMap B S hS f T) :=
  (hasQuasiCompactDiagonal_completionSheafMap_iff B S hS f T).2
    (isQuasiCompact_completionSheafMap_of_isQuasiCompact B S hS hX'
      (isAlgebraicSpace_pullback B S hS f f hX' hX' hX) (pullback.diagonal f) _ hf)

/-! ### The converse -/

/-- If `f : X' ⟶ X` is an isomorphism over the open subspace `U` with point set `Tᶜ`, then its
relative diagonal `Δ_f : X' ⟶ X' ×_X X'` is an isomorphism over the open subspace of
`X' ×_X X'` whose points are those not lying over `T`. -/
theorem isIso_pullback_snd_diagonal_openSubspaceOfPoints
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X)) (f : X' ⟶ X)
    (hU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι)) :
    IsIso (pullback.snd (pullback.diagonal f)
      (Space.openSubspaceOfPoints B S hS (pullback f f)
        (Space.pullbackPoints B S hS f f T)ᶜ).ι) := by
  let UY := Space.openSubspaceOfPoints B S hS (pullback f f) (Space.pullbackPoints B S hS f f T)ᶜ
  let UX := Space.openSubspaceOfPoints B S hS X Tᶜ
  have hrange : Set.range (Space.pointsMap B S hS UY.toFunctor
      (UY.ι ≫ pullback.fst f f ≫ f)) ⊆ Tᶜ := by
    rintro _ ⟨x, rfl⟩
    have hx : Space.pointsMap B S hS UY.toFunctor UY.ι x ∈
        (Space.pullbackPoints B S hS f f T)ᶜ := by
      rw [← Space.range_pointsMap_ι_openSubspaceOfPoints B S hS
        (Space.pullbackPoints B S hS f f T)ᶜ]
      exact ⟨x, rfl⟩
    rw [Space.pointsMap_comp, Function.comp_apply]
    exact hx
  have hle : Subfunctor.range (UY.ι ≫ pullback.fst f f ≫ f) ≤ UX :=
    (Space.range_le_openSubspaceOfPoints_range_pointsMap _).trans
      (Space.openSubspaceOfPoints_mono B S hS hrange)
  exact Space.isIso_pullback_snd_diagonal_of_factors f UX.ι UY.ι
    (Subfunctor.lift _ hle) (Subfunctor.lift_ι _ hle).symm

/-- **The converse of Stacks 0ARV.** Let `X` be a locally Noetherian algebraic space over `S`,
let `T` be a closed set of points of `X` and let `f : X' ⟶ X` be a morphism of algebraic spaces
which is locally of finite type and an isomorphism over the open subspace `U` with point set
`Tᶜ`. If the completion `f_{/T}` is quasi-separated in the sense of Stacks 0ARN, part (2), then
`f` is quasi-separated.

This is the converse of Stacks 0ARU applied to the relative diagonal `Δ_f : X' ⟶ X' ×_X X'` and
the closed set `T''` of points of `X' ×_X X'` over `T`: the space `X' ×_X X'` is locally
Noetherian, being locally of finite type over `X`, `Δ_f` is an isomorphism over the complement
of `T''`, and `(Δ_f)_{/T''}` is quasi-compact by Stacks 0GDF. -/
theorem isQuasiSeparated_of_hasQuasiCompactDiagonal_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hXN : Space.IsLocallyNoetherian B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (f : X' ⟶ X)
    (hfl : Space.IsLocallyOfFiniteType B S hS f)
    (hU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hg : HasQuasiCompactDiagonal B S hS (Space.completionSheafMap B S hS f T)) :
    Space.IsQuasiSeparated B S hS f := by
  have hP : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback B S hS f f hX' hX' hX
  have hX'N : Space.IsLocallyNoetherian B S hS X' :=
    isLocallyNoetherian_of_isLocallyOfFiniteType hX' hX f hfl hXN
  have hPN : Space.IsLocallyNoetherian B S hS (pullback f f) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType hP hX' (pullback.fst f f)
      (Space.IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback f f) hX' hX
        hfl) hX'N
  have hT'' : IsClosed (Space.pullbackPoints B S hS f f T) :=
    hT.preimage (Space.continuous_pointsMap B S hS (pullback.fst f f ≫ f))
  exact isQuasiCompact_of_isQuasiCompact_completionSheafMap B S hS hX' hP hPN
    (Space.pullbackPoints B S hS f f T) hT'' (pullback.diagonal f)
    (isIso_pullback_snd_diagonal_openSubspaceOfPoints B S hS T f hU)
    ((hasQuasiCompactDiagonal_completionSheafMap_iff B S hS f T).1 hg)

/-! ### Stacks 0ARV -/

/-- **Stacks 0ARV.** Let `X` be a locally Noetherian algebraic space over `S`, let `T ⊆ |X|` be
a closed subset and let `U ⊂ X` be the open subspace with `|U| = |X| ∖ T`. Let `f : X' ⟶ X` be
a morphism of algebraic spaces which is locally of finite type and such that `f⁻¹U ⟶ U` is an
isomorphism, and let `g : W ⟶ X_{/T}` correspond to `f` under the equivalence of Stacks 0ARB
(`isEquivalence_completionModificationFunctor`), that is, be isomorphic over `X_{/T}` to the
completion `f_{/T} : X'_{/T'} ⟶ X_{/T}`, the value at `f` of the functor
`completionModificationFunctor` of Stacks 0AR5. Then `f` is quasi-separated (Stacks 03HL,
part (3)) if and only if `g` is quasi-separated (Stacks 0ARN, part (2)). -/
@[stacks 0ARV]
theorem isQuasiSeparated_iff_hasQuasiCompactDiagonal_of_overIso
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXN : Space.IsLocallyNoetherian B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    {W : FppfSheaf B S hS} (g : W ⟶ Space.completionSheaf B S hS X T)
    (e : Over.mk g ≅ Over.mk (Space.completionSheafMap B S hS M.obj.hom T)) :
    Space.IsQuasiSeparated B S hS M.obj.hom ↔ HasQuasiCompactDiagonal B S hS g := by
  have hw : e.hom.left ≫ Space.completionSheafMap B S hS M.obj.hom T = g := Over.w e.hom
  have hw' : e.inv.left ≫ g = Space.completionSheafMap B S hS M.obj.hom T := Over.w e.inv
  have : IsIso e.hom.left := (inferInstance : IsIso ((Over.forget _).mapIso e).hom)
  have : IsIso e.inv.left := (inferInstance : IsIso ((Over.forget _).mapIso e).inv)
  exact ⟨fun hf ↦ HasQuasiCompactDiagonal.of_isPullback B S hS
      (IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, hw]⟩).flip
      (hasQuasiCompactDiagonal_completionSheafMap_of_isQuasiSeparated B S hS
        M.property.source_isAlgebraicSpace hX M.obj.hom T hf),
    fun hg ↦ isQuasiSeparated_of_hasQuasiCompactDiagonal_completionSheafMap B S hS
      M.property.source_isAlgebraicSpace hX hXN T hT M.obj.hom
      M.property.isLocallyOfFiniteType M.property.isIso_pullback_snd
      (HasQuasiCompactDiagonal.of_isPullback B S hS
        (IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, hw']⟩).flip hg)⟩

end FormalSpace

end AlgebraicGeometry

end
