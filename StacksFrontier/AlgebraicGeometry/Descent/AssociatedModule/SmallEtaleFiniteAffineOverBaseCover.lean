module

public import StacksFrontier.AlgebraicGeometry.AffineExtend.Induction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineOverBaseCechTerms

/-!
# A finite covering family of the final object of `X_étale` with affine Čech terms

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site, with `X` quasi-compact. This file
constructs a covering family of the final object of the small étale site of `X` with a finite
index type in `Type u`, whose members and all their iterated fibre products over `X` are affine
over `Y` when `Y` and `a` are separated.

For a scheme `S` the family is a `Finset` `s` of affine opens of `S`, as objects of `S_étale`
through `AlgebraicGeometry.SmallEtale.opensToSmallEtale`, indexed by the subtype
`{V : S.affineOpens // V ∈ s}`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.finsetAffineOpensHypercoverFinal`: a `Finset` of affine opens of
  `S` as a `CategoryTheory.PreZeroHypercover.{u}` of the final object of `S_étale`, with `Finite`
  index type.

## Main results

* `AlgebraicGeometry.SmallEtale.coversTop_finsetAffineOpensHypercoverFinal`: it covers the final
  object as soon as the `Finset` covers `S`.
* `AlgebraicGeometry.SmallEtale.exists_finite_coversTop_isAffine_of_compactSpace`: a finite
  covering family of the final object of `S_étale` with affine members, for a quasi-compact `S`.
* `exists_finite_coversTop_isAffineHom_piObj_of_compactSpace_of_isSeparated_of_isSeparatedHom`:
  a finite covering family of the final object of `X_étale` whose members and all their iterated
  fibre products over `X` are affine over `Y`, for `X` quasi-compact, `Y` separated and `a`
  separated.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01SG](https://stacks.math.columbia.edu/tag/01SG)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

section Family

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : Finset S.affineOpens)

/-- The family of objects of `S_étale` over its final object given by the affine opens of `S`
lying in the `Finset` `s`, indexed by the subtype `{V : S.affineOpens // V ∈ s}`. It is
`AlgebraicGeometry.SmallEtale.affineOpensHypercoverFinal` restricted to `s`. -/
public def finsetAffineOpensHypercoverFinal : PreZeroHypercover.{u} (final B S hS) where
  I₀ := {V : S.affineOpens // V ∈ s}
  X V := (opensToSmallEtale B S hS).obj (V.1 : S.Opens)
  f _ := (finalIsTerminal B S hS).from _

/-- The member of `finsetAffineOpensHypercoverFinal B S hS s` at `V` is the image of the open `V`
under `AlgebraicGeometry.SmallEtale.opensToSmallEtale`. -/
@[simp]
public theorem finsetAffineOpensHypercoverFinal_X (V : {V : S.affineOpens // V ∈ s}) :
    (finsetAffineOpensHypercoverFinal B S hS s).X V =
      (opensToSmallEtale B S hS).obj (V.1 : S.Opens) :=
  rfl

/-- The index type of `AlgebraicGeometry.SmallEtale.finsetAffineOpensHypercoverFinal` is finite. -/
public instance finite_finsetAffineOpensHypercoverFinal :
    Finite (finsetAffineOpensHypercoverFinal B S hS s).I₀ :=
  inferInstanceAs (Finite {V : S.affineOpens // V ∈ s})

/-- The underlying scheme of a member of
`AlgebraicGeometry.SmallEtale.finsetAffineOpensHypercoverFinal` is affine. -/
public instance isAffine_toScheme_finsetAffineOpensHypercoverFinal
    (V : {V : S.affineOpens // V ∈ s}) :
    AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((finsetAffineOpensHypercoverFinal B S hS s).X V)) :=
  V.1.2

/-- If the affine opens in `s` cover `S`, then
`AlgebraicGeometry.SmallEtale.finsetAffineOpensHypercoverFinal B S hS s` covers the final object
of `S_étale`. -/
public theorem coversTop_finsetAffineOpensHypercoverFinal
    (hs : (⨆ V ∈ s, (V : S.Opens)) = ⊤) :
    (topology B S hS).CoversTop (finsetAffineOpensHypercoverFinal B S hS s).X := by
  refine coversTop_opensToSmallEtale B S hS
    (fun V : {V : S.affineOpens // V ∈ s} ↦ (V.1 : S.Opens))
    ((Opens.coversTop_iff ↥S _).2 (le_antisymm le_top ?_))
  rw [← hs]
  exact iSup₂_le fun V hV ↦
    le_iSup (fun W : {V : S.affineOpens // V ∈ s} ↦ (W.1 : S.Opens)) ⟨V, hV⟩

end Family

section Compact

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a quasi-compact `S`, the final object of `S_étale` has a covering family with finite
index type whose members have affine underlying schemes. -/
public theorem exists_finite_coversTop_isAffine_of_compactSpace [CompactSpace ↥S] :
    ∃ E : PreZeroHypercover.{u} (final B S hS), Finite E.I₀ ∧
      (topology B S hS).CoversTop E.X ∧
      ∀ j, AlgebraicGeometry.IsAffine ((toScheme B S hS).obj (E.X j)) := by
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top (X := S)
  exact ⟨finsetAffineOpensHypercoverFinal B S hS s, inferInstance,
    coversTop_finsetAffineOpensHypercoverFinal B S hS s hs,
    fun j ↦ isAffine_toScheme_finsetAffineOpensHypercoverFinal B S hS s j⟩

end Compact

section Base

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- For a quasi-compact `X`, a separated `Y` and a separated `a`, the final object of `X_étale`
has a covering family `E` with finite index type whose members have affine underlying schemes and
are affine over `Y`, and whose iterated fibre products over `X` are affine over `Y`. -/
public theorem
    exists_finite_coversTop_isAffineHom_piObj_of_compactSpace_of_isSeparated_of_isSeparatedHom
    [CompactSpace ↥X.obj] [Y.obj.IsSeparated] [IsSeparated (schemeHom B a)] :
    ∃ E : PreZeroHypercover.{u} (final B X.obj X.property), Finite E.I₀ ∧
      (topology B X.obj X.property).CoversTop E.X ∧
      (∀ j, AlgebraicGeometry.IsAffine ((toScheme B X.obj X.property).obj (E.X j))) ∧
      (∀ j, IsAffineHom (toBaseHom B a (E.X j))) ∧
      ∀ (p : ℕ) (i : Fin (p + 1) → E.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
            HasProduct (fun b ↦ Over.mk (E.f (j b))) := fun q j ↦
          Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
        IsAffineHom (toBaseHom B a (∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left) := by
  obtain ⟨E, hfin, hcov, haff⟩ :=
    exists_finite_coversTop_isAffine_of_compactSpace B X.obj X.property
  exact ⟨E, hfin, hcov, haff,
    fun j ↦ isAffineHom_toBaseHom B a _ (haff j),
    fun p i ↦ isAffineHom_toBaseHom_piObj_of_isSeparatedHom B a E
      (fun j ↦ isAffineHom_toBaseHom B a _ (haff j)) p i⟩

end Base

end AlgebraicGeometry.SmallEtale

end
