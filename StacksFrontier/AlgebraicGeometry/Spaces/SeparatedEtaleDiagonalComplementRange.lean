module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubfunctorDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreSquareOverIsoSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalComplement

/-!
# The diagonal piece of the fibre square of a separated étale morphism is the diagonal

Let `f : V ⟶ W` be a separated étale morphism of algebraic spaces over a scheme `S`. The
decomposition `V ×_W V = Δ(V) ⊔ U` of
`AlgebraicGeometry.Space.exists_diagonalComplement_decomposition` produces two complementary
open-and-closed subfunctors of `V ×_W V` and identifies them only by their point sets: one has the
point set of the relative diagonal and the other its complement. This file upgrades that
identification to an equality of subfunctors — the piece with the point set of the diagonal *is*
`Subfunctor.range (pullback.diagonal f)` — and then locates the complementary piece over the
base: if `T` is a subfunctor of `W` over which `f` restricts to an isomorphism `f⁻¹T ≅ T`, then
both projections of the complementary piece to `W` land over the open complement of `T`.

## Main results

* `AlgebraicGeometry.Space.eq_range_diagonal_of_range_pointsMap_eq`: an open subspace of the
  fibre square of a separated étale morphism whose point set is that of the relative diagonal is
  the range of the relative diagonal.
* `AlgebraicGeometry.Space.le_preimage_openComplement_of_inf_le_sheafify_bot`: a subfunctor of
  the fibre square meeting the diagonal over `T` only in the sheafification of the bottom
  subfunctor lies over the open complement of `T`.
* `AlgebraicGeometry.Space.exists_subfunctor_sheafify_sup_range_diagonal_eq_top`: the
  decomposition `V ×_W V = Δ(V) ⊔ U` with the diagonal piece given as the range of the diagonal
  and the complementary piece shown to lie over the open complement of `T`.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The range of the relative diagonal of a separated étale morphism of algebraic spaces over
`S` is an open subspace of the fibre square. -/
theorem isOpenSubspace_range_diagonal (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W) (hf : IsEtale B S hS f) :
    IsOpenSubspace B S hS (Subfunctor.range (pullback.diagonal f)) :=
  isOpenSubspace_subfunctorRange B S hS hV
    (isOpenImmersion_diagonal_of_isUnramified B S hS hV hW f
      (isUnramified_of_isEtale B S hS hf))

/-- The point set of the range of the relative diagonal is the point set of the relative
diagonal. -/
theorem range_pointsMap_ι_range_diagonal (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W) (hf : IsEtale B S hS f) :
    Set.range (pointsMap B S hS (Subfunctor.range (pullback.diagonal f)).toFunctor
        (Subfunctor.range (pullback.diagonal f)).ι) =
      Set.range (pointsMap B S hS V (pullback.diagonal f)) :=
  have : Mono (pullback.diagonal f) := mono_of_presheaf_isOpenImmersion
    (isOpenImmersion_diagonal_of_isUnramified B S hS hV hW f (isUnramified_of_isEtale B S hS hf))
  range_pointsMap_ι_range B S hS (pullback.diagonal f)

/-- An open subspace of the fibre square of a separated étale morphism of algebraic spaces over
`S` whose point set is the point set of the relative diagonal is the range of the relative
diagonal. -/
theorem eq_range_diagonal_of_range_pointsMap_eq (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W) (hf : IsEtale B S hS f)
    (D : Subfunctor (pullback f f)) (hD : IsOpenSubspace B S hS D)
    (hDrange : Set.range (pointsMap B S hS D.toFunctor D.ι) =
      Set.range (pointsMap B S hS V (pullback.diagonal f))) :
    D = Subfunctor.range (pullback.diagonal f) :=
  have hpoints := range_pointsMap_ι_range_diagonal B S hS hV hW f hf
  le_antisymm
    (le_of_range_pointsMap_ι_subset B S hS (isOpenSubspace_range_diagonal B S hS hV hW f hf)
      (hDrange.trans hpoints.symm).le)
    (le_of_range_pointsMap_ι_subset B S hS hD (hpoints.trans hDrange.symm).le)

/-- A section lying in the sheafification of the bottom subfunctor lives over an empty
scheme. -/
private theorem isEmpty_of_mem_sheafify_bot {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A : (BigFppfOver B S hS)ᵒᵖ} {x : F.obj A}
    (hx : x ∈ ((⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS)).obj A) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj A.unop) := by
  have hsieve : (⊥ : Subfunctor F).sieveOfSection x = ⊥ :=
    le_antisymm (fun _ _ h => h) bot_le
  have hbot : (⊥ : Sieve A.unop) ∈ BigFppfOver.topology B S hS A.unop := hsieve ▸ hx
  refine ⟨fun y => ?_⟩
  obtain ⟨Y, g, hg, -⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS hbot y
  exact hg

/-- Let `T` be a subfunctor of `W` over which `f` restricts to an isomorphism. A subfunctor of
the fibre square of `f` whose meet with the diagonal over `f⁻¹T` is contained in the
sheafification of the bottom subfunctor lies over the open complement of `T`. -/
theorem le_preimage_openComplement_of_inf_le_sheafify_bot (f : V ⟶ W) (T : Subfunctor W)
    (hT : IsIso (T.fromPreimage f)) (U : Subfunctor (pullback f f))
    (hU : U ⊓ Subfunctor.range ((T.preimage f).ι ≫ pullback.diagonal f) ≤
      (⊥ : Subfunctor (pullback f f)).sheafify (BigFppfOver.topology B S hS)) :
    U ≤ (openComplement B S hS T).preimage (pullback.fst f f ≫ f) := by
  intro A x hx A' a ha
  have hdiag : (pullback f f).map a x
      ∈ (Subfunctor.range ((T.preimage f).ι ≫ pullback.diagonal f)).obj A' := by
    rw [← preimage_fst_comp_eq_range_diagonal B S hS f T hT]
    show (pullback.fst f f ≫ f).app A' ((pullback f f).map a x) ∈ T.obj A'
    rwa [NatTrans.naturality_apply]
  exact isEmpty_of_mem_sheafify_bot B S hS (hU _ ⟨U.map a hx, hdiag⟩)

/-- **The decomposition `V ×_W V = Δ(V) ⊔ U`.** For a separated étale morphism `f : V ⟶ W` and
a subfunctor `T` of `W` over which `f` restricts to an isomorphism, there is a subfunctor `C` of
`V ×_W V` such that the range of the diagonal and `C` together sheafify to all of `V ×_W V`, and
both projections of `C` to `W` land over the open complement of `T`. -/
theorem exists_subfunctor_sheafify_sup_range_diagonal_eq_top
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W)
    (hf : IsEtale B S hS f) (hsep : IsSeparated B S hS f)
    (T : Subfunctor W) (hT : IsIso (T.fromPreimage f)) :
    ∃ C : Subfunctor (CategoryTheory.Limits.pullback f f),
      (Subfunctor.range (CategoryTheory.Limits.pullback.diagonal f) ⊔ C).sheafify
          (BigFppfOver.topology B S hS) = ⊤ ∧
      C ≤ (openComplement B S hS T).preimage
          (CategoryTheory.Limits.pullback.fst f f ≫ f) ∧
      C ≤ (openComplement B S hS T).preimage
          (CategoryTheory.Limits.pullback.snd f f ≫ f) := by
  obtain ⟨C, D, -, -, hDopen, -, hsup, hinf, hDrange, -⟩ :=
    exists_diagonalComplement_decomposition B S hS hV hW f hf hsep
  obtain rfl := eq_range_diagonal_of_range_pointsMap_eq B S hS hV hW f hf D hDopen hDrange
  have hC := le_preimage_openComplement_of_inf_le_sheafify_bot B S hS f T hT C
    ((inf_le_inf_left C (Subfunctor.range_comp_le (T.preimage f).ι (pullback.diagonal f))).trans_eq
      hinf)
  refine ⟨C, eq_top_iff.mpr (hsup.ge.trans (Subfunctor.sheafify_le_sheafify _
    (sup_le le_sup_right le_sup_left))), hC, ?_⟩
  rwa [← pullback.condition]

end AlgebraicGeometry.Space

end
