module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuotientScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdUnderlying
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ActionQuotientSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent

/-!
# Separatedness of a finite self-product, of the complement of its diagonals, and of `U_p`

Let `X` be an algebraic space over a scheme `S` which is separated over `S`, and let `U` be an
object of the spaces-étale site of `X` whose structure morphism `U ⟶ X` is separated.  Then the
`n`-fold self-product `U^n = U ×_X ⋯ ×_X U` is separated over `S`, and so is the complement
`W_n` of all the diagonals in it, which is an open subspace of `U^n`.  When `W_n` is
representable, the scheme representing it is separated over `S`, and the quotient
`U_p = W_p/S_{p+1}` of [Stacks, Tag 0726] is separated over `S` by [Stacks, Tag 02Z4] part (2).

This is the separated companion of
`StacksFrontier/AlgebraicGeometry/Spaces/AlternatingCech/DiagonalComplementQuasiSeparated.lean`,
and the two together are what choices (4) and (5) of [Stacks, Tag 072C] need of the space `W_p`
of [Stacks, Tag 0726]: "since `X` is quasi-separated the schemes `W_p` are quasi-compact, hence
`U_p` is quasi-compact; since `U` is separated, the schemes `W_p` are separated, hence `U_p` is
separated".  The second clause is what this file proves.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isSeparatedOver_of_mono` and
  `AlgebraicGeometry.Space.isSeparatedOver_source_of_iso`: the source of a monomorphism into a
  presheaf separated over `S` is separated over `S`.
* `AlgebraicGeometry.Space.isSeparated_underlyingOver_hom_of_isSeparatedOver`: an object of the
  site whose represented presheaf is separated over `S` has separated structure morphism of
  schemes.  This is the converse of
  `AlgebraicGeometry.Space.isSeparatedOver_yoneda_obj` read relatively over `S`.
* `AlgebraicGeometry.Space.SpacesEtale.isSeparatedOver_underlying_selfProd` and
  `AlgebraicGeometry.Space.SpacesEtale.isSeparatedOver_underlying_diagonalComplement`: the
  self-product and the complement of its diagonals are separated over `S`.
* `AlgebraicGeometry.Space.SpacesEtale.isSeparated_underlyingOver_diagonalComplementScheme`:
  **the scheme representing `W_n` is separated over `S`**, which is the instance
  `AlgebraicGeometry.Space.isSeparatedOver_actionQuotient_unconditional` takes.
* `AlgebraicGeometry.Space.SpacesEtale.isSeparatedOver_diagonalComplementQuotient`:
  **the quotient `U_p = W_p/S_{p+1}` is separated over `S`.**

## Implementation notes

Separatedness is taken throughout in the relative form
`AlgebraicGeometry.Space.IsSeparatedOver` of [Stacks, Tag 02X5], which is the form
`AlgebraicGeometry.Space.isSeparatedOver_actionQuotient_unconditional` concludes in and the form
its hypothesis on the scheme representing `W_n` is stated in.  Unlike the quasi-separated
companion no absolute form over `Spec ℤ` is needed, so no hypothesis `B.Contains (⊤_ Scheme)`
appears and the transport between the relative and the absolute readings is not run.

The induction is the one of
`AlgebraicGeometry.Space.SpacesEtale.isAbsolutelyQuasiSeparated_underlying_selfProd`: the empty
product is a final object of the site, whose underlying algebraic space is `X` itself, and the
step from `n` to `n + 1` reads `U^{n+1}` as the fibre product over `X` of `U` with `U^n`
through `AlgebraicGeometry.Space.SpacesEtale.underlyingSelfProdSuccIso`.  Where the
quasi-separated companion invokes a fibre-product permanence result, the separated version needs
none: the second projection `U ×_X U^n ⟶ U^n` is a base change of `U ⟶ X`, hence separated by
`AlgebraicGeometry.Space.isSeparated_pullbackSnd`, and [Stacks, Tag 04ZH] part (4) carries
separatedness over `S` from the target of a separated morphism to its source.  This is why the
hypothesis on `U` here is separatedness of its structure morphism — which is already carried by
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplement` as `hsep` — rather than separatedness
of `U` over `S`.

For the complement of the diagonals no closedness is used: its inclusion into `U^n` is the
inclusion of a subfunctor, hence a monomorphism, hence a separated morphism, and the same part
of [Stacks, Tag 04ZH] applies.

Nothing here carries `@[stacks 02Z4]`: that tag sits on
`AlgebraicGeometry.Space.isSeparatedOver_actionQuotient_unconditional`, and this file only
supplies its hypothesis and applies it.  Neither does anything here carry `@[stacks 072C]`,
whose content is the spectral-sequence argument of which this is one input.

## References

* [Stacks Project, Tag 02X5](https://stacks.math.columbia.edu/tag/02X5)
* [Stacks Project, Tag 02Z4](https://stacks.math.columbia.edu/tag/02Z4)
* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The source of a monomorphism into a presheaf separated over `S` is separated over `S`.**
A monomorphism of presheaves is a separated morphism, so this is [Stacks, Tag 04ZH]
part (4). -/
theorem isSeparatedOver_of_mono {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : Mono f) (hG : IsSeparatedOver B S hS G) :
    IsSeparatedOver B S hS F :=
  isSeparatedOver_of_isSeparated B S hS hG (isSeparated_of_mono f hf)

/-- **Separatedness over `S` transports along an isomorphism of presheaves.** -/
theorem isSeparatedOver_source_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (hG : IsSeparatedOver B S hS G) :
    IsSeparatedOver B S hS F :=
  isSeparatedOver_of_mono B S hS e.hom
    ⟨fun g h w => by
      rw [← Category.comp_id g, ← Category.comp_id h, ← e.hom_inv_id, ← Category.assoc, w,
        Category.assoc]⟩ hG

/-- **An object of the site whose represented presheaf is separated over `S` has separated
structure morphism of schemes.** The structure morphism of the object to the terminal object of
the site is a separated morphism of presheaves by [Stacks, Tag 04ZH] part (4), hence so is the
scheme morphism it represents by [Stacks, Tag 03KY]; that scheme morphism is the structure
morphism of the underlying scheme over `S`.

This is the converse of `AlgebraicGeometry.Space.isSeparatedOver_yoneda_obj`, which runs from
absolute separatedness of the underlying scheme; here both sides are relative to `S`. -/
theorem isSeparated_underlyingOver_hom_of_isSeparatedOver (T : BigFppfOver B S hS)
    (hT : IsSeparatedOver B S hS (yoneda.obj T)) :
    _root_.AlgebraicGeometry.IsSeparated (underlyingOver B hS T).hom := by
  have hmap : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from T)) :=
    (isSeparated_yoneda_map_iff B S hS (Over.mkIdTerminal.from T)).1
      (isSeparated_of_isSeparatedOver B S hS hT (yoneda.map (Over.mkIdTerminal.from T)))
  have heq : (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from T) =
      (underlyingOver B hS T).hom :=
    congrArg B.inclusion.map
      (show (Over.mkIdTerminal.from T : T ⟶ Over.mk (𝟙 (B.obj hS))).left = T.hom by simp)
  rwa [heq] at hmap

variable (X : AlgebraicSpaces B S hS)

namespace SpacesEtale

open Stacks.OverProducts

/-- **A finite self-product in the spaces-étale site of `X` is separated over `S`.** If `X` is
separated over `S` and the structure morphism of `U` is separated, then the algebraic space
underlying the `n`-fold self-product `U ×_X ⋯ ×_X U` is separated over `S`.

The empty product is a final object of the site, so the case `n = 0` is the hypothesis on `X`;
the step from `n` to `n + 1` reads `U^{n+1}` as the fibre product of `U` with `U^n` over `X`,
whose second projection is a base change of the structure morphism of `U` and so separated. -/
theorem isSeparatedOver_underlying_selfProd (U : SpacesEtale B S hS X)
    (hX : IsSeparatedOver B S hS X.1) (hsep : IsSeparated B S hS U.1.hom.hom) (n : ℕ) :
    IsSeparatedOver B S hS (underlying B S hS X (selfProd B S hS X U n)).1 := by
  induction n with
  | zero =>
      have hlim : IsLimit (Fan.mk (∏ᶜ fun _ : Fin 0 => U) (Pi.π fun _ : Fin 0 => U)) :=
        productIsProduct _
      have hT : IsTerminal (selfProd B S hS X U 0) :=
        (isLimitEquivIsTerminalOfIsEmpty _ _) hlim
      refine isSeparatedOver_source_of_iso B S hS ?_ hX
      exact ((ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
        ((toSpaces B S hS X).mapIso
          ((final_isTerminal B S hS X).uniqueUpToIso hT))).symm
  | succ n ih =>
      have hpb : IsSeparatedOver B S hS
          (pullback U.1.hom.hom (selfProd B S hS X U n).1.hom.hom) :=
        isSeparatedOver_of_isSeparated B S hS ih
          (isSeparated_pullbackSnd B S hS (selfProd B S hS X U n).1.hom.hom hsep)
      refine isSeparatedOver_source_of_iso B S hS ?_ hpb
      refine (ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
        (underlyingSelfProdSuccIso B S hS X U n) ≪≫ ?_
      exact pullbackFiberProductIso B S hS U.1.hom (selfProd B S hS X U n).1.hom

/-- **The complement of the diagonals in a self-product separated over `S` is separated over
`S`.** Its inclusion into the self-product is the inclusion of a subfunctor, hence a
monomorphism, so this is `AlgebraicGeometry.Space.isSeparatedOver_of_mono`. -/
theorem isSeparatedOver_diagonalComplement (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    (hprod : IsSeparatedOver B S hS
      (underlying B S hS X (selfProd B S hS X U n)).1) :
    IsSeparatedOver B S hS
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1 :=
  isSeparatedOver_of_mono B S hS
    (Subfunctor.ι (diagonalComplementSubspace B S hS X U n hsep).1)
    (inferInstanceAs (Mono (Subfunctor.ι _))) hprod

/-- **The space `W_n` of [Stacks, Tag 0726] is separated over `S`** when `X` is and the
structure morphism of the chart is: the self-product is separated over `S` by
`AlgebraicGeometry.Space.SpacesEtale.isSeparatedOver_underlying_selfProd`, and the complement of
the diagonals is an open subspace of it. -/
theorem isSeparatedOver_underlying_diagonalComplement (U : SpacesEtale B S hS X)
    (hX : IsSeparatedOver B S hS X.1) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    IsSeparatedOver B S hS
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1 :=
  isSeparatedOver_diagonalComplement B S hS X U n hsep
    (isSeparatedOver_underlying_selfProd B S hS X U hX hsep n)

variable (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).obj)

include U n hsep e in
/-- **The presheaf represented by the scheme representing `W_n` is separated over `S`**: it is
isomorphic to the algebraic space underlying `W_n`, which is separated over `S`. -/
theorem isSeparatedOver_yoneda_diagonalComplementScheme
    (hX : IsSeparatedOver B S hS X.1) :
    IsSeparatedOver B S hS (yoneda.obj V) :=
  isSeparatedOver_source_of_iso B S hS e
    (isSeparatedOver_underlying_diagonalComplement B S hS X U hX n hsep)

include U n hsep e in
/-- **The scheme representing `W_n` is separated over `S`.** This is the instance hypothesis
of `AlgebraicGeometry.Space.isSeparatedOver_actionQuotient_unconditional`, and the one input
that the quotient `U_p = W_p/S_{p+1}` needed for its separatedness. -/
theorem isSeparated_underlyingOver_diagonalComplementScheme
    (hX : IsSeparatedOver B S hS X.1) :
    _root_.AlgebraicGeometry.IsSeparated (underlyingOver B hS V).hom :=
  isSeparated_underlyingOver_hom_of_isSeparatedOver B S hS V
    (isSeparatedOver_yoneda_diagonalComplementScheme B S hS X U n hsep V e hX)

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

include e in
/-- **The quotient `U_p = W_p/S_{p+1}` is separated over `S`.** This is [Stacks, Tag 02Z4]
part (2) for the action of the symmetric group on the complement of the diagonals, read through
an object `V` of the site representing `W_n`: the action is free in the strong sense that no
nonidentity permutation fixes a point of `V` together with its residue field, by
`actsNontriviallyOnFixedResidueFields_diagonalComplementSchemeAut`, `V` is separated over `S` by
`isSeparated_underlyingOver_diagonalComplementScheme`, and `U_p` is the quotient sheaf `V/S_n` by
`diagonalComplementQuotientIsoActionQuotient`.

This is the clause "since `U` is separated, the schemes `W_p` are separated, hence `U_p` is
separated" of [Stacks, Tag 072C], and one of the inputs the vanishing of [Stacks, Tag 072B]
draws from separatedness of `X`. -/
theorem isSeparatedOver_diagonalComplementQuotient (hX : IsSeparatedOver B S hS X.1) :
    IsSeparatedOver B S hS (diagonalComplementQuotient B S hS X U n hsep).obj :=
  have : _root_.AlgebraicGeometry.IsSeparated (underlyingOver B hS V).hom :=
    isSeparated_underlyingOver_diagonalComplementScheme B S hS X U n hsep V e hX
  isSeparatedOver_source_of_iso B S hS
    (diagonalComplementQuotientIsoActionQuotient B S hS X U n hsep V e)
    (isSeparatedOver_actionQuotient_unconditional B hS V (Equiv.Perm (Fin n))
      (diagonalComplementOverAut B S hS X U n hsep V e)
      (actsNontriviallyOnFixedResidueFields_diagonalComplementSchemeAut B S hS X U n hsep V e))

end SpacesEtale

end AlgebraicGeometry.Space

end
