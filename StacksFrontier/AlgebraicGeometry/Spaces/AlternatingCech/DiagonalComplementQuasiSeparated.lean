module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdUnderlying
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Quasi-separatedness of a finite self-product and of the complement of its diagonals

The `n`-fold self-product `U^n = U ×_X ⋯ ×_X U` of an object `U` of the spaces-étale site of an
algebraic space `X` is quasi-separated as soon as `X` and the algebraic space underlying `U`
are, and so is the complement `W_n` of all the diagonals in it, which is an open subspace of
`U^n`.

This is the companion of
`AlgebraicGeometry.Space.SpacesEtale.isQuasiCompactSpace_underlying_selfProd` for the other
finiteness condition, and the two together are what choices (4) and (5) of [Stacks, Tag 072C]
need of the space `W_p` of [Stacks, Tag 0726] before its quotient by the symmetric group can be
charted: "since `X` is quasi-separated the schemes `W_p` are quasi-compact, hence `U_p` is
quasi-compact; since `U` is separated, the schemes `W_p` are separated, hence `U_p` is
separated".

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_yoneda_obj` and
  `AlgebraicGeometry.Space.quasiSeparatedSpace_toScheme_obj`: for an object of the site over a
  quasi-separated base, quasi-separatedness of the algebraic space it represents and of its
  underlying scheme agree.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_mono`: the source of a monomorphism
  into a quasi-separated algebraic space is quasi-separated.
* `AlgebraicGeometry.Space.SpacesEtale.isAbsolutelyQuasiSeparated_underlying_selfProd` and
  `AlgebraicGeometry.Space.SpacesEtale.isAbsolutelyQuasiSeparated_underlying_diagonalComplement`:
  the two statements of the title.

## Implementation notes

Quasi-separatedness is taken throughout in the absolute form
`AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` of [Stacks, Tag 03BS] part (3), which is
the form [Stacks, Tag 073B] part (3) is stated in and the form
`AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers'`
consumes.

The induction is the one of
`AlgebraicGeometry.Space.SpacesEtale.isQuasiCompactSpace_underlying_selfProd`: the empty
product is a final object of the site, whose underlying algebraic space is `X` itself, and the
step from `n` to `n + 1` reads `U^{n+1}` as the fibre product over `X` of `U` with `U^n`
through `AlgebraicGeometry.Space.SpacesEtale.underlyingSelfProdSuccIso` and applies
[Stacks, Tag 073B] part (3). Unlike the quasi-compact case the inductive step needs no
hypothesis on `X`, since a fibre product of two quasi-separated algebraic spaces is
quasi-separated whatever it is taken over; `X` enters only through the base case.

For the complement of the diagonals no closedness is used: its inclusion into `U^n` is the
inclusion of a subfunctor, hence a monomorphism, hence a quasi-separated morphism, and
[Stacks, Tag 04ZH] part (2) carries quasi-separatedness from the target to the source. This is
in contrast to
`AlgebraicGeometry.Space.SpacesEtale.isQuasiCompactSpace_diagonalComplement`, which does need
the inclusion to be a closed immersion.

## References

* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 04ZI](https://stacks.math.columbia.edu/tag/04ZI)
* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The source of a monomorphism into a quasi-separated algebraic space is
quasi-separated.** A monomorphism of presheaves is a quasi-separated morphism, so this is
[Stacks, Tag 04ZH] part (2). -/
theorem isAbsolutelyQuasiSeparated_of_mono {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G) (hf : Mono f)
    (hG : IsAbsolutelyQuasiSeparated B S hS hZ G) :
    IsAbsolutelyQuasiSeparated B S hS hZ F :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hF hG
    (isQuasiSeparated_of_mono B S hS f hf)

/-- **Quasi-separatedness transports along an isomorphism of presheaves.** -/
theorem isAbsolutelyQuasiSeparated_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (e : F ≅ G)
    (hG : IsAbsolutelyQuasiSeparated B S hS hZ G) :
    IsAbsolutelyQuasiSeparated B S hS hZ F :=
  isAbsolutelyQuasiSeparated_of_mono B S hS hZ hF e.hom
    ⟨fun g h w => by
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using w =≫ e.inv⟩ hG

/-- **An object of the site with quasi-separated underlying scheme represents a
quasi-separated algebraic space.** This is the implication `(ι) ⇒ (η)` of [Stacks, Tag 03JX] at
the object itself. -/
theorem isAbsolutelyQuasiSeparated_yoneda_obj (T : BigFppfOver B S hS)
    (hT : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T) :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj T) hZ
    ⟨T, hT, ⟨Functor.RepresentableBy.yoneda T⟩⟩

/-- **An object of the site over a quasi-separated base whose represented presheaf is a
quasi-separated algebraic space has quasi-separated underlying scheme.** The structure morphism
of the object to the terminal object of the site is quasi-separated by [Stacks, Tag 04ZI]
part (6), hence so is the scheme morphism it represents by [Stacks, Tag 03KY]; the underlying
scheme of the terminal object is the base. -/
theorem quasiSeparatedSpace_toScheme_obj (hSqs : QuasiSeparatedSpace S)
    (T : BigFppfOver B S hS)
    (hT : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T)) :
    QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T) := by
  set E : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS)) with hE
  have hterm : IsTerminal E := Over.mkIdTerminal
  set m : T ⟶ E := hterm.from T with hm
  have hqsOver : IsQuasiSeparatedOver B S hS (yoneda.obj T) :=
    isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS hZ
      (isAlgebraicSpace_yoneda B S hS T) hT
  have hmap : QuasiSeparated ((BigFppfOver.toScheme B S hS).map m) :=
    (isQuasiSeparated_yoneda_map_iff B S hS m).1
      (isQuasiSeparated_of_isQuasiSeparatedOver B S hS hqsOver (yoneda.map m))
  have hEqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj E) := hSqs
  have _ := hmap
  have _ : QuasiSeparated (terminal.from ((BigFppfOver.toScheme B S hS).obj E)) :=
    (quasiSeparatedSpace_iff_quasiSeparated _).mp hEqs
  have hcomp : (BigFppfOver.toScheme B S hS).map m ≫
      terminal.from ((BigFppfOver.toScheme B S hS).obj E) =
      terminal.from ((BigFppfOver.toScheme B S hS).obj T) :=
    terminalIsTerminal.hom_ext _ _
  rw [quasiSeparatedSpace_iff_quasiSeparated, ← hcomp]
  infer_instance

variable (X : AlgebraicSpaces B S hS)

namespace SpacesEtale

open Stacks.OverProducts

/-- **A finite self-product of the spaces-étale site of `X` is quasi-separated.** If `X` and
the algebraic space underlying `U` are quasi-separated, then so is the algebraic space
underlying the `n`-fold self-product `U ×_X ⋯ ×_X U`.

The empty product is a final object of the site, so the case `n = 0` is the hypothesis on `X`;
the step from `n` to `n + 1` is [Stacks, Tag 073B] part (3) for the fibre product of `U` with
the `n`-fold self-product over `X`. -/
theorem isAbsolutelyQuasiSeparated_underlying_selfProd (U : SpacesEtale B S hS X)
    (hX : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hU : IsAbsolutelyQuasiSeparated B S hS hZ (underlying B S hS X U).1) (n : ℕ) :
    IsAbsolutelyQuasiSeparated B S hS hZ
      (underlying B S hS X (selfProd B S hS X U n)).1 := by
  induction n with
  | zero =>
      have hlim : IsLimit (Fan.mk (∏ᶜ fun _ : Fin 0 => U) (Pi.π fun _ : Fin 0 => U)) :=
        productIsProduct _
      have hT : IsTerminal (selfProd B S hS X U 0) :=
        (isLimitEquivIsTerminalOfIsEmpty _ _) hlim
      refine isAbsolutelyQuasiSeparated_of_iso B S hS hZ
        (underlying B S hS X (selfProd B S hS X U 0)).2 ?_ hX
      exact ((ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
        ((toSpaces B S hS X).mapIso
          ((final_isTerminal B S hS X).uniqueUpToIso hT))).symm
  | succ n ih =>
      have hpb := isAbsolutelyQuasiSeparated_pullback B S hS hZ
        U.1.hom.hom (selfProd B S hS X U n).1.hom.hom (underlying B S hS X U).2
        (underlying B S hS X (selfProd B S hS X U n)).2 X.2 hU ih
      refine isAbsolutelyQuasiSeparated_of_iso B S hS hZ
        (underlying B S hS X (selfProd B S hS X U (n + 1))).2 ?_ hpb
      refine (ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
        (underlyingSelfProdSuccIso B S hS X U n) ≪≫ ?_
      exact pullbackFiberProductIso B S hS U.1.hom (selfProd B S hS X U n).1.hom

/-- **The complement of the diagonals in a quasi-separated self-product is quasi-separated.**
Its inclusion into the self-product is the inclusion of a subfunctor, hence a monomorphism, so
this is `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_mono`. -/
theorem isAbsolutelyQuasiSeparated_diagonalComplement (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ
      (underlying B S hS X (selfProd B S hS X U n)).1) :
    IsAbsolutelyQuasiSeparated B S hS hZ
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1 :=
  isAbsolutelyQuasiSeparated_of_mono B S hS hZ
    (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
    (Subfunctor.ι (diagonalComplementSubspace B S hS X U n hsep).1)
    (inferInstanceAs (Mono (Subfunctor.ι _))) hqs

/-- **The space `W_n` of Stacks 0726 is quasi-separated** when `X` and the algebraic space
underlying the chart are: the self-product is quasi-separated by
`AlgebraicGeometry.Space.SpacesEtale.isAbsolutelyQuasiSeparated_underlying_selfProd`, and the
complement of the diagonals is an open subspace of it. -/
theorem isAbsolutelyQuasiSeparated_underlying_diagonalComplement (U : SpacesEtale B S hS X)
    (hX : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hU : IsAbsolutelyQuasiSeparated B S hS hZ (underlying B S hS X U).1) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    IsAbsolutelyQuasiSeparated B S hS hZ
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1 :=
  isAbsolutelyQuasiSeparated_diagonalComplement B S hS hZ X U n hsep
    (isAbsolutelyQuasiSeparated_underlying_selfProd B S hS hZ X U hX hU n)

end SpacesEtale

end AlgebraicGeometry.Space

end
