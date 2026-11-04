module

public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExternalTensorResolution

/-!
# A finite type module on a product is a quotient of an external tensor product

[Stacks, Tag 0FZ1] drops every Noetherian hypothesis from [Stacks, Tag 0FZ0]: for `R` an
arbitrary ring and `X`, `Y` quasi-compact quasi-separated `R`-schemes with the resolution
property, every **finite type quasi-coherent** `𝒪_{X ×_R Y}`-module `F` admits a surjection
`𝓔 ⊠ 𝓖 ⟶ F` with `𝓔` finite locally free on `X` and `𝓖` finite locally free on `Y`.

This file proves that statement when `X ×_R Y` is Noetherian and `X`, `Y` are locally
Noetherian.  The base ring is an arbitrary commutative ring and the structure morphisms are not
assumed to be of finite type, so the hypotheses are not those of [Stacks, Tag 0FZ0]; what is
assumed instead is exactly the Noetherian condition that the limit argument of
[Stacks, Tag 0FZ1] is there to remove.

## Main results

* `AlgebraicGeometry.exists_externalTensorProduct_epi_of_isFiniteType`: [Stacks, Tag 0FZ1] when
  `X ×_R Y` is Noetherian and `X`, `Y` are locally Noetherian.

## Implementation notes

Over a locally Noetherian scheme a quasi-coherent module of finite type is coherent — this is
[Stacks, Tag 01XZ], (2) ⇒ (1), proved as
`Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType` — so under
the Noetherian hypothesis the finite type module of [Stacks, Tag 0FZ1] is a coherent module and
`AlgebraicGeometry.exists_isFiniteLocallyFree_epi_externalTensorProduct`, the content of
[Stacks, Tag 0FZ0], applies to it directly.  That is the whole proof: the Noetherian case of
0FZ1 is 0FZ0 together with 01XZ.

**What is not proved.** The general case of [Stacks, Tag 0FZ1] is a limit argument: replace `R`
by `ℤ` (harmless, since `X ×_R Y` is a closed subscheme of `X ×_ℤ Y`), use
[Stacks, Tag 086M] to assume `F` of finite presentation, write `X = lim X_i` and `Y = lim Y_j`
with the `X_i`, `Y_j` of finite presentation over `ℤ` ([Stacks, Tag 01ZA]), descend `F` to some
`X_i ×_ℤ Y_j` ([Stacks, Tag 01ZR]) along with the resolution property
([Stacks, Tag 0F8B]), apply [Stacks, Tag 0FZ0] there and pull back.  The descent of the
resolution property is the hard input, and the hard direction of [Stacks, Tag 0F8B] rests in
turn on the converse half of [Stacks, Tag 0F89]; neither is available, so the tag below carries
a clause string naming the case that is proved.

The quasi-compactness and quasi-separatedness of `X` and `Y` are hypotheses of
[Stacks, Tag 0FZ1] and are recorded below even though the Noetherian route does not consume
them, so that the statement is an instance of the source statement rather than a variant of it.

## References

* [Stacks Project, Tag 0FZ1](https://stacks.math.columbia.edu/tag/0FZ1)
* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0FZ1] when `X ×_R Y` is Noetherian.** Let `R` be a ring and let `X`, `Y` be
quasi-compact, quasi-separated, locally Noetherian `R`-schemes with the resolution property,
with `X ×_R Y` Noetherian.  Every finite type quasi-coherent `𝒪_{X ×_R Y}`-module `F` admits a
surjection `𝓔 ⊠ 𝓖 ⟶ F` with `𝓔` a finite locally free `𝒪_X`-module and `𝓖` a finite locally
free `𝒪_Y`-module.

Under the Noetherian hypothesis `F` is coherent ([Stacks, Tag 01XZ]) and the statement is
[Stacks, Tag 0FZ0]; the limit argument that removes the hypothesis is not proved, see the
implementation notes of this file. -/
@[stacks 0FZ1 "the case where the product is Noetherian and the two factors are locally \
Noetherian; the limit argument removing those hypotheses is not covered"]
theorem exists_externalTensorProduct_epi_of_isFiniteType (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [HasResolutionProperty X] [HasResolutionProperty Y] [IsNoetherian (pullback f g)]
    (F : (pullback f g).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (E : X.Modules) (G : Y.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G)
      (q : externalTensorProduct f g E G ⟶ F), Epi q :=
  have : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType F
  exists_isFiniteLocallyFree_epi_externalTensorProduct f g F

end AlgebraicGeometry

end
