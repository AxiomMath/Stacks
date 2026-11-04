module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatInBothVariables
public import StacksFrontier.Homology.KFlat.AcyclicKFlat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange

@[expose] public section

/-!
# An acyclic K-flat complex of modules annihilates every tensor product

Let `R` be a commutative ring and `C` a cochain complex of `R`-modules which is **both** acyclic
and K-flat. Then `Tot(G ⊗_R C)` is acyclic for *every* complex `G`, with no hypothesis on `G`
at all, and the same holds after base change along a ring map `R → S` for every complex of
`S`-modules.

Neither hypothesis on `C` can be dropped. K-flatness alone says nothing about `Tot(G ⊗_R C)`
for a `G` with homology, and acyclicity alone says nothing either, since `Tot(- ⊗_R -)` is not
computed degreewise.

## Main results

* `CochainComplex.KFlat.kFlatLeft_of_kFlat`: a K-flat complex of `R`-modules is K-flat in the
  left variable of the tensor product.
* `CochainComplex.KFlat.acyclic_tensorObj_of_kFlat_of_acyclic`: the statement above.
* `CochainComplex.KFlat.acyclic_tensorObj_extendScalars_of_kFlat_of_acyclic`: its form after
  extension of scalars along `φ : R →+* S`.

## Implementation notes

Both statements are fed to the bifunctor-generic K-flatness engine with no transport:
`CochainComplex.KFlat` is definitionally K-flatness for the bifunctor
`MonoidalCategory.curriedTensor`, the monoidal product of complexes *being* the bifunctor
total complex of the curried tensor. That identity is already recorded, as
`CochainComplex.kFlat_iff_kFlatBifunctor` in
`StacksFrontier.Topology.Sheaves.Modules.StalkKFlat`, and is not restated here.

The mathematics is `CochainComplex.KFlatBifunctor.acyclic_totalComplex_of_kFlat_of_acyclic`,
the general bifunctor statement, whose remaining input is a resolution of `G` by a complex which is
K-flat in the *left* variable of the bifunctor. On a ringed site that input is supplied by
`Stacks.DerivedTensor.RingedSite.exists_kFlatLeft_quasiIso`; here it is supplied by composing the
  ordinary K-flat
resolution of Stacks 06Y4 with `kFlatLeft_of_kFlat`, which converts K-flatness in one variable
into K-flatness in the other.

That conversion is the whole content of the file, and until recently it was unavailable at the
module level. It reads left K-flatness for `F` as K-flatness for `F.flip`
(`CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip`) and then compares `F.flip` with `F`
by `BraidedCategory.curriedBraidingNatIso`, exactly as the ringed-site statement
`Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat` does through
  `Stacks.SheafOfModules.Tensor.sheafTensorFlipNatIso`. The
braiding it needs is the one for the *lifted* monoidal structure that
`CochainComplex.KFlat` pins — Mathlib's symmetry on `ModuleCat.{u} R` is stated against a
different monoidal instance and does not transfer, even at `v = u` — and it is supplied by
`ModuleCat.liftedModuleSymmetric`. No braiding of *total* complexes is needed anywhere: the
Koszul signs are handled once and for all inside `kFlatLeft_iff_kFlat_flip` by Mathlib's
`HomologicalComplex.mapBifunctorFlipIso`.

The base-change form is not proved by transporting acyclicity of `C` through `extendScalars`,
which would be a separate theorem; it is the same-ring statement read through
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso`, which identifies the underlying
complex of `R`-modules of `G ⊗_S (S ⊗_R C)` with `G ⊗_R C`, together with the fact that
restriction of scalars reflects acyclicity. Its universe discipline is that of
`StacksFrontier.Homology.KFlat.ScalarBaseChange`: the two ring universes are independent, the
module universe is independent of both, and the lifted monoidal structures are pinned
explicitly at each ring because instance synthesis cannot choose the extra universe argument on
its own — left to search, the elaborator reports `stuck at solving universe constraint`
`max uR uS v =?= max uS ?u`.

## References

* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [The Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

namespace CochainComplex.KFlat

universe u v uR uS

section SameRing

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct ModuleCat.liftedModuleMonoidal
  ModuleCat.liftedModuleMonoidalPreadditive ModuleCat.liftedModuleSymmetric

variable {R : Type u} [CommRing R]

/-- **A K-flat complex of `R`-modules is K-flat in the left variable of the tensor product**:
`Tot(K ⊗_R G)` is acyclic for every acyclic `G`.

The two predicates constrain different arguments of the tensor bifunctor, and it is the
symmetry of the tensor product that identifies the conditions they impose: left K-flatness for
`⊗_R` is K-flatness for `(⊗_R)ᶠˡᶦᵖ`, and K-flatness is invariant under an isomorphism of
bifunctors. This is `Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat` with
  `ModuleCat.liftedModuleSymmetric` in
place of `Stacks.SheafOfModules.Tensor.sheafTensorFlipNatIso`. -/
theorem kFlatLeft_of_kFlat {K : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (hK : CochainComplex.KFlat.{u, v} K) :
    CochainComplex.KFlatBifunctor.KFlatLeft (curriedTensor (ModuleCat.{max u v} R)) K :=
  (CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip _ K).2
    (CochainComplex.KFlatBifunctor.kFlat_of_natIso _ _
      (BraidedCategory.curriedBraidingNatIso (ModuleCat.{max u v} R)) hK)

/-- **An acyclic K-flat complex of `R`-modules makes `Tot(G ⊗_R C)` acyclic for every complex
`G` of `R`-modules.**

The two hypotheses on `C` are used once each and in different variables of the tensor product.
Acyclicity of `C` is what makes `Tot(P ⊗_R C)` acyclic, by left K-flatness of a K-flat
resolution `P ⟶ G`; K-flatness of `C` is what makes `Tot(- ⊗_R C)` carry the quasi-isomorphism
`P ⟶ G` to a quasi-isomorphism, along which that acyclicity transports. No hypothesis on `G`
survives, because every complex of modules admits a K-flat resolution (Stacks 06Y4). -/
theorem acyclic_tensorObj_of_kFlat_of_acyclic {C : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (hC : CochainComplex.KFlat.{u, v} C) (hCac : C.Acyclic)
    (G : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (HomologicalComplex.tensorObj G C).Acyclic := by
  obtain ⟨P, q, hP, -, hq, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, v} G
  exact CochainComplex.KFlatBifunctor.acyclic_totalComplex_of_kFlat_of_acyclic
    (curriedTensor (ModuleCat.{max u v} R)) hC hCac q hq (kFlatLeft_of_kFlat hP)

end SameRing

section BaseChange

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- **An acyclic K-flat complex of `R`-modules makes `Tot(G ⊗_S (S ⊗_R C))` acyclic for every
complex `G` of `S`-modules**, for any ring map `φ : R →+* S`.

Extension of scalars carries `C` to a K-flat complex of `S`-modules
(`CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars`, Stacks 06Y1), but acyclicity of
the base change is not what is used, and is not needed: the comparison
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso` says that the underlying complex
of `R`-modules of `G ⊗_S (S ⊗_R C)` is `G ⊗_R C` with `G` restricted, and restriction of
scalars reflects acyclicity, so the statement reduces to the same-ring one over `R`. -/
theorem acyclic_tensorObj_extendScalars_of_kFlat_of_acyclic (φ : R →+* S)
    {C : CochainComplex (ModuleCat.{max v uR uS} R) ℤ}
    (hC : CochainComplex.KFlat.{uR, max v uS} C) (hCac : C.Acyclic)
    (G : CochainComplex (ModuleCat.{max v uR uS} S) ℤ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uS} S) :=
    ModuleCat.liftedModuleMonoidalStruct.{uS, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uS} S) :=
    ModuleCat.liftedModuleMonoidal.{uS, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uS} S) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uS, max v uR};
  (HomologicalComplex.tensorObj G
      ((CochainComplex.extendScalarsLarge.{v, uR, uS} φ).obj C)).Acyclic :=
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uS} S) :=
    ModuleCat.liftedModuleMonoidalStruct.{uS, max v uR};
  let : MonoidalCategory (ModuleCat.{max v uR uS} S) :=
    ModuleCat.liftedModuleMonoidal.{uS, max v uR};
  let : MonoidalPreadditive (ModuleCat.{max v uR uS} S) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uS, max v uR};
  by
  refine (CochainComplex.restrictScalarsLarge_acyclic_iff.{v} φ _).1 ?_
  exact HomologicalComplex.Acyclic.of_iso
    (CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso.{uR, uS, v} φ C G).symm
    (acyclic_tensorObj_of_kFlat_of_acyclic.{uR, max v uS} hC hCac
      ((CochainComplex.restrictScalarsLarge.{v} φ).obj G))

end BaseChange

end CochainComplex.KFlat

end

end
