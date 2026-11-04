module

public import StacksFrontier.CategoryTheory.Functor.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroGenerators
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FlatFreeYoneda
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatTensorShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ResolutionBySumsOfExtensionsByZero
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise
import StacksCore.Tactic.StacksAttribute

/-!
# K-flat resolutions on a ringed site

Work towards Stacks Tag 06YS: every complex of modules on a ringed site admits a termwise
surjective quasi-isomorphism from a K-flat complex with flat terms.

## Main results

* `Stacks.SheafOfModules.KFlatResolution.isFlat_of_isSumOfExtensionByZeroStructureSheaves`: a
  direct sum of extensions by zero `j_{U!}O_U` of the structure sheaves is flat, which is exactly
  what the terms of 077J's ladder are. Flatness of a single `j_{U!}O_U` is
  `Stacks.SheafOfModules.FlatTensorShortExact.isFlat_extensionByZero_unit`, proved in Chapter 18
  because the sheaf-level flat quotient is needed there.
* `Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat`: a flat module placed in a single
  degree is K-flat,
  which is the base case 06YQ reduces the bounded-above case to.
* `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution`: **Tag 06YS.** Every complex of
  `O`-modules admits a
  termwise surjective quasi-isomorphism from a K-flat complex with flat terms.

## Implementation notes

The flatness of `j_{U!}O_U` as a *sheaf* of modules is the input 06YS needs and the one piece
the 03E-cluster stopped short of: `Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeYoneda`
  proves it for the free
*presheaf* on the representable at `U`, and
  `Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification` carries
flatness across sheafification, but nothing connected `j_{U!}O_U` to that presheaf.
`SheafOfModules.extensionByZeroIsoSheafifiedFreeYoneda` is that connection, and with it the
sheaf statement is the two library results composed.

Every spelling along the way was checked rather than assumed, because three of them could
have differed and did not: `Stacks.SheafOfModules.Tensor.ringSheaf R` and
`Stacks.SheafOfModules.Tensor.ringSheaf R` agree by `rfl`, as do
`(PresheafOfModules.free R).obj` and `PresheafOfModules.freeObj`, and also
`associatedRingMap J (𝟙 R.obj)` and `𝟙 (ringSheaf R).obj`.
The last of those is `rfl` but *not* visible to instance search, which works at `instances`
transparency and will not unfold `Functor.whiskerRight`; the two local-bijectivity instances
are therefore seated by hand at the `associatedRingMap` spelling rather than left to the
global instances at the `𝟙` spelling. `IsFlat` is moreover an `abbrev`, so in a statement
it unfolds before a named `(O := R)` can land and its four universes default; they are given
explicitly instead.

Note also that `isFlat_freeYoneda` pins the ring universe to the *hom* universe of the site,
which is where Mathlib states the universal property it rests on. That costs nothing here
only because of the smallness assumption made for this statement: with `[SmallCategory.{u} C]`
the hom universe is `u`, so the ring universe is the one we want.

The resolution itself is the colimit of 077J's ladder, and each clause of 06YS is one
property of that ladder pushed through a library result: K-flatness of each stage by
`kFlat_of_isStrictlyLE` from the flat terms, K-flatness of the colimit by
`kFlat_of_isColimit`, flatness of the terms of the colimit by
  `Stacks.SheafOfModules.FlatCoproduct.isFlat_colimit`,
the quasi-isomorphism directly from the ladder, and termwise surjectivity from the ladder's
termwise surjectivity composed with `CochainComplex.epi_ιTruncLE_f_of_lt` — the inclusion of
`τ_{≤ n+1} G` is a degreewise epimorphism in every degree below `n + 1`, and `i.toNat` is such
a degree for any `i`.

The two hypotheses `hF` and `hexact` of 06YQ's criteria are discharged once each, as the two
private lemmas below. `hF` is immediate: `Mod(O)` is monoidal closed, so `X ⊗_O -` is a left
adjoint, which is `preservesColimitsOfSize_sheafTensor_obj`. `hexact` is
`CochainComplex.KFlat.acyclic_colimit` transported from `colimit E` to an arbitrary colimit
cocone along `coconePointUniqueUpToIso`.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.KFlatResolution

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

/-- Flatness of `O`-modules is invariant under isomorphism. -/
private theorem isFlat_of_iso_of_isFlat
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)} (e : N ≅ M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M := by
  rw [Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u}] at hN ⊢
  exact (exactFunctor _ _).prop_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.mapIso e) hN

/-- **A direct sum of extensions by zero of the structure sheaves is flat**, by 03EU. This is
exactly the property the terms of 077J's ladder have. -/
theorem isFlat_of_isSumOfExtensionByZeroStructureSheaves
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
    (hM : Stacks.DerivedTensor.ResolutionByExtensionsByZero.IsSumOfExtensionByZeroStructureSheaves R
      M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M := by
  obtain ⟨ι, U, ⟨e⟩⟩ := hM
  have hsum : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
      (∐ fun i : ι ↦ (SheafOfModules.extensionByZero
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) (U i)).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).over (U i))))
            :=
    Stacks.SheafOfModules.FlatCoproduct.isFlat_coproduct.{u, u} _ (fun i ↦
      Stacks.SheafOfModules.FlatTensorShortExact.isFlat_extensionByZero_unit R (U i))
  exact isFlat_of_iso_of_isFlat R e hsum

/-- **A flat module placed in a single degree gives a K-flat complex.** This is the hook
`StacksTag06YQ`'s base case `kFlat_single_of_exact` leaves open for `⊗_O`: its hypothesis is
that `· ⊗_O M` carries acyclic complexes to acyclic ones, and for a flat `M` that functor is
exact, so `HomologicalComplex.Acyclic.map` supplies it. The row complex of 06YQ is by `rfl`
the termwise application of `· ⊗_O M`, so nothing has to be transported. -/
theorem kFlat_single_of_isFlat
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M) (q : ℤ) :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M) := by
  obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff _).1
    ((Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u} R M).1 hM)
  refine CochainComplex.KFlatBifunctor.kFlat_single_of_exact _ M q (fun G hG ↦ ?_)
  exact HomologicalComplex.Acyclic.map
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj M) hG

/-- `X ⊗_O -` commutes with sequential colimits: `Mod(O)` is monoidal closed, so it is a left
adjoint. This is the hypothesis `hF` of 06YQ's K-flatness criteria. -/
lemma hF_sheafTensor :
    ∀ X : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R),
      PreservesColimitsOfShape ℕ
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj X) :=
  fun _ ↦ ⟨fun {_} ↦ inferInstance⟩

/-- A sequential colimit of acyclic complexes of `O`-modules is acyclic, stated at an
arbitrary colimit cocone. This is the hypothesis `hexact` of 06YQ's K-flatness criteria. -/
lemma hexact_sheafOfModules :
    ∀ (E : ℕ ⥤ CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
      (s : Cocone E), IsColimit s → (∀ i, (E.obj i).Acyclic) → s.pt.Acyclic := by
  intro E s hs hE n
  exact (CochainComplex.KFlat.acyclic_colimit E hE n).of_iso
    ((colimit.isColimit E).coconePointUniqueUpToIso hs)

/-- **A sequential colimit of bounded above complexes of flat `O`-modules is K-flat**: each
stage is K-flat by 06YQ and K-flatness passes to the colimit. -/
theorem kFlat_colimit_of_isStrictlyLE_of_isFlat
    (D : ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      R)) ℤ)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
      ((D.obj n).X i)) :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (colimit D) := by
  refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit _ (colimit.cocone D)
    (colimit.isColimit _) (hF_sheafTensor R) (hexact_sheafOfModules R) (fun n ↦ ?_)
  obtain ⟨b, hb⟩ := hLE n
  have := hb
  exact CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ (D.obj n) b
    (hF_sheafTensor R) (hexact_sheafOfModules R)
    (fun q ↦ kFlat_single_of_isFlat R _ (hflat n q) q)

/-- **The terms of a sequential colimit of complexes with flat terms are flat**, by 03EU:
evaluation in a degree commutes with the colimit. -/
theorem isFlat_colimit_X
    (D : ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      R)) ℤ)
    (hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
      ((D.obj n).X i))
    (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) ((colimit D).X i) := by
  have : HasExactColimitsOfShape ℕ
      (SheafOfModules.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :=
    (inferInstance : HasExactColimitsOfShape ℕ
      (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)))
  have hcol := Stacks.SheafOfModules.FlatCoproduct.isFlat_colimit.{u, u} (O := R)
    (D ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) i) (fun n ↦ hflat n i)
  exact isFlat_of_iso_of_isFlat R
    (preservesColimitIso (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) D).symm hcol

/-- **The resolution of 06YS, presented as a sequential colimit.** Every complex of
`O`-modules receives a termwise surjective quasi-isomorphism from the colimit of a sequence
of bounded above complexes of flat `O`-modules.

This is the shape of the resolution that the derived pullback needs (Tag 0G7E): what makes
the pullback of the resolution K-flat is not K-flatness of the resolution itself — which does
not transport along a functor — but the presentation of the resolution as a colimit of
bounded above complexes with flat terms, each clause of which does transport. -/
theorem exists_resolution_colimit
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
      :
    ∃ (D : ℕ ⥤ CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ) (f : colimit D
          ⟶ G),
      (∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b) ∧
      (∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
        ((D.obj n).X i)) ∧
      QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  obtain ⟨L⟩ :=
    Stacks.DerivedTensor.ResolutionByExtensionsByZero.exists_resolutionByDirectSumsExtensionsByZero
      R G
  refine ⟨L.system, L.colimitComparison, L.boundedAbove, ?_, L.colimit_quasiIso, ?_⟩
  · exact fun n i ↦
      isFlat_of_isSumOfExtensionByZeroStructureSheaves R _ (L.term_isSum n i)
  · intro i
    have hlt : i < ((i.toNat + 1 : ℕ) : ℤ) := by
      have := Int.self_le_toNat i
      push_cast
      omega
    have h1 : Epi ((L.toTruncation i.toNat).f i) := L.epi_f i.toNat i
    have h2 : Epi ((G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i) :=
      G.epi_ιTruncLE_f_of_lt _ i hlt
    have hfac : (colimit.ι L.system i.toNat).f i ≫ L.colimitComparison.f i
        = (L.toTruncation i.toNat).f i ≫ (G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i :=
      congrArg (fun φ ↦ φ.f i) (L.colimitComparison_fac i.toNat)
    have h3 : Epi ((L.toTruncation i.toNat).f i ≫
        (G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i) := epi_comp _ _
    exact epi_of_epi_fac hfac

/-- **Stacks Tag 06YS.** Every complex of `O`-modules on a ringed site admits a termwise
surjective quasi-isomorphism from a K-flat complex whose terms are flat: the colimit of the
ladder of 077J. -/
@[stacks 06YS]
theorem exists_kFlatResolution
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
      :
    ∃ (K : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ) (f : K ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) (K.X i)) ∧
      QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  obtain ⟨D, f, hLE, hflat, hqis, hepi⟩ := exists_resolution_colimit R G
  exact ⟨colimit D, f, kFlat_colimit_of_isStrictlyLE_of_isFlat R D hLE hflat,
    isFlat_colimit_X R D hflat, hqis, hepi⟩

end Stacks.SheafOfModules.KFlatResolution

end
