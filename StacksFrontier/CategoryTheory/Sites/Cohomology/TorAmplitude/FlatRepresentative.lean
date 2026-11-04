module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatCokernel
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Tor amplitude in `[a, b]` is a bounded flat representative, on a ringed site

Stacks 08G1 characterises Tor amplitude in `[a, b]` of an object of `D(O)` on a ringed site by
the existence of a representative which is a complex of flat `O`-modules concentrated in
`[a, b]`. This file proves both directions and the equivalence.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative`: an object
  of `D(O)` represented by a complex of flat `O`-modules which vanishes outside `[a, b]` has Tor
  amplitude in `[a, b]`.
* `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit`: the structure sheaf, viewed as a
  module over itself, is flat.
* `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero`: a zero `O`-module is flat.
* `Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_of_hasTorAmplitude`,
  `Stacks.SheafOfModules.DerivedTensorProduct.isGE_of_hasTorAmplitude` and
  `Stacks.SheafOfModules.DerivedTensorProduct.isLE_of_hasTorAmplitude`: Tor amplitude in
  `[a, b]` bounds the cohomology of the object itself to `[a, b]`.
* `Stacks.SheafOfModules.DerivedTensorProduct.exists_flatRepresentative_of_hasTorAmplitude`: the
  converse, which produces the representative.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_iff_exists_flatRepresentative`:
  **Stacks 08G1**, the equivalence.

## Implementation notes

The mathematical content is one line of the source and one general lemma. The line is that the
representative `K` is K-flat: it is bounded above and has flat terms, which is Stacks 06YQ on a
ringed site. K-flatness of the *left* factor alone is what
`Stacks.SheafOfModules.DerivedTensorProduct.comparisonLeft` asks for, so the derived tensor
product with the module `F[0]` is computed by the ordinary total tensor complex
`Tot(K ⊗_O F[0])` with no resolution of `F[0]` and no naturality square. The general lemma is the
support bound `CochainComplex.KFlatBifunctor.isZero_homology_mapBifunctor_single`: that total
complex has no cohomology in a degree where `K` vanishes. Both are stated for an arbitrary
bifunctor between abelian categories, so the ringed-space form of this result and this one are
two applications of the same lemma.

The hypothesis `hzero` writes the complement of the interval as `i ∉ Set.Icc a b`, as
`Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude` does, so that no translation happens
inside the proof; the two are related by `omega` at the single point where a
`CochainComplex.IsStrictlyLE` bound is produced.

All four universes are free in that direction, as for the Tor-amplitude predicate itself: the
statement is made against a given derived tensor product datum `T`.

The converse direction is the source's argument. Tensoring with the structure sheaf is the
identity, `Stacks.SheafOfModules.DerivedTensorProduct.unitIso`, so Tor amplitude in `[a, b]`
already bounds the object itself: it is `IsGE a` and `IsLE b`. Hence it is the image of a
complex which is strictly `LE b`, and `CochainComplex.exists_quasiIso_prop` resolves that
complex by one which is termwise flat and still strictly `LE b` — flat modules cover, by Stacks
03EW. That resolution `P` need not vanish below `a`, and the truncation `P.truncGE a` is the
required representative: its terms above `a` are those of `P`, its term in degree `a` is
`P.opcycles a`, the cokernel of `d^{a-1}`, which is flat by Stacks 08G0, and its terms below `a`
are zero. The source instead walks down from the top of a bounded above flat complex, replacing
it by `τ_{≤ n-1}` while `n > b`; the truncation at `a` reaches the same complex in one step, the
flatness of the new term in degree `a` being exactly Stacks 08G0.

All four universes are free in that direction too. The unit law it uses is
`Stacks.SheafOfModules.sheafTensorUnitNatIsoFreeSections`, which identifies `F ⊗_O O` with `F`
through the right unitor of *presheaves* of modules and the counit of the sheafification
adjunction, neither of which restricts the universe of the sections; the monoidal structure on
`Mod(O)` of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensor.lean`, which does
need `w = max u v` because its localizing class is shown monoidal through the internal hom, is
not used. `Mod(O)` being abelian at a free `w` is what the `HasSheafify` hypothesis is for.

## References

* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 08G0](https://stacks.math.columbia.edu/tag/08G0)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

-- The sections universe `w` is free, so Mathlib's size-restricted instances do not supply the
-- sheaf-condition composition that `AlgebraicGeometry.SheafOfModules.IsFlat` is stated through.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Stacks 08G1, the direction that needs no converse input.** An object of `D(O)` represented
by a complex of flat `O`-modules which vanishes in every degree outside `[a, b]` has Tor
amplitude in `[a, b]`. -/
theorem hasTorAmplitude_of_flatRepresentative (T : DerivedTensorProduct.{u, v, w, d} X)
    (E : RingedSite.DerivedModules.{u, v, w, d} X) (a b : ℤ)
    (K : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ)
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O) (K.X i))
    (hzero : ∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K.X i))
    (e : DerivedCategory.Q.obj K ≅ E) :
    HasTorAmplitude T E a b := by
  have hKLE : K.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hzero i (by simp only [Set.mem_Icc]; omega)
  have hKflat := Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O K ⟨b, hKLE⟩ hflat
  intro F i hi
  have hz0 :=
    CochainComplex.KFlatBifunctor.isZero_homology_mapBifunctor_single
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) K F i (hzero i hi)
  have hE := ((T.tensor.mapIso e).app _).symm ≪≫ T.comparisonLeft K
    ((HomologicalComplex.single (RingedSite.Modules.{u, v, w} X) (ComplexShape.up ℤ) 0).obj F)
    hKflat
  exact (hz0.of_iso ((DerivedCategory.homologyFunctorFactors _ i).app _)).of_iso
    ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).mapIso hE)

section BoundedRepresentative

variable {Y : RingedSite.{u, v, w}}
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The structure sheaf is a flat `O`-module**: tensoring with it is the identity functor of
`Mod(O)`, which is exact.

This is the unit law `Stacks.SheafOfModules.sheafTensorUnitNatIsoFreeSections`, read through the
definition of flatness. -/
theorem isFlat_unit :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O)
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  Stacks.SheafOfModules.isFlat_of_exactFunctor_sheafTensorFlip Y.O _
    ((exactFunctor _ _).prop_of_iso
      (Stacks.SheafOfModules.sheafTensorUnitNatIsoFreeSections Y.O).symm
      (by rw [exactFunctor_iff]; exact ⟨inferInstance, inferInstance⟩))

/-- The kernel of the identity of the structure sheaf — a zero `O`-module — is flat: it sits in
a short exact sequence whose other two terms are the flat structure sheaf, so Stacks 03EY (2)
applies. -/
theorem isFlat_kernel_id_unit :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O)
      (kernel (𝟙 (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) :=
  Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact Y.O
    (ShortComplex.mk
      (kernel.ι (𝟙 (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
      (𝟙 (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
      (kernel.condition _))
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
    isFlat_unit isFlat_unit

/-- **A zero `O`-module is flat.** Every zero object is isomorphic to the kernel of the identity
of the structure sheaf, which is flat. -/
theorem isFlat_of_isZero (M : RingedSite.Modules.{u, v, w} Y) (hM : IsZero M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) M :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_iso Y.O
    (IsZero.iso (isZero_kernel_of_mono (𝟙 (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) hM)
    isFlat_kernel_id_unit

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **Tor amplitude bounds the cohomology of the object itself.** If `E` has Tor amplitude in
`[a, b]` then its cohomology vanishes in every degree outside `[a, b]`: tensoring with the
structure sheaf in degree zero is the identity, so `E` is one of the objects the Tor-amplitude
hypothesis speaks about. -/
theorem isZero_homology_of_hasTorAmplitude (T : DerivedTensorProduct.{u, v, w, d} Y)
    (E : RingedSite.DerivedModules.{u, v, w, d} Y) {a b i : ℤ}
    (hamp : HasTorAmplitude T E a b) (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} Y) i).obj E) :=
  (hamp (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) i hi).of_iso
    ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} Y) i).mapIso
      (T.unitIso E).symm)

/-- An object of Tor amplitude in `[a, b]` has no cohomology below `a`. -/
theorem isGE_of_hasTorAmplitude (T : DerivedTensorProduct.{u, v, w, d} Y)
    (E : RingedSite.DerivedModules.{u, v, w, d} Y) {a b : ℤ}
    (hamp : HasTorAmplitude T E a b) : E.IsGE a := by
  rw [DerivedCategory.isGE_iff]
  exact fun i hi => isZero_homology_of_hasTorAmplitude T E hamp
    (by simp only [Set.mem_Icc]; omega)

/-- An object of Tor amplitude in `[a, b]` has no cohomology above `b`. -/
theorem isLE_of_hasTorAmplitude (T : DerivedTensorProduct.{u, v, w, d} Y)
    (E : RingedSite.DerivedModules.{u, v, w, d} Y) {a b : ℤ}
    (hamp : HasTorAmplitude T E a b) : E.IsLE b := by
  rw [DerivedCategory.isLE_iff]
  exact fun i hi => isZero_homology_of_hasTorAmplitude T E hamp
    (by simp only [Set.mem_Icc]; omega)

/-- **Stacks 08G1, the direction producing the representative.** An object of `D(O)` with Tor
amplitude in `[a, b]` is the image of a complex of flat `O`-modules vanishing in every degree
outside `[a, b]`.

A flat resolution `P` of a strictly `LE b` representative is truncated at `a`; the only term
that changes is the one in degree `a`, which becomes `Coker(d_P^{a-1})`, flat by Stacks 08G0. -/
theorem exists_flatRepresentative_of_hasTorAmplitude
    (T : DerivedTensorProduct.{u, v, w, d} Y)
    (E : RingedSite.DerivedModules.{u, v, w, d} Y) (a b : ℤ) (hab : a ≤ b)
    (hamp : HasTorAmplitude T E a b) :
    ∃ K : CochainComplex (RingedSite.Modules.{u, v, w} Y) ℤ,
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w}
        (O := Y.O) (K.X i)) ∧
      (∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K.X i)) ∧
      Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  have hEGE : E.IsGE a := isGE_of_hasTorAmplitude T E hamp
  have hELE : E.IsLE b := isLE_of_hasTorAmplitude T E hamp
  obtain ⟨M, hMLE, ⟨eM⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E b
  let Pflat : ObjectProperty (RingedSite.Modules.{u, v, w} Y) := fun F =>
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) F
  have _ : Pflat.ContainsZero :=
    ⟨⟨kernel (𝟙 (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))), isZero_kernel_of_mono _,
        isFlat_kernel_id_unit⟩⟩
  have hcover : ∀ F : RingedSite.Modules.{u, v, w} Y,
      ∃ (G : RingedSite.Modules.{u, v, w} Y) (_ : Pflat G) (f : G ⟶ F), Epi f := by
    intro F
    obtain ⟨G, f, hG, hf⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat Y.O F
    exact ⟨G, hG, f, hf⟩
  obtain ⟨P, f, -, hf, hPflat, hPLE⟩ :=
    (CochainComplex.exists_quasiIso_prop Pflat hcover b).1 M
  have eP : DerivedCategory.Q.obj P ≅ E := asIso (DerivedCategory.Q.map f) ≪≫ eM.symm
  have hPGE : P.IsGE a :=
    (DerivedCategory.isGE_Q_obj_iff P a).1 (DerivedCategory.TStructure.t.isGE_of_iso eP.symm a)
  have hPamp : HasTorAmplitude T (DerivedCategory.Q.obj P) a b := fun F i hi =>
    (hamp F i hi).of_iso
      ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} Y) i).mapIso
        ((T.tensor.mapIso eP).app
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} Y) 0).obj F)))
  have hCoker := isFlat_cokernel_of_hasTorAmplitude T P a b ⟨b, hPLE⟩ hPflat hPamp
  have eOpCoker : P.opcycles a ≅
      (cokernel (P.d (a - 1) a) : RingedSite.Modules.{u, v, w} Y) :=
    IsColimit.coconePointUniqueUpToIso
      (P.opcyclesIsCokernel (a - 1) a (by simp)) (colimit.isColimit _)
  have hTruncFlat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w}
      (O := Y.O) ((P.truncGE a).X i) := by
    intro i
    rcases lt_trichotomy i a with hlt | heq | hgt
    · exact isFlat_of_isZero _ ((P.truncGE a).isZero_of_isStrictlyGE a i hlt)
    · rw [heq]
      exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso Y.O
        (eOpCoker.symm ≪≫ (P.truncGEXIsoOpcycles a).symm) hCoker
    · exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso Y.O
        (P.truncGEXIso a i hgt).symm (hPflat i)
  have hTruncLE : (P.truncGE a).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => (P.isZero_of_isStrictlyLE b i hi).of_iso (P.truncGEXIso a i (by omega))
  refine ⟨P.truncGE a, hTruncFlat, ?_,
    ⟨(asIso (DerivedCategory.Q.map (P.πTruncGE a))).symm ≪≫ eP⟩⟩
  intro i hi
  rcases (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi : i < a ∨ b < i) with
    hlt | hgt
  · exact (P.truncGE a).isZero_of_isStrictlyGE a i hlt
  · exact (P.truncGE a).isZero_of_isStrictlyLE b i hgt

/-- **Stacks 08G1.** An object of `D(O)` has Tor amplitude in `[a, b]` exactly when some complex
of flat `O`-modules vanishing in every degree outside `[a, b]` represents it. -/
@[stacks 08G1, sga "4 XVII 4.1.9" "(i) <=> (iii)", sga "6 I 5.1"]
theorem hasTorAmplitude_iff_exists_flatRepresentative
    (T : DerivedTensorProduct.{u, v, w, d} Y)
    (E : RingedSite.DerivedModules.{u, v, w, d} Y) (a b : ℤ) (hab : a ≤ b) :
    HasTorAmplitude T E a b ↔
      ∃ K : CochainComplex (RingedSite.Modules.{u, v, w} Y) ℤ,
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w}
          (O := Y.O) (K.X i)) ∧
        (∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K.X i)) ∧
        Nonempty (DerivedCategory.Q.obj K ≅ E) where
  mp hamp := exists_flatRepresentative_of_hasTorAmplitude T E a b hab hamp
  mpr := fun ⟨K, hflat, hzero, ⟨e⟩⟩ =>
    hasTorAmplitude_of_flatRepresentative T E a b K hflat hzero e

end BoundedRepresentative

end Stacks.SheafOfModules.DerivedTensorProduct

end
