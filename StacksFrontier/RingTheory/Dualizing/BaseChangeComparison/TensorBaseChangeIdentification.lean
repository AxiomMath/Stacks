module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeBridge
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeStrong

/-!
# The keystone obligation as a single identification of two morphisms

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeBridge` reduces the
chapter's keystone to the equation `hg` of `Dualizing.isIso_derivedTensorBaseChange_of_unit`,
an equation between two morphisms of `D(R)` obtained by transposing twice.  This file records
that `hg` says nothing more than that its morphism **is** the lax monoidal structure map
`Dualizing.derivedTensorBaseChange`, and that this in turn is one equation between morphisms of
`D(A)` with no transpose on either side:

`homEquiv⁻¹ g = F (coev) ≫ (base change of derived Hom)`,

the coevaluation being the one of [stacks 0A63] over `R` and the second factor the morphism of
[stacks 0E1X] at `(Y, X ⊗ᴸ_R Y)`.

Nothing here is new mathematics: the closed formula
`Dualizing.derivedTensorBaseChange_eq` already presents the lax structure map as the transpose of
that composite, so the content is that the double transpose of
`Dualizing.unit_comp_homEquiv_symm_derivedTensorBaseChange` can be undone.  What it buys is that
two of the shapes in which the obligation has been stated in this directory — the equation `hg`
and the identification of the [stacks 068I] morphism `Dualizing.tensorBaseChangeMor` with `μ` —
are the *same* equation up to the choice of the morphism `g`, so a proof of either, in any model,
discharges the other.  Those equivalences are the `Iff`s proved below.

`Dualizing.TensorComparisonCompatibility` is **not** among them.  It is not the same statement:
its second argument is fixed to
`Dualizing.derivedAlgebraSingle` rather than ranging over a second object, and it is phrased with
`Dualizing.tensorComparisonOfIso` — two projection formulas, `derivedBaseChangeSquareIso` and
[stacks 0661] — in place of the [stacks 068I] morphism.  Since
`Dualizing.kFlatAlgebraActionEq_of_tensorComparisonCompatibility` consumes
`TensorComparisonCompatibility` and nothing else, a proof of the equations below leaves a bridge
to be written before the tags depending on `Dualizing.KFlatAlgebraActionEq` are released.

That bridge is written, in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonBaseChangeMor`.  What
the identification leaves is one equation and no more:
`Dualizing.tensorComparisonCompatibility_iff_tensorBaseChangeMor` says that granted
`Dualizing.tensorBaseChangeMor_eq_iff` at `(X, A[0])`, the obligation at `X` *is*

`μ' ≫ tensorComparisonOfIso X = 𝟙 ⊗ derivedBaseChangeAlgebraIso`,

in which no component of [stacks 0E1W], no morphism of [stacks 0E1X], neither `μ` nor `ν` and no
transpose occurs; and `Dualizing.tensorBaseChangeMor_eq_iff_tensorComparisonCompatibility` says
that granted that equation, the obligation *is* the identification.  So the two are jointly
equivalent to the obligation, and the equations below are a step towards it that leaves exactly
one [stacks 0E1W]-free equation behind.

## Main results

* `Dualizing.eq_derivedTensorBaseChange_iff` — a morphism is the lax monoidal structure map
  exactly when its transpose over [stacks 0A63] is `F` applied to the coevaluation followed by
  the base-change morphism of [stacks 0E1X].
* `Dualizing.unit_comp_homEquiv_symm_iff` — the equation `hg` of
  `Dualizing.isIso_derivedTensorBaseChange_of_unit` holds for a morphism exactly when that
  morphism is the lax monoidal structure map.
* `Dualizing.tensorBaseChangeMor_eq_iff` — the keystone in the [stacks 068I] shape: the
  monoidality isomorphism of [stacks 068I] is `μ` exactly when the transposed identity holds.
* `Dualizing.tensorBaseChangeMor_eq_of_kFlat` — the keystone has to be checked only at pairs of
  K-flat complexes: both sides are natural in both variables and every object of `D(R)` is the
  localization of a K-flat complex up to isomorphism.

## Implementation notes

The `Prop`-valued hypothesis `hg` of `Dualizing.isIso_derivedTensorBaseChange_of_unit` is
restated here rather than abbreviated, so that the equivalence is stated at exactly the
proposition that theorem consumes.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

/-- **Every object of the derived category of modules is the localization of a K-flat complex, up
to isomorphism.**  `CategoryTheory.Functor.EssSurj` holds for `DerivedCategory.Q`, and the K-flat
resolution of [stacks 06Y4] supplied by `CochainComplex.KFlat.exists_kFlat_resolution` is a
quasi-isomorphism, hence invertible after localization. -/
theorem exists_kFlat_iso {R : Type uR} [CommRing R]
    (X : DerivedCategory (ModuleCat.{max uR uM} R)) :
    ∃ K : CochainComplex (ModuleCat.{max uR uM} R) ℤ,
      K.KFlat ∧ Nonempty (X ≅ DerivedCategory.Q.obj K) := by
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := DerivedCategory.Q (C := ModuleCat.{max uR uM} R)) X
  obtain ⟨K, q, hK, -, hq, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{uR, uM} M
  have : IsIso (DerivedCategory.Q.map q) := inferInstance
  exact ⟨K, hK, ⟨e.symm ≪≫ (asIso (DerivedCategory.Q.map q)).symm⟩⟩

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

/-- **A morphism is the lax monoidal structure map of derived base change exactly when its
transpose is the coevaluation followed by the base-change morphism of [stacks 0E1X].**  This is
the closed formula `Dualizing.derivedTensorBaseChange_eq` with the transpose moved to the other
side, and it is the shape of the keystone obligation that carries no transpose. -/
theorem eq_derivedTensorBaseChange_iff
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (g : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
        (F.obj X, F.obj Y) ⟶
      F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        (X, Y))) :
    g = derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
          (F.obj X) (F.obj Y)
          (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y)))).symm g =
        F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensorHomUnit X Y) ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison Y
            ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.obj (X, Y)) := by
  rw [derivedTensorBaseChange_eq.{uR, uA, uM} f F comparison X Y]
  exact (Equiv.symm_apply_eq _).symm

/-- **The equation `hg` of `Dualizing.isIso_derivedTensorBaseChange_of_unit` says exactly that
its morphism is the lax monoidal structure map of derived base change.**  One direction is
`Dualizing.eq_derivedTensorBaseChange_of_unit` and the other is
`Dualizing.unit_comp_homEquiv_symm_derivedTensorBaseChange`. -/
theorem unit_comp_homEquiv_symm_iff
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (g : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
        (F.obj X, F.obj Y) ⟶
      F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        (X, Y))) :
    ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
          (((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv (F.obj
              X) (F.obj Y)
              (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1}
                  R).tensor.obj (X, Y)))).symm g) =
      ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj
                ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
                    (X, Y))))).symm
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
              ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj (X,
                  Y))) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).hom.app
          (Opposite.op Y, F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1}
              R).tensor.obj (X, Y)))) ↔
      g = derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y := by
  constructor
  · exact eq_derivedTensorBaseChange_of_unit.{uR, uA, uM} f F comparison X Y g
  · intro h
    rw [h]
    exact unit_comp_homEquiv_symm_derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y

/-- **A morphism is the lax monoidal structure map of derived base change exactly when the
canonical section of [stacks 0E1W] is a section of it.**  The two-sided inverse
`Dualizing.derivedTensorBaseChangeSection` of `Dualizing.derivedTensorBaseChange` has the property
that precomposition with it is injective
(`Dualizing.derivedTensorBaseChangeSection_comp_injective`), so a morphism with the same composite
as the lax structure map is the lax structure map.

This is the shape of the obligation that carries no transpose, no unit of [stacks 0GMT] and no
`homEquiv` of [stacks 0A63]: it is one composite of two morphisms of `D(A)` against the identity.
Compare `Dualizing.eq_derivedTensorBaseChange_iff`, which pays for the absence of the unit with a
transpose, and `Dualizing.unit_comp_homEquiv_symm_iff`, which pays with both. -/
theorem eq_derivedTensorBaseChange_iff_section_comp
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (g : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
        (F.obj X, F.obj Y) ⟶
      F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        (X, Y))) :
    g = derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫ g = 𝟙 _ := by
  have hsec := derivedTensorBaseChangeSection_comp_derivedTensorBaseChange.{uR, uA, uM} f F
    comparison X Y
  exact ⟨fun h => h ▸ hsec, fun h => derivedTensorBaseChangeSection_comp_injective.{uR, uA, uM}
    f F comparison X Y _ (h.trans hsec.symm)⟩

variable (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
    max uR uA uM + 1} f)

/-- **The keystone in the [stacks 068I] shape.**  The monoidality isomorphism of [stacks 068I],
read in the vocabulary of [stacks 0A63] by `Dualizing.tensorBaseChangeMor`, is the lax monoidal
structure map of derived base change exactly when its transpose over [stacks 0A63] is `F` applied
to the coevaluation followed by the base-change morphism of [stacks 0E1X].

Since `Dualizing.tensorBaseChangeMor` is invertible, this identification is the equation whose
proof would make the keystone's conclusion unconditional; by
`Dualizing.unit_comp_homEquiv_symm_iff` it is the hypothesis `hg` of
`Dualizing.isIso_derivedTensorBaseChange_of_unit` at that morphism. -/
theorem tensorBaseChangeMor_eq_iff (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
        derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
          (F.obj X) (F.obj Y)
          (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y)))).symm
          (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y) =
        F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensorHomUnit X Y) ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison Y
            ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.obj (X, Y)) :=
  eq_derivedTensorBaseChange_iff.{uR, uA, uM} f F comparison X Y _

/-- **The keystone in the [stacks 068I] shape, with no transpose on either side.**  The
monoidality isomorphism of [stacks 068I], read in the vocabulary of [stacks 0A63] by
`Dualizing.tensorBaseChangeMor`, is the lax monoidal structure map of derived base change exactly
when `Dualizing.derivedTensorBaseChangeSection` is a section of it.

This is `Dualizing.eq_derivedTensorBaseChange_iff_section_comp` at the [stacks 068I] morphism, and
it is the smallest shape the obligation has been reduced to: an equation `ν ≫ μ' = 𝟙` between
endomorphisms of `F X ⊗ᴸ_A F Y`, with `ν` the two-sided inverse of
`Dualizing.derivedTensorBaseChange` supplied by
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeStrong` and `μ'` the
[stacks 068I] candidate, which `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral_hom_app_kFlat`
and the field `CochainComplex.DerivedTensor.DerivedExtensionScalarsTensorIso.comparison` pin down
on a pair of K-flat complexes.  Neither the unit of [stacks 0GMT] nor the `homEquiv` of
[stacks 0A63] occurs. -/
theorem tensorBaseChangeMor_eq_iff_section_comp
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
        derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫
        tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y = 𝟙 _ :=
  eq_derivedTensorBaseChange_iff_section_comp.{uR, uA, uM} f F comparison X Y _

/-- **The [stacks 068I] identification transports along isomorphisms of both arguments.**  Both
`Dualizing.tensorBaseChangeMor` and `Dualizing.derivedTensorBaseChange` are natural in both
variables — the first as a component of `Dualizing.tensorBaseChangeNatIso`, the second by
`Dualizing.derivedTensorBaseChange_naturality` — and the morphism of `D(A)` the two naturality
squares are postcomposed with is `F` applied to the image of an isomorphism of the product
category, hence invertible. -/
theorem tensorBaseChangeMor_eq_of_iso
    {X Y X' Y' : DerivedCategory (ModuleCat.{max uR uA uM} R)} (a : X ≅ X') (b : Y ≅ Y')
    (h : tensorBaseChangeMor.{uR, uA, uM} f F comparison D X' Y' =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison X' Y') :
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y := by
  have hmu := derivedTensorBaseChange_naturality.{uR, uA, uM} f F comparison a.hom b.hom
  have hmu' : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.map
          ((F.map a.hom, F.map b.hom) : (F.obj X, F.obj Y) ⟶ (F.obj X', F.obj Y')) ≫
        tensorBaseChangeMor.{uR, uA, uM} f F comparison D X' Y' =
      tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y ≫
        F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.map ((a.hom, b.hom) : (X, Y) ⟶ (X', Y'))) :=
    (tensorBaseChangeNatIso.{uR, uA, uM} f F comparison D).hom.naturality
      ((a.hom, b.hom) : ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
        DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶ (X', Y'))
  have : IsIso (F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.map ((a.hom, b.hom) : (X, Y) ⟶ (X', Y')))) :=
    inferInstanceAs (IsIso (F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.map (a.prod b).hom)))
  refine (cancel_mono (F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.map ((a.hom, b.hom) : (X, Y) ⟶ (X', Y'))))).1 ?_
  rw [← hmu, ← hmu', h]

/-- **The keystone has to be checked only at pairs of K-flat complexes.**  Granted the
identification of the [stacks 068I] morphism with the lax monoidal structure map at every pair of
localizations of K-flat complexes, it holds at every pair of objects of `D(R)`.

This is `Dualizing.tensorBaseChangeMor_eq_of_iso` at the representatives supplied by
`Dualizing.exists_kFlat_iso`.  It is the shape in which the two sides are pinned down: the
[stacks 068I] side by `CochainComplex.DerivedTensor.DerivedExtensionScalarsTensorIso.comparison`
together with `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral_hom_app_kFlat`, and the unit of
[stacks 0GMT] occurring in the lax structure map by
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat`,
both of which ask for a K-flat complex. -/
theorem tensorBaseChangeMor_eq_of_kFlat
    (h : ∀ K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ, K.KFlat → L.KFlat →
      tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L) =
        derivedTensorBaseChange.{uR, uA, uM} f F comparison (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L))
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y := by
  obtain ⟨K, hK, ⟨a⟩⟩ := exists_kFlat_iso.{uR, max uA uM} X
  obtain ⟨L, hL, ⟨b⟩⟩ := exists_kFlat_iso.{uR, max uA uM} Y
  exact tensorBaseChangeMor_eq_of_iso.{uR, uA, uM} f F comparison D a b (h K L hK hL)

end Dualizing

end
