module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.Cotangent.AtiyahClassBigSiteDiagram
import StacksCore.Tactic.StacksAttribute

/-!
# The Atiyah triangle and the Atiyah class at the site `C_{B/A}` itself

[Stacks, Tag 09DD] displays its triangle with both endpoints identified:

`L_{B/A} ⊗^𝐋_B M ⟶ Lπ_!(P¹_{𝒪/A}(M)) ⟶ M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]`,

and [Tag 09DE] calls the last arrow `M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]` the *Atiyah class* of `M`,
whereas the triangle as `StacksFrontier/Cotangent/AtiyahClass.lean` constructs it has endpoints
`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲)` and `Lπ_!(M̲)`. At the site `C_{B/A}` of [Stacks, Tag 08PR] itself, read
on its `CategoryTheory.AsSmall` model `CommAlgCat.atiyahSite`, both identifications are now
theorems of this tree, so the displayed triangle and its last arrow can be stated with nothing
assumed. That is what this file does.

* The third term is `CommAlgCat.polynomialAtiyahTriangleObj₃Iso`, which rests on [Tag 08QE] at
  this site (`CommAlgCat.atiyahModuleDerivedInverseImageCompLowerShriekIso`).
* The first term is `CommAlgCat.nonempty_atiyahFirstVertexDerivedTensorIso`, assembled below
  from `CommAlgCat.atiyahFirstVertexMooreIso` (the chain of [Tag 08PT] and [Tag 09CZ] at this
  site), `CommAlgCat.atiyahFirstVertexDiagramIso` (the universe-lift comparison of
  `StacksFrontier/Cotangent/UliftBaseChangedDifferentials.lean`, transported to the site) and
  `CommAlgCat.atiyahMooreTensorIso` ([Tag 08PU] on the standard resolution), together with the
  K-flatness of the universe lift of `L_{B/A}` proved here.

The identification of the first term is available as a `Nonempty`, the choice of a K-flat
resolution inside `Stacks.DerivedTensor.nonempty_derivedTensor_iso_tensor_of_kFlat_right` being
non-canonical, so the displayed triangle is stated existentially in that identification;
membership in `CategoryTheory.Pretriangulated.distinguishedTriangles` is a `Prop`, so nothing is
lost. The identification of the third term is canonical and is named outright.

## Main results

* `CommAlgCat.kFlat_moduleLiftCotangentComplex`: **the universe lift of `L_{B/A}` is K-flat**,
  which is what makes the ordinary tensor product `L_{B/A} ⊗_B M` compute the derived one at the
  coefficients of the site's own ringed point.
* `CommAlgCat.nonempty_atiyahFirstVertexDerivedTensorIso`: **the first term of the Atiyah
  triangle at `C_{B/A}` is `L_{B/A} ⊗^𝐋_B M`**.
* `CommAlgCat.exists_atiyahDisplayedTriangle_distinguished`: **the displayed triangle of
  [Stacks, Tag 09DD] is distinguished**, with its first term `L_{B/A} ⊗^𝐋_B M` and its third
  term `M`.
* `CommAlgCat.exists_atiyahDisplayedClass_mem_distinguished`: **the Atiyah class of `M`,
  `M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]`, is the last arrow of that triangle** — [Stacks, Tag 09DE].

## Implementation notes

**Why K-flatness is proved here and not inherited.** `CommAlgCat.kFlat_cotangentComplex`
(`StacksFrontier/Cotangent/CotangentDerivedTensorModule.lean`) is K-flatness of `L_{B/A}` over `B`
at `Type u` coefficients. The triangle of [Tag 09DD] at the site `C_{B/A}` lives over the ring
`ULift B` of the site's own ringed point `CommAlgCat.polynomialRingedPoint`, so what is needed is
K-flatness of `CommAlgCat.moduleLiftCotangentComplex`, the universe lift. Flatness of its terms
is `Module.Flat.ulift_right_iff` followed by `Module.Flat.of_semilinearEquiv` along
`ULift.ringEquiv`: the `ULift B`-action on the lifted terms is restriction of scalars along that
isomorphism, and `Module.Flat.ulift_left_iff` does not apply to it, being stated for the
`ULift.module'` action instead. The complex still vanishes in positive degrees, by
`CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff`, so [Tag 064K]
(`CochainComplex.KFlat.kFlat_of_flat`) applies, with its universes pinned at `u + 1`.

**Why this is not the small-model statement transported.**
`CommAlgCat.exists_smallAtiyahDisplayedTriangle_distinguished`
(`StacksFrontier/Cotangent/AtiyahClassSmallSiteDisplayed.lean`) proves the same displayed triangle
on the small model of the `κ`-bounded full subcategory of `C_{B/A}`, and nothing transports
between the two. Restricting to a full subcategory of bounded-cardinality augmentations changes
both `Mod(B̲)` and `Lπ_!`, and the inclusion of the small model is only fully faithful
(`CommAlgCat.fullyFaithfulSmallBoundedPolynomialSiteToPolynomialSite`) — the unrestricted site is
recorded as not essentially small — while
`Stacks.CategoryHomology.totalDerivedColimitEquivalenceIso` would need an equivalence.
Independently of the site, the small statement quantifies over `M : ModuleCat.{u} B` and this one
over `M : ModuleCat.{u + 1} (ULift B)`, which is strictly wider, so it could not imply this one
even given a comparison of the sites.

**Why the Atiyah class is not a `def` here.** The displayed class is the arrow already named by
`CommAlgCat.polynomialAtiyahClassOfIso` (`StacksFrontier/Cotangent/AtiyahClass.lean`) — the Atiyah
class `Lπ_!(M̲) ⟶ Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲)[1]` of the triangle, read through identifications of the
two endpoints — instantiated at the displayed endpoints `L := L_{B/A} ⊗^𝐋_B M` and `N := M`,
with `e₃` the canonical `CommAlgCat.polynomialAtiyahTriangleObj₃Iso` and `e₁` an identification
of the first term. No new arrow is defined here, and none should be: `e₁` is available only as a
`Nonempty`, so a closed-form `def` could only pick one by `Classical.choice`, and the resulting
arrow genuinely depends on the pick — two identifications `e₁` and `e₁'` give classes differing
by post-composition with `(e₁.symm ≪≫ e₁').hom⟦1⟧`, a generally non-identity automorphism of
`(L_{B/A} ⊗^𝐋_B M)[1]`. So the class is well defined only up to that automorphism group, and a
`def` would fix a non-canonical choice silently.

Nothing is lost by stating it existentially. Being the last arrow of the displayed distinguished
triangle holds for **every** identification of the first term — that is
`CommAlgCat.polynomialAtiyahClassOfIso_mem_distinguished`, proved for arbitrary `e₁` and `e₃` —
and an identification exists, by
`CommAlgCat.nonempty_atiyahFirstVertexDerivedTensorIso`. The existential in
`CommAlgCat.exists_atiyahDisplayedClass_mem_distinguished` is therefore the conjunction of those
two facts and not a choice of `e₁`: it says the identification exists, and the conclusion is
insensitive to which one it is.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 09DE](https://stacks.math.columbia.edu/tag/09DE)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QE](https://stacks.math.columbia.edu/tag/08QE)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open CochainComplex.DerivedTensor
open Stacks.ChaoticSite.ModuleValued

universe u

namespace CommAlgCat

attribute [local instance 2000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### The universe lift of the cotangent complex is K-flat -/

/-- Each term of the universe lift of `L_{B/A}` is a flat `ULift B`-module. Flatness of the
universe lift over `B` is `Module.Flat.ulift_right_iff`, and the passage to the `ULift B`-action
that restriction of scalars along `ULift.ringEquiv` puts on it is
`Module.Flat.of_semilinearEquiv`. -/
instance flat_moduleLiftCotangentComplex_X (i : ℤ) :
    Module.Flat (ULift.{u + 1} (B : Type u))
      ((moduleLiftCotangentComplex A B).X i) := by
  have hflat : Module.Flat (B : Type u)
      (ULift.{u + 1} ((cotangentComplex.{u, u} A B).X i)) :=
    Module.Flat.ulift_right_iff.2 inferInstance
  exact @Module.Flat.of_semilinearEquiv (ULift.{u + 1} (B : Type u)) (B : Type u)
    (↑((moduleLiftCotangentComplex A B).X i) : Type (u + 1))
    (ULift.{u + 1} ((cotangentComplex.{u, u} A B).X i)) _ _ _ _ _ _ hflat
    (ULift.ringEquiv (R := (B : Type u))) (AddEquiv.refl _) fun _ _ => rfl

/-- The universe lift of `L_{B/A}` vanishes in positive cohomological degrees, because `L_{B/A}`
does and the lift is faithful and preserves zero morphisms. -/
instance isStrictlyLE_moduleLiftCotangentComplex :
    (moduleLiftCotangentComplex A B).IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff (cotangentComplex.{u, u} A B)
    (StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1} (B : Type u)) 0).2 inferInstance

/-- **The universe lift of `L_{B/A}` is K-flat.** It is bounded above by cohomological degree
zero and its terms are flat, which is [Stacks, Tag 064K]. This is the form of
`CommAlgCat.kFlat_cotangentComplex` that the Atiyah triangle at the site `C_{B/A}` needs, the
coefficients there being the ring `ULift B` of the site's own ringed point. -/
theorem kFlat_moduleLiftCotangentComplex :
    CochainComplex.KFlat.{u + 1, u + 1} (moduleLiftCotangentComplex A B) :=
  CochainComplex.KFlat.kFlat_of_flat.{u + 1, u + 1} (moduleLiftCotangentComplex A B) 0

/-! ### The first displayed term -/

variable (M : ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))

/-- `M` placed in cohomological degree zero, at the coefficients of the site's own ringed
point. -/
abbrev atiyahModuleSingleComplex :
    CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))
    (ComplexShape.up ℤ) 0).obj M

/-- **`L_{B/A} ⊗^𝐋_B M`**, the first term of the triangle as [Stacks, Tag 09DD] displays it, at
the coefficients of the site's own ringed point. -/
abbrev atiyahDisplayedObj₁ :
    DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) :=
  ((canonicalDerivedTensorProductFunctor (ULift.{u + 1} (B : Type u))).obj
      (DerivedCategory.Q.obj (moduleLiftCotangentComplex A B))).obj
    (DerivedCategory.Q.obj (atiyahModuleSingleComplex A B M))

/-- **`L_{B/A} ⊗^𝐋_B M` is an ordinary total tensor product**, the universe lift of `L_{B/A}`
being K-flat. This is the step the source calls "the flatness of the terms of `L_{B/A}`", read at
the coefficients of the site's own ringed point. -/
theorem nonempty_moduleLiftCotangentComplexDerivedTensorModule_iso :
    Nonempty (atiyahDisplayedObj₁ A B M ≅
      DerivedCategory.Q.obj (tensorObj (atiyahModuleSingleComplex A B M)
        (moduleLiftCotangentComplex A B))) :=
  (Stacks.DerivedTensor.nonempty_derivedTensor_iso_tensor_of_kFlat_right
      (ULift.{u + 1} (B : Type u)) (atiyahModuleSingleComplex A B M)
      (moduleLiftCotangentComplex A B)
      (kFlat_moduleLiftCotangentComplex A B)).map fun e =>
    derivedTensorProductCommIso _ _ ≪≫ e

/-- **The extended Moore complex of `M ⊗_B i^*Ω_{𝒪/A}` on the standard resolution is
`L_{B/A} ⊗^𝐋_B M`** in `D(B)`, at the site `C_{B/A}` itself. The degreewise computation is
`CommAlgCat.atiyahMooreTensorIso`;
`StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso` turns the
degreewise tensor product into the tensor product of complexes `M[0] ⊗ L_{B/A}`, and
`CommAlgCat.nonempty_moduleLiftCotangentComplexDerivedTensorModule_iso` identifies that with the
derived tensor product. -/
theorem nonempty_atiyahMooreDerivedTensorIso :
    Nonempty (DerivedCategory.Q.obj
        ((mooreCochainComplex (atiyahStandardCosimplicialObject A B)).obj
          (atiyahCotangentModulePresheaf A B ⋙
            StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1} (B : Type u) ⋙
              tensorLeft M)) ≅
      atiyahDisplayedObj₁ A B M) :=
  (nonempty_moduleLiftCotangentComplexDerivedTensorModule_iso A B M).map fun e =>
    DerivedCategory.Q.mapIso (atiyahMooreTensorIso A B M ≪≫
      (StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso
        M (moduleLiftCotangentComplex A B)).symm) ≪≫ e.symm

/-- **The first term of the Atiyah triangle at the site `C_{B/A}` itself is `L_{B/A} ⊗^𝐋_B M`**,
which is the first displayed term of the triangle of [Stacks, Tag 09DD]:

`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲) ≅ L_{B/A} ⊗^𝐋_B M` in `D(B)`.

`CommAlgCat.atiyahFirstVertexMooreIso` computes the vertex as the extended Moore complex of the
`B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})` on the standard resolution,
`CommAlgCat.atiyahFirstVertexDiagramIso` reads that `B̲`-module as the diagram
`M ⊗_B i^*Ω_{𝒪/A}`, and `CommAlgCat.nonempty_atiyahMooreDerivedTensorIso` computes the extended
Moore complex of that diagram to be `L_{B/A} ⊗^𝐋_B M`.

`Nonempty` records the non-canonical choice of a K-flat resolution in the last of the three. -/
theorem nonempty_atiyahFirstVertexDerivedTensorIso :
    Nonempty ((polynomialAtiyahTriangle A B M).obj₁ ≅ atiyahDisplayedObj₁ A B M) :=
  (nonempty_atiyahMooreDerivedTensorIso A B M).map fun e =>
    atiyahFirstVertexMooreIso A B M ≪≫
      DerivedCategory.Q.mapIso
          ((mooreCochainComplex (atiyahStandardCosimplicialObject A B)).mapIso
            (atiyahFirstVertexDiagramIso A B M)) ≪≫
        e

/-! ### The displayed triangle -/

/-- **Stacks 09DD, the displayed triangle.** For a ring map `A → B` and a `B`-module `M` there is
an identification `e₁` of the first term of the Atiyah triangle on the site `C_{B/A}` with
`L_{B/A} ⊗^𝐋_B M` for which

`L_{B/A} ⊗^𝐋_B M ⟶ Lπ_!(P¹_{𝒪/A}(M)) ⟶ M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]`

is a distinguished triangle, the third term being identified with `M` by the canonical
`CommAlgCat.polynomialAtiyahTriangleObj₃Iso`.

Nothing is assumed: the first identification is
`CommAlgCat.nonempty_atiyahFirstVertexDerivedTensorIso`, the chain of [Stacks, Tag 08PT] and
[Tag 08PU] together with the universe-lift comparison of the sections of `B̲ ⊗_𝒪 Ω_{𝒪/A}`, and
the third is [Tag 08QE] through
`Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso`. It is `e₁` that is
existentially quantified rather than named, because the K-flat resolution computing the derived
tensor product is chosen and not canonical. -/
@[stacks 09DD "the displayed triangle `L_{B/A} ⊗^L_B M → Lπ_!(P¹(M)) → M → [1]` at the site \
  C_{B/A} itself, with both endpoint identifications proved rather than assumed"]
theorem exists_atiyahDisplayedTriangle_distinguished :
    ∃ e₁ : (polynomialAtiyahTriangle A B M).obj₁ ≅ atiyahDisplayedObj₁ A B M,
      Triangle.mk (e₁.inv ≫ (polynomialAtiyahTriangle A B M).mor₁)
          ((polynomialAtiyahTriangle A B M).mor₂ ≫
            (polynomialAtiyahTriangleObj₃Iso A B M).hom)
          ((polynomialAtiyahTriangleObj₃Iso A B M).inv ≫
            (polynomialAtiyahTriangle A B M).mor₃ ≫
              (shiftFunctor
                (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))))
                (1 : ℤ)).map e₁.hom) ∈
        distinguishedTriangles := by
  obtain ⟨e₁⟩ := nonempty_atiyahFirstVertexDerivedTensorIso A B M
  exact ⟨e₁, Stacks.Atiyah.triangle_distinguished_of_iso _ _ _ _ _ _ e₁
    (polynomialAtiyahTriangleObj₃Iso A B M)⟩

/-! ### The Atiyah class -/

/-- **Stacks 09DE, the Atiyah class of a module.** For a ring map `A → B` and a `B`-module `M`
there is an identification `e₁` of the first term of the Atiyah triangle on the site `C_{B/A}`
with `L_{B/A} ⊗^𝐋_B M` for which the *Atiyah class* of `M`,

`M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]`,

is the last arrow of the distinguished triangle displayed by [Stacks, Tag 09DD]:

`L_{B/A} ⊗^𝐋_B M ⟶ Lπ_!(P¹_{𝒪/A}(M)) ⟶ M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]`.

The class itself is `CommAlgCat.polynomialAtiyahClassOfIso`, the last arrow
`Lπ_!(M̲) ⟶ Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲)[1]` of the Atiyah triangle read through identifications of the
endpoints, instantiated at the displayed endpoints: the third by the canonical
`CommAlgCat.polynomialAtiyahTriangleObj₃Iso`, [Stacks, Tag 08QE] at this site, and the first by
`e₁`. Nothing is assumed — `e₁` is produced inside the proof from
`CommAlgCat.nonempty_atiyahFirstVertexDerivedTensorIso`, the chain of [Tag 08PT] and [Tag 08PU]
at this site — and this is the whole of the definition: the arrow, its source `M`, its target
`(L_{B/A} ⊗^𝐋_B M)[1]`, and its being the last arrow of the triangle of (92.17.0.1).

`e₁` is existentially quantified rather than named because the K-flat resolution computing the
derived tensor product is chosen and not canonical, so there is no canonical identification of
the first term to name. That costs nothing: by
`CommAlgCat.polynomialAtiyahClassOfIso_mem_distinguished` the conclusion holds for *every* such
identification, so the existential asserts only that one exists. The module documentation records
why naming one by `Classical.choice` instead would fix a non-canonical choice. -/
@[stacks 09DE "the Atiyah class M → (L_{B/A} ⊗^L_B M)[1] at the site C_{B/A} itself, as the \
  last arrow of the displayed distinguished triangle of (92.17.0.1); both endpoint \
  identifications are proved rather than assumed"]
theorem exists_atiyahDisplayedClass_mem_distinguished :
    ∃ e₁ : (polynomialAtiyahTriangle A B M).obj₁ ≅ atiyahDisplayedObj₁ A B M,
      Triangle.mk (e₁.inv ≫ (polynomialAtiyahTriangle A B M).mor₁)
          ((polynomialAtiyahTriangle A B M).mor₂ ≫
            (polynomialAtiyahTriangleObj₃Iso A B M).hom)
          (polynomialAtiyahClassOfIso A B M (atiyahDisplayedObj₁ A B M)
            ((DerivedCategory.singleFunctor
              (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) 0).obj M) e₁
            (polynomialAtiyahTriangleObj₃Iso A B M)) ∈
        distinguishedTriangles := by
  obtain ⟨e₁⟩ := nonempty_atiyahFirstVertexDerivedTensorIso A B M
  exact ⟨e₁, polynomialAtiyahClassOfIso_mem_distinguished A B M _ _ e₁
    (polynomialAtiyahTriangleObj₃Iso A B M)⟩

end CommAlgCat

end
