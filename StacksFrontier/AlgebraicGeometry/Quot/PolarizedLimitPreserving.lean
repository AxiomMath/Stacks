module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesFibered
public import StacksFrontier.Deformation.Artin.LimitPreserving

/-!
# Limit preservation for the stack of polarized proper schemes (Stacks 0D43)

Stacks 0D43 asserts that the stack in groupoids `𝒫olarized` of Stacks 0D1M is *limit preserving*
in the sense of Stacks 07XL: for every cofiltered inverse system of affine schemes with limit `T`
the canonical comparison `colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` is an equivalence of categories.

Two things have to be arranged before the predicate can even be applied. First, `𝒫olarized` is a
category over the *absolute* big fppf site `Sch_fppf`, through
`AlgebraicGeometry.polarizedProjection`, whereas `Deformation.Artin.IsLimitPreserving` is stated
for a category fibred in groupoids over the big fppf site `(Sch/S)_fppf` of a base scheme `S`.
Since the source's site is absolute, the base to take is a *terminal* one, and a category over `C`
is canonically a category over the slice `C/T` at a terminal `T`: send an object to the unique
morphism from its image to `T`. This reindexing is `CategoryTheory.Functor.sliceAtTerminal`, and it
carries fibredness in groupoids because lifts and fill-ins in `C/T` are those of `C`, the
commutation with the structure morphism to `T` being automatic. For `S = Spec(ℤ)` the terminality
hypothesis is discharged by `AlgebraicGeometry.isTerminal_obj_specULiftZ`.

Second, `𝒫olarized` is known to be fibred in groupoids only given Stacks 0893, that relative
ampleness of an invertible module is stable under base change; that is
`AlgebraicGeometry.Scheme.Modules.RelativelyAmpleBaseChange`, and it is carried here as the
hypothesis `hbc`, exactly as in
`AlgebraicGeometry.polarizedProjection_isFiberedInGroupoids`.

What is proved about the comparison itself is its *essential surjectivity criterion*: the
comparison is essentially surjective as soon as every object over the vertex of the cone admits a
morphism, lying over a cone projection, to an object at a finite stage. That is the shape in which
the four colimit-and-descent facts of the source — Stacks 01ZM, 01ZR, 0B8W, 04AI, 09MT and 081F —
deliver their conclusion, and it is the converse of the reduction already in the library for the
outward implication Stacks 07XN. The geometric input itself, that a polarized family over a
cofiltered limit of affine schemes descends to a finite stage, is not proved in this file, and
neither is the full faithfulness of the comparison; both are proved in
`StacksFrontier/AlgebraicGeometry/Quot/PolarizedLimitPreservingProof.lean`. See the implementation
notes.

## Main definitions

* `CategoryTheory.Functor.sliceAtTerminal`: a category over `C` read as a category over the slice
  of `C` at a terminal object.
* `AlgebraicGeometry.polarizedSliceProjection`: `𝒫olarized` read as a category over the big fppf
  site of a terminal base scheme.
* `AlgebraicGeometry.polarizedStack`: **Stacks 0D1M and 003S**, `𝒫olarized` as an object of the
  2-category of categories fibred in groupoids over that site, given Stacks 0893.
* `AlgebraicGeometry.IsLimitPreservingPolarized`: **Stacks 0D43**, the assertion of Stacks 07XL
  for `𝒫olarized`.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.sliceAtTerminal`: **Stacks 003S** transports along
  the reindexing to a terminal slice.
* `AlgebraicGeometry.isTerminal_obj_specULiftZ`: `Spec(ℤ)` is terminal in the underlying category
  of a big fppf site containing it.
* `Deformation.Artin.essSurj_colimitComparison_of_exists_stage_iso` and
  `Deformation.Artin.essSurj_colimitComparison_of_exists_stage_lift`: the stage-wise criteria for
  essential surjectivity of the comparison functor of Stacks 07XL.

## Implementation notes

**Where the proof lives.** `AlgebraicGeometry.IsLimitPreservingPolarized` is stated here and not
proved here; the proof, for the hypothesis-free form
`AlgebraicGeometry.IsLimitPreservingPolarizedUnconditional`, is
`AlgebraicGeometry.isLimitPreservingPolarizedUnconditional` in
`StacksFrontier/AlgebraicGeometry/Quot/PolarizedLimitPreservingProof.lean`. It cannot be stated in
this file, which is below `AlgebraicGeometry.polarizedStackUnconditional` in the import order. Two
inputs go into it.

The first is geometric, and is the content of the source's proof: a polarized family over the
limit `S = lim Sᵢ` of a cofiltered system of affine schemes descends to a finite stage. The seven
cited ingredients are all in the library — `exists_model_of_finitePresentation` (01ZM (1)),
`exists_morphism_after_baseChange` and `eventually_eq_of_baseChange_eq` (01ZM (2), (3)),
`exists_isFinitePresentation_pullback_iso_of_qcqs` (01ZR),
`exists_isInvertible_pullback_iso_of_isLimit` (0B8W),
`exists_flat_baseChange_of_limitBaseChange` (04AI),
`exists_isAmple_pullback_map_of_isLimit_of_qcqs` (09MT) and, for an affine base,
`exists_isProper_finitePresentation_baseChange_of_isAffine` (081F) — and the bases occurring in
Stacks 07XL are affine, so `isRelativelyAmple_iff_isAmple_of_isAffineBase` (01VK) bridges the
relative ampleness carried by `AlgebraicGeometry.PolarizedFamily` to the absolute ampleness that
09MT speaks about. Assembling them into one stage requires, besides the cofiltered joins, the
limit presentation of the system of base changes of the total space, and the transport of the
polarization along it; that assembly is
`AlgebraicGeometry.exists_stage_polarizedModel`. Note also that every one of those ingredients
asks the index category to be essentially small in the scheme universe, while
`Deformation.Artin.IsLimitPreserving` quantifies over index categories in free universes `v` and
`w`; the predicate is therefore provable from them only at `v = w = u`, which is the smallness the
source's directed sets have.

The second input is full faithfulness of the comparison, which is not a stage-wise statement about
pullbacks but a statement about morphisms of a colimit in `Cat`. It is reduced to stage-wise data
by `Deformation.Artin.full_of_descentHom` and `Deformation.Artin.faithful_of_descentEq`, whose
hypotheses are `AlgebraicGeometry.descentHom_polarizedSliceProjection` and
`AlgebraicGeometry.descentEq_polarizedSliceProjection`; the geometric inputs there are 01ZM (2)
and (3) together with 01ZR.

**Why a general reindexing rather than a redefinition.** The fibred-in-groupoids statement for
polarized families is proved for `AlgebraicGeometry.polarizedProjection` into the absolute site,
so the slice version must be obtained from it rather than proved again; and the reindexing used is
an equivalence of base categories, so nothing is lost. The alternative, restricting `𝒫olarized`
along `Over.forget` for an arbitrary base `S`, would describe polarized families whose base
carries a morphism to `S` and so would state a different assertion from the source's.

**Why the essential-surjectivity criterion is stated twice.** The iso form is what the colimit
machinery of Stacks 07XL produces directly; the lift form is what a geometric descent argument
produces, and it reduces to the iso form because in a category fibred in groupoids any lift of a
base morphism is strongly cartesian, so it is canonically isomorphic in the fibre to the chosen
pullback.

## References

* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w uC vC uX vX

/-! ### Reindexing a category over `C` to the slice of `C` at a terminal object -/

namespace CategoryTheory.Functor

variable {𝒮 : Type*} [Category 𝒮] {C : Type*} [Category C] {T : C}

/-- Equal morphisms of a slice category have equal underlying morphisms. -/
private theorem over_hom_left_congr {V U : Over T} {f g : V ⟶ U} (h : f = g) :
    f.left = g.left := by rw [h]

/-- A category over `C` read as a category over the slice of `C` at a terminal object `T`: an
object is sent to the unique morphism from its image to `T`. The base categories `C` and `C/T` are
equivalent, so this changes nothing but the indexing. -/
def sliceAtTerminal (p : 𝒮 ⥤ C) (hT : IsTerminal T) : 𝒮 ⥤ Over T :=
  p ⋙ (Over.equivalenceOfIsTerminal hT).inverse

/-- The image of an object `x` under `p.sliceAtTerminal hT` is the unique morphism from `p.obj x`
to the terminal object `T`. -/
@[simp]
theorem sliceAtTerminal_obj (p : 𝒮 ⥤ C) (hT : IsTerminal T) (x : 𝒮) :
    (p.sliceAtTerminal hT).obj x = Over.mk (hT.from (p.obj x)) := rfl

/-- The underlying object of the image of `x` under `p.sliceAtTerminal hT` is `p.obj x`. -/
@[simp]
theorem sliceAtTerminal_obj_left (p : 𝒮 ⥤ C) (hT : IsTerminal T) (x : 𝒮) :
    ((p.sliceAtTerminal hT).obj x).left = p.obj x := rfl

/-- The underlying morphism of the image of `f` under `p.sliceAtTerminal hT` is `p.map f`. -/
@[simp]
theorem sliceAtTerminal_map_left (p : 𝒮 ⥤ C) (hT : IsTerminal T) {x y : 𝒮} (f : x ⟶ y) :
    ((p.sliceAtTerminal hT).map f).left = p.map f := rfl

/-- An object of `𝒮` lies over an object `V` of the slice exactly when it lies over the underlying
object of `V`: two morphisms to a terminal object agree. -/
theorem sliceAtTerminal_obj_eq (p : 𝒮 ⥤ C) (hT : IsTerminal T) {x : 𝒮} {V : Over T}
    (h : p.obj x = V.left) : (p.sliceAtTerminal hT).obj x = V := by
  change Over.mk (hT.from (p.obj x)) = V
  rw [h]
  exact congrArg Over.mk (hT.hom_ext _ _)

/-- **Stacks 003S for a terminal slice.** A category fibred in groupoids over `C` is fibred in
groupoids over the slice of `C` at a terminal object: a lift of a morphism of the slice is a lift
of its underlying morphism, and a fill-in is determined by its underlying morphism. -/
theorem IsFiberedInGroupoids.sliceAtTerminal {p : 𝒮 ⥤ C} (hp : p.IsFiberedInGroupoids)
    (hT : IsTerminal T) : (p.sliceAtTerminal hT).IsFiberedInGroupoids where
  exists_lift {V U} f x hx := by
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift f.left x (congrArg Comma.left hx)
    have := hφ
    refine ⟨y, φ, IsHomLift.of_fac' _ f φ
      (p.sliceAtTerminal_obj_eq hT (IsHomLift.domain_eq p f.left φ)) hx ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left,
      sliceAtTerminal_map_left]
    exact IsHomLift.fac' p f.left φ
  unique_lift {x y z} φ ψ f hcomm := by
    obtain ⟨χ, ⟨hχ₁, hχ₂⟩, huniq⟩ := hp.unique_lift φ ψ f.left (over_hom_left_congr hcomm)
    exact ⟨χ, ⟨Over.OverMorphism.ext hχ₁, hχ₂⟩,
      fun χ' hχ' => huniq χ' ⟨over_hom_left_congr hχ'.1, hχ'.2⟩⟩

end CategoryTheory.Functor

/-! ### Stage-wise criteria for essential surjectivity of the comparison of Stacks 07XL -/

namespace Deformation.Artin

section EssSurj

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.chosenPullbacks

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  (p : X ⥤ C) [p.IsFibered] {I : Type v} [Category.{w} I] (D : I ⥤ C) (c : Cone D)

/-- **Essential surjectivity of the comparison of Stacks 07XL from stage-wise data.** If every
object over the vertex of the cone is isomorphic, in its fibre, to the pullback along a cone
projection of an object at a finite stage, then the canonical comparison from the colimit of the
stage fibres is essentially surjective.

This is the converse of the reduction used for the outward implication Stacks 07XN. -/
theorem essSurj_colimitComparison_of_exists_stage_iso
    (h : ∀ x : p.Fiber c.pt, ∃ (i : I) (xᵢ : p.Fiber (D.obj i)),
      Nonempty ((Functor.chosenPullbacks p).obj (c.π.app i) xᵢ ≅ x)) :
    (colimitComparison p D c).EssSurj where
  mem_essImage x := by
    obtain ⟨i, xᵢ, ⟨ex⟩⟩ := h x
    refine ⟨(colimit.ι (fiberDiagram p D) (op i)).toFunctor.obj
      (AsSmall.up.{vX, max (max uC uX) vC, max v w}.obj
        ⟨D.obj i, xᵢ, 𝟙 (D.obj i)⟩), ⟨?_⟩⟩
    exact (colimitComparisonStageIso p D c i).app _ ≪≫
      ((Functor.chosenPullbacks p).pullbackFunctor (c.π.app i)).mapIso
        (Functor.pullbackFiberIdIso xᵢ) ≪≫ ex

/-- **Essential surjectivity of the comparison of Stacks 07XL from descent to a stage.** For a
category fibred in groupoids, if every object over the vertex of the cone admits a morphism, lying
over a cone projection, to an object at a finite stage, then the canonical comparison from the
colimit of the stage fibres is essentially surjective.

This is the shape in which a limit-descent argument supplies the condition: the morphism is
strongly cartesian because the category is fibred in groupoids, so its source is canonically
isomorphic in the fibre to the chosen pullback of its target. -/
theorem essSurj_colimitComparison_of_exists_stage_lift (hp : p.IsFiberedInGroupoids)
    (h : ∀ x : p.Fiber c.pt, ∃ (i : I) (xᵢ : p.Fiber (D.obj i)) (φ : x.1 ⟶ xᵢ.1),
      p.IsHomLift (c.π.app i) φ) :
    (colimitComparison p D c).EssSurj :=
  essSurj_colimitComparison_of_exists_stage_iso p D c fun x => by
    obtain ⟨i, xᵢ, φ, hφ⟩ := h x
    have := hφ
    have hcart : p.IsStronglyCartesian (c.π.app i) φ :=
      hp.isStronglyCartesian_homLift (c.π.app i) φ
    have hchosen : p.IsStronglyCartesian (c.π.app i) ((Functor.chosenPullbacks p).map
        (c.π.app i) xᵢ) := (Functor.chosenPullbacks p).isStronglyCartesian (c.π.app i) xᵢ
    exact ⟨i, xᵢ, ⟨Functor.fiberIsoOfCartesian (c.π.app i)
      ((Functor.chosenPullbacks p).map (c.π.app i) xᵢ) φ inferInstance inferInstance⟩⟩

end EssSurj

end Deformation.Artin

/-! ### `𝒫olarized` over the big fppf site of a terminal base -/

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- `Spec(ℤ)` is terminal in the underlying category of a big fppf site containing it: the
inclusion into all schemes is fully faithful, and `Spec(ℤ)` is terminal in all schemes. -/
def isTerminal_obj_specULiftZ
    (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ)))) : IsTerminal (B.obj hZ) :=
  IsTerminal.ofUniqueHom
    (fun Y => B.inclusion.preimage (specULiftZIsTerminal.from (B.inclusion.obj Y)))
    (fun Y m => B.inclusion.map_injective (by
      rw [Functor.map_preimage]
      exact specULiftZIsTerminal.hom_ext _ _))

/-- **Stacks 0D1M.** The category of polarized families read as a category over the big fppf site
of a terminal base scheme `S`, by sending a polarized family to the unique morphism from its base
to `S`. -/
def polarizedSliceProjection (hT : IsTerminal (B.obj hS)) :
    PolarizedFamily B ⥤ BigFppfOver B S hS :=
  (polarizedProjection B).sliceAtTerminal hT

/-- A polarized family whose base is the underlying scheme of an object `V` of the big fppf site
over a terminal `S`, read as an object of the fibre of `𝒫olarized` over `V`. -/
def polarizedFiberMk (hT : IsTerminal (B.obj hS)) (x : PolarizedFamily B)
    {V : BigFppfOver B S hS} (h : x.base = V.left) :
    (polarizedSliceProjection B hS hT).Fiber V :=
  Functor.Fiber.mk ((polarizedProjection B).sliceAtTerminal_obj_eq hT h)

/-- **Stacks 0D1M and 003S, given Stacks 0893.** `𝒫olarized` as an object of the 2-category of
categories fibred in groupoids over the big fppf site of a terminal base scheme. -/
def polarizedStack (hbc : Scheme.Modules.RelativelyAmpleBaseChange.{u})
    (hT : IsTerminal (B.obj hS)) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (polarizedSliceProjection B hS hT))
    ((polarizedProjection_isFiberedInGroupoids hbc).sliceAtTerminal hT)

/-- **Stacks 0D43.** The stack in groupoids `𝒫olarized` of polarized proper schemes is limit
preserving in the sense of Stacks 07XL: for every cofiltered inverse system of affine schemes over
the terminal base with limit `T`, the canonical comparison `colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` is
an equivalence of categories. -/
abbrev IsLimitPreservingPolarized (hbc : Scheme.Modules.RelativelyAmpleBaseChange.{u})
    (hT : IsTerminal (B.obj hS)) : Prop :=
  Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS (polarizedStack B hS hbc hT)

end AlgebraicGeometry

end
