module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.SingleFreeStrictlyPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.TopDegreeInductionStep
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
import StacksCore.Tactic.StacksAttribute

/-!
# The standing hypothesis of the induction travels to the cone along an exact pullback

Let `(C, O)` and `(C', O')` be ringed sites and let `F : Mod(O) ⥤ Mod(O')` be an exact additive
functor carrying the unit to the unit — in the application of Stacks 08HE (2) ⇒ (1) this is the
pullback `ε^*` along the morphism of ringed sites `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of
Stacks 08H7, which is exact by Stacks 08H8 and so acts on the derived categories as
`CategoryTheory.Functor.mapDerivedCategory` of the underived functor.

The recursion `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep` carries a
predicate `P` on objects of `D(O)` from `E` to the third vertex of the triangle its step produces.
In the application `P E` is the conjunction of "`F E` is `m`-pseudo-coherent" and
"the cohomology sheaves of `E` are quasi-coherent"; this module supplies the **first** conjunct's
propagation, which is the half that is about `F`.

The argument is the source's: `F` is exact, so it carries the step's distinguished triangle
`𝒪^{⊕t}[-n] ⟶ E ⟶ C ⟶ 𝒪^{⊕t}[-n+1]` to a distinguished triangle; `F(𝒪^{⊕t}[-n])` is strictly
perfect, hence `m'`-pseudo-coherent for every `m'`; and Stacks 08FV part (1) then makes `F C`
`m`-pseudo-coherent.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_obj₃_of_distinguished`:
  Stacks 08FV part (1) read through `F`, i.e. the propagation with the hypothesis on the first
  vertex left abstract.
* `RingedSite.isPseudoCoherentFrom_mapDerivedCategory_Q_obj_of_isStrictlyPerfect`:
  `F` carries a strictly perfect complex to an `m`-pseudo-coherent object of `D(O')`, for every
  `m`.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_singleFunctor_obj_free`
  and `..._shift_singleFunctor_obj_free`: the same for the induction triangle's actual first
  vertex, `𝒪^{⊕t}` in degree `n` and the shift `(𝒪^{⊕t}[0])[-n]` in which the step produces it.
* `AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift_mapDerivedCategory`: **the
  composition.**  It is `AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift` with the
  `F`-half of `P` on the third vertex added to the conclusion, which is the datum
  `isPseudoCoherentFrom_of_descentStep` asks of its step.

## Implementation notes

That `F.mapDerivedCategory` carries distinguished triangles to distinguished triangles is
Mathlib's: `CategoryTheory.Functor.mapDerivedCategory` of an exact additive functor comes with
`CategoryTheory.Functor.CommShift` and `CategoryTheory.Functor.IsTriangulated` instances, so
`CategoryTheory.Functor.map_distinguished` applies and
`(F.mapDerivedCategory.mapTriangle.obj T).objᵢ` is `F.mapDerivedCategory.obj T.objᵢ` by
definition.  No triangulated structure is constructed here.

Strict perfectness is carried by `SheafOfModules.isStrictlyPerfect_map` — additive, preserving
finite colimits, unit to unit, at independent object and morphism universes — and not by
Stacks 08H3 `AlgebraicGeometry.RingedToposHom.isStrictlyPerfect_pullbackModules`, whose
hypothesis is a `AlgebraicGeometry.RingedToposHom` and which therefore cannot be applied to a
bare functor; the two sites here keep their object and morphism universes independent and share
only the universe `w` of the sections of the two structure sheaves, which is the shape `ε` lives
in.

`exists_distTriang_free_of_lift_mapDerivedCategory` repeats the four lines that build the triangle
in `AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift` rather than invoking it: that
theorem binds its triangle existentially, so the identity of the first vertex — which is what
makes the `(m + 1)`-pseudo-coherence of `F T.obj₁` available — is not recoverable from its
conclusion.  Nothing in the repeat is weaker; the conclusion here is that one with a further
conjunct.

## References

* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
* [Stacks Project, Tag 08H3](https://stacks.math.columbia.edu/tag/08H3)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe uX vX uY vY w dX dY

namespace AlgebraicGeometry.RingedSite

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ V : Y.C, HasSheafify (Y.J.over V) AddCommGrpCat.{w}]
variable [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasDerivedCategory.{dX}
  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [HasDerivedCategory.{dY}
  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
variable (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
  SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

omit [∀ V : Y.C, HasSheafify (Y.J.over V) AddCommGrpCat.{w}]
  [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Stacks 08FV part (1), read through an exact pullback.**  Let `T` be a distinguished triangle
of `D(O)`.  If `F T.obj₁` is `(m + 1)`-pseudo-coherent and `F T.obj₂` is `m`-pseudo-coherent, then
`F T.obj₃` is `m`-pseudo-coherent.

`F.mapDerivedCategory` is a triangulated functor, so it carries `T` to a distinguished triangle
with the same three objects; Stacks 08FV part (1) is
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_one_general`. -/
public theorem isPseudoCoherentFrom_mapDerivedCategory_obj₃_of_distinguished (m : ℤ)
    (T : Triangle (DerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
    (hT : T ∈ distTriang (DerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
    (h₁ : X.IsPseudoCoherentFrom (F.mapDerivedCategory.obj T.obj₁) (m + 1))
    (h₂ : X.IsPseudoCoherentFrom (F.mapDerivedCategory.obj T.obj₂) m) :
    X.IsPseudoCoherentFrom (F.mapDerivedCategory.obj T.obj₃) m :=
  isPseudoCoherentFrom_of_distinguished_one_general X m
    (F.mapDerivedCategory.mapTriangle.obj T)
    (F.mapDerivedCategory.map_distinguished T hT) h₁ h₂

omit [∀ V : Y.C, HasSheafify (Y.J.over V) AddCommGrpCat.{w}]
  [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **An exact pullback of a strictly perfect complex is `m`-pseudo-coherent for every `m`.**
The degreewise image of a strictly perfect complex is strictly perfect
(`SheafOfModules.isStrictlyPerfect_map`), a strictly perfect complex is `m`-pseudo-coherent
(`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_Q_obj_of_isStrictlyPerfect`), and the
degreewise image represents `F.mapDerivedCategory.obj` of the object represented by the complex
(`CategoryTheory.Functor.mapDerivedCategoryFactors`). -/
public theorem isPseudoCoherentFrom_mapDerivedCategory_Q_obj_of_isStrictlyPerfect
    (ηF : F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (m : ℤ) :
    X.IsPseudoCoherentFrom (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) m :=
  isPseudoCoherentFrom_of_iso X m
    (X.isPseudoCoherentFrom_Q_obj_of_isStrictlyPerfect
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      (SheafOfModules.isStrictlyPerfect_map F ηF hP) m)
    (F.mapDerivedCategoryFactors.app P)

omit [∀ V : Y.C, HasSheafify (Y.J.over V) AddCommGrpCat.{w}]
  [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **An exact pullback of a finite free module placed in a single degree is `m`-pseudo-coherent
for every `m`.**  This is the first vertex of the induction triangle of Stacks 08HE (2) ⇒ (1),
read on the other site. -/
public theorem isPseudoCoherentFrom_mapDerivedCategory_singleFunctor_obj_free
    (ηF : F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (n m : ℤ) (ι : Type w) [Finite ι] :
    X.IsPseudoCoherentFrom (F.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) n).obj
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ι))) m :=
  isPseudoCoherentFrom_mapDerivedCategory_Q_obj_of_isStrictlyPerfect F ηF
    ((HomologicalComplex.single
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ) n).obj
      (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ι))
    (IsStrictlyPerfect.single_obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) n _
      (IsDirectSummandOfFiniteFree.free (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ι)) m

/-- `𝒪^{⊕t}` in degree zero, shifted by `-n`, is `𝒪^{⊕t}` in degree `n`. -/
private def shiftSingleFunctorObjFreeIso (n : ℤ) (ι : Type w) :
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
      (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ι))⟦(-n : ℤ)⟧ ≅
    (DerivedCategory.singleFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) n).obj
      (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ι) :=
  ((DerivedCategory.singleFunctors
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).shiftIso (-n) n 0
    (by omega)).app (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ι)

omit [∀ V : Y.C, HasSheafify (Y.J.over V) AddCommGrpCat.{w}]
  [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The first vertex of the induction triangle, in the shape the step produces it.**  The step
of Stacks 08HE (2) ⇒ (1) lifts at truncation degree `0` and puts the shift on `E`, so its first
vertex is `(𝒪^{⊕t}[0])[-n]`; its image under an exact pullback is `m`-pseudo-coherent for every
`m`.

It follows from the degree `n` case through the identification of `(𝒪^{⊕t}[0])[-n]` with
`𝒪^{⊕t}[n]`, which `shiftSingleFunctorObjFreeIso` provides. -/
public theorem isPseudoCoherentFrom_mapDerivedCategory_shift_singleFunctor_obj_free
    (ηF : F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (n m : ℤ) (ι : Type w) [Finite ι] :
    X.IsPseudoCoherentFrom (F.mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ι))⟦(-n : ℤ)⟧))
      m :=
  isPseudoCoherentFrom_of_iso X m
    (isPseudoCoherentFrom_mapDerivedCategory_singleFunctor_obj_free F ηF n m ι)
    (F.mapDerivedCategory.mapIso (shiftSingleFunctorObjFreeIso (Y := Y) n ι))

/-- **The triangle of the induction step of Stacks 08HE (2) ⇒ (1), with the standing hypothesis
carried to the third vertex along an exact pullback.**

This is `AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift` together with the extra
conclusion that `F` of the third vertex is `m`-pseudo-coherent, given that `F E` is: the triangle
datum that `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep` asks of its step,
with the `F`-half of its predicate `P` discharged on the cone.

The first vertex's image is `(m + 1)`-pseudo-coherent by
`isPseudoCoherentFrom_mapDerivedCategory_shift_singleFunctor_obj_free`, the second vertex is `E`
on the nose, and the propagation is
`isPseudoCoherentFrom_mapDerivedCategory_obj₃_of_distinguished`. -/
public theorem exists_distTriang_free_of_lift_mapDerivedCategory
    (ηF : F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (m n : ℤ)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [DerivedCategory.IsLE E n] (ι : Type w) [Finite ι]
    (φ : SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ι ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) n).obj E)
    (hφ : Epi φ)
    (f : (DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ι) ⟶ E⟦n⟧)
    (hf : f ≫ (DerivedCategory.TStructure.t.truncGEπ 0).app (E⟦n⟧) =
      DerivedCategory.singleMapTruncGEZeroShift E n φ)
    (hE : X.IsPseudoCoherentFrom (F.mapDerivedCategory.obj E) m) :
    ∃ T : Triangle (DerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))),
      T ∈ distTriang (DerivedCategory
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ∧
        Nonempty (T.obj₂ ≅ E) ∧ Y.IsPseudoCoherentFrom T.obj₁ m ∧
          X.IsPseudoCoherentFrom (F.mapDerivedCategory.obj T.obj₃) m ∧
            ∀ j : ℤ, n ≤ j →
              IsZero ((DerivedCategory.homologyFunctor
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).obj
                T.obj₃) := by
  have := hφ
  let e := shiftSingleFunctorObjFreeIso (Y := Y) n ι
  have hK : ∀ j : ℤ, n < j →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).obj
        (((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ι))⟦(-n : ℤ)⟧)) :=
    fun j hj =>
    IsZero.of_iso (DerivedCategory.isZero_of_isLE _ n j hj)
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).mapIso e)
  obtain ⟨Q, g, h, hT, hQ⟩ := exists_distTriang_isZero_homology_obj₃_of_epi n
    (f⟦(-n : ℤ)⟧' ≫ (shiftShiftNeg E n).hom) hK
    (fun j hj => DerivedCategory.isZero_of_isLE E n j hj)
    (DerivedCategory.epi_homologyMap_shiftBack_of_lift E n f _ hf
      (DerivedCategory.epi_homologyMap_singleMapTruncGEZeroShift E n φ))
  refine ⟨Triangle.mk (f⟦(-n : ℤ)⟧' ≫ (shiftShiftNeg E n).hom) g h, hT, ⟨Iso.refl _⟩,
    isPseudoCoherentFrom_of_iso Y m
      (Y.isPseudoCoherentFrom_singleFunctor_obj_free n m ι) e, ?_, hQ⟩
  exact isPseudoCoherentFrom_mapDerivedCategory_obj₃_of_distinguished F m _ hT
    (isPseudoCoherentFrom_mapDerivedCategory_shift_singleFunctor_obj_free F ηF n (m + 1) ι) hE

/-! ### The same statements with the functor's typeclass hypotheses passed explicitly

At a concrete pair of ringed sites — the small Zariski and small étale sites of a scheme, with
`F = ε^*` — additivity and exactness of `F` are available at the spelling of the structure sheaves
`F` was built with, whereas the statements above ask for them at the spelling
`AlgebraicGeometry.RingedSite.ringSheaf`.  The two are equal by `rfl`, but
`AlgebraicGeometry.RingedSite.ringSheaf` does not reduce at instance transparency, so instance
search does not cross between them; passing the hypotheses explicitly replaces synthesis by a
definitional check, which does.  This is the obstruction documented at
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses`, and the
two forms below are the same statements in the shape that can be applied. -/

section Applied

variable (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
  SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

omit [∀ V : Y.C, HasSheafify (Y.J.over V) AddCommGrpCat.{w}]
  [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `isPseudoCoherentFrom_mapDerivedCategory_obj₃_of_distinguished` with the three functor-level
typeclass hypotheses taken as explicit arguments rather than synthesized. -/
public theorem isPseudoCoherentFrom_mapDerivedCategory_obj₃_of_distinguished_of_hypotheses
    (hadd : F'.Additive) (hlim : PreservesFiniteLimits F') (hcolim : PreservesFiniteColimits F')
    (m : ℤ) (T : Triangle (DerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
    (hT : T ∈ distTriang (DerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
    (h₁ : haveI := hadd; haveI := hlim; haveI := hcolim
      X.IsPseudoCoherentFrom (F'.mapDerivedCategory.obj T.obj₁) (m + 1))
    (h₂ : haveI := hadd; haveI := hlim; haveI := hcolim
      X.IsPseudoCoherentFrom (F'.mapDerivedCategory.obj T.obj₂) m) :
    haveI := hadd
    haveI := hlim
    haveI := hcolim
    X.IsPseudoCoherentFrom (F'.mapDerivedCategory.obj T.obj₃) m := by
  have := hadd
  have := hlim
  have := hcolim
  exact isPseudoCoherentFrom_mapDerivedCategory_obj₃_of_distinguished F' m T hT h₁ h₂

/-- `exists_distTriang_free_of_lift_mapDerivedCategory` with the three functor-level typeclass
hypotheses taken as explicit arguments rather than synthesized. -/
public theorem exists_distTriang_free_of_lift_mapDerivedCategory_of_hypotheses
    (hadd : F'.Additive) (hlim : PreservesFiniteLimits F') (hcolim : PreservesFiniteColimits F')
    (ηF : F'.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (m n : ℤ)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [DerivedCategory.IsLE E n] (ι : Type w) [Finite ι]
    (φ : SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ι ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) n).obj E)
    (hφ : Epi φ)
    (f : (DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ι) ⟶ E⟦n⟧)
    (hf : f ≫ (DerivedCategory.TStructure.t.truncGEπ 0).app (E⟦n⟧) =
      DerivedCategory.singleMapTruncGEZeroShift E n φ)
    (hE : haveI := hadd; haveI := hlim; haveI := hcolim
      X.IsPseudoCoherentFrom (F'.mapDerivedCategory.obj E) m) :
    haveI := hadd
    haveI := hlim
    haveI := hcolim
    ∃ T : Triangle (DerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))),
      T ∈ distTriang (DerivedCategory
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ∧
        Nonempty (T.obj₂ ≅ E) ∧ Y.IsPseudoCoherentFrom T.obj₁ m ∧
          X.IsPseudoCoherentFrom (F'.mapDerivedCategory.obj T.obj₃) m ∧
            ∀ j : ℤ, n ≤ j →
              IsZero ((DerivedCategory.homologyFunctor
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).obj
                T.obj₃) := by
  have := hadd
  have := hlim
  have := hcolim
  exact exists_distTriang_free_of_lift_mapDerivedCategory F' ηF m n E ι φ hφ f hf hE

end Applied

end AlgebraicGeometry.RingedSite

end
