module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomTermwiseSplit
public import StacksFrontier.CategoryTheory.Limits.CoproductSingleSupport
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom complex into a complex concentrated in one degree

Let `(C, O)` be a ringed site, let `E` be a bounded complex of `O`-modules and let `M` be an
`O`-module placed in a single degree. This file collapses the degree-`n` term of the internal
Hom complex `SheafHom(E, M[-b])` of Stacks 0A8Z to a single internal Hom sheaf.

## Main results

* `AlgebraicGeometry.RingedSite.homSingleTargetDegreeIso`: the collapse, for a target
  concentrated in degree `n - r`:

  `SheafHom(E, M[r - n])^n = SheafHom(E^{-r}, M)`.

* `AlgebraicGeometry.RingedSite.homStructureSheafDegreeIso`: the same for the structure sheaf
  in degree zero, `SheafHom(E, O[0])^n = SheafHom(E^{-n}, O)`.
* `AlgebraicGeometry.RingedSite.homStructureSheafDegreeIso_hom`: that collapse is the `n`-th
  projection of the product description of the term, up to the transport identifying `O[0]^{n-n}`
  with `O`, and `AlgebraicGeometry.RingedSite.homStructureSheafDegreeIso_naturality`: it is
  natural in the source complex.
* `AlgebraicGeometry.RingedSite.isZero_homStructureSheafDegree` and
  `AlgebraicGeometry.RingedSite.sheafHomComplex_structureSheaf_bounded`: the term vanishes where
  `E^{-n}` does, and `SheafHom(E, O[0])` is bounded when `E` is.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The covariant functoriality of the internal Hom sheaf in its target carries the identity to
the identity. -/
private theorem internalHomPost_id
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomPost X (A := A) (𝟙 B) = 𝟙 (internalHomSheaf X A B) := by
  ext U a
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- An isomorphism of the target induces an isomorphism of internal Hom sheaves. -/
def internalHomSheafPostIso (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {B C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : B ≅ C) :
    internalHomSheaf X A B ≅ internalHomSheaf X A C where
  hom := internalHomPost X e.hom
  inv := internalHomPost X e.inv
  hom_inv_id := by
    rw [internalHomPost_comp, e.hom_inv_id, internalHomPost_id]
  inv_hom_id := by
    rw [internalHomPost_comp, e.inv_hom_id, internalHomPost_id]

/-- **Stacks 08JH for a target concentrated in one degree.** For `E` bounded and `M` an
`O`-module placed in degree `n - r`, the degree-`n` term of the internal Hom complex
`SheafHom(E, M[r - n])` of Stacks 0A8Z is the single internal Hom sheaf `SheafHom(E^{-r}, M)`. -/
def homSingleTargetDegreeIso
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n r : ℤ) :
    (sheafHomComplex X E
        ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) (n - r)).obj M)).obj.X n ≅
      internalHomSheaf X (E.X (-r)) M :=
  (strictlyPerfectHomDegreeIso X E
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) (n - r)).obj M) hE n).trans
    ((coprodIsoOfSingleSupport
        (fun q : ℤ => internalHomSheaf X (E.X (-q))
          (((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) (n - r)).obj M).X (n - q))) r
        (fun q hq => internalHomSheaf_isZero_of_isZero_target X
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (n - r) M (n - q)
            (fun h => hq (by omega))))).trans
      (internalHomSheafPostIso X (E.X (-r))
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (n - r) M)))

/-- **Stacks 08JH into the structure sheaf.** The degree-`n` term of the internal Hom complex
`SheafHom(E, O[0])` of a bounded complex `E` is the dual `SheafHom(E^{-n}, O)` of its
degree-`(-n)` term. -/
def homStructureSheafDegreeIso
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n : ℤ) :
    (sheafHomComplex X E (structureSheafComplex X)).obj.X n ≅
      internalHomSheaf X (E.X (-n))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (strictlyPerfectHomDegreeIso X E (structureSheafComplex X) hE n).trans
    ((coprodIsoOfSingleSupport
        (fun q : ℤ => internalHomSheaf X (E.X (-q)) ((structureSheafComplex X).X (n - q))) n
        (fun q hq => internalHomSheaf_isZero_of_isZero_target X
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ (n - q)
            (by omega)))).trans
      (eqToIso (by rw [sub_self]; rfl)))

/-- **The collapse into the structure sheaf is the `n`-th projection of the product
description** of the degree-`n` term, up to the transport identifying the degree-`0` term
`O[0]^{n-n}` of the target with `O`. -/
theorem homStructureSheafDegreeIso_hom
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n : ℤ)
    (h : internalHomSheaf X (E.X (-n)) ((structureSheafComplex X).X (n - n)) =
      internalHomSheaf X (E.X (-n))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (homStructureSheafDegreeIso X E hE n).hom =
      homDegreeProjection X E (structureSheafComplex X) n n ≫ eqToHom h := by
  have hvan : ∀ q : ℤ, q ≠ n →
      IsZero (internalHomSheaf X (E.X (-q)) ((structureSheafComplex X).X (n - q))) :=
    fun q hq => internalHomSheaf_isZero_of_isZero_target X
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ (n - q) (by omega))
  have hdesc : (coprodIsoOfSingleSupport
        (fun q : ℤ => internalHomSheaf X (E.X (-q)) ((structureSheafComplex X).X (n - q))) n
        hvan).hom =
      Sigma.desc (fun i : ℤ =>
        Sigma.ι (fun q : ℤ => internalHomSheaf X (E.X (-q))
            ((structureSheafComplex X).X (n - q))) i ≫
          (coprodIsoOfSingleSupport (fun q : ℤ => internalHomSheaf X (E.X (-q))
            ((structureSheafComplex X).X (n - q))) n hvan).hom) :=
    Sigma.hom_ext _ _ fun i => by rw [Sigma.ι_comp_desc]
  have hkey : (strictlyPerfectHomDegreeIso X E (structureSheafComplex X) hE n).hom ≫
      (coprodIsoOfSingleSupport (fun q : ℤ => internalHomSheaf X (E.X (-q))
        ((structureSheafComplex X).X (n - q))) n hvan).hom =
      homDegreeProjection X E (structureSheafComplex X) n n := by
    have hid : Sigma.ι (fun q : ℤ => internalHomSheaf X (E.X (-q))
          ((structureSheafComplex X).X (n - q))) n ≫
        (coprodIsoOfSingleSupport (fun q : ℤ => internalHomSheaf X (E.X (-q))
          ((structureSheafComplex X).X (n - q))) n hvan).hom =
        𝟙 (internalHomSheaf X (E.X (-n)) ((structureSheafComplex X).X (n - n))) :=
      (coprodIsoOfSingleSupport (fun q : ℤ => internalHomSheaf X (E.X (-q))
        ((structureSheafComplex X).X (n - q))) n hvan).inv_hom_id
    rw [hdesc, strictlyPerfectHomDegreeIso_hom_comp_desc X E (structureSheafComplex X) hE n n
      hvan, hid, Category.comp_id]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eqToHom h) hkey)

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A transport of the target of an internal Hom sheaf commutes with precomposition in the
source. -/
private theorem internalHomPre_comp_eqToHom
    {A B C C' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f : A ⟶ B) (h : C = C') :
    internalHomPre X (C := C) f ≫ eqToHom (congrArg (internalHomSheaf X A) h) =
      eqToHom (congrArg (internalHomSheaf X B) h) ≫ internalHomPre X (C := C') f := by
  subst h
  simp

/-- **The collapse into the structure sheaf is natural in the source complex.** A morphism
`k : E' ⟶ E` of complexes induces the morphism `homMap X k (𝟙 O[0])` of internal Hom complexes
in the other direction, and through the collapse its degree-`n` component is precomposition
with the component `k^{-n}`. -/
theorem homStructureSheafDegreeIso_naturality
    (E E' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hE' : {i : ℤ | ¬ IsZero (E'.X i)}.Finite) (k : E' ⟶ E) (n : ℤ) :
    (homMap X k (𝟙 (structureSheafComplex X))).f n ≫
        (homStructureSheafDegreeIso X E' hE' n).hom =
      (homStructureSheafDegreeIso X E hE n).hom ≫ internalHomPre X (k.f (-n)) := by
  have hobj : (structureSheafComplex X).X (n - n) =
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) := by
    rw [sub_self]; rfl
  rw [homStructureSheafDegreeIso_hom X E' hE' n
      (congrArg (internalHomSheaf X (E'.X (-n))) hobj),
    homStructureSheafDegreeIso_hom X E hE n (congrArg (internalHomSheaf X (E.X (-n))) hobj),
    ← Category.assoc, homDegreeProjection_homMap, Category.assoc, Category.assoc]
  exact congrArg (homDegreeProjection X E (structureSheafComplex X) n n ≫ ·)
    (internalHomPre_comp_eqToHom X (k.f (-n)) hobj)

/-- The degree-`n` term of `SheafHom(E, O[0])` vanishes where `E^{-n}` does. -/
theorem isZero_homStructureSheafDegree
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n : ℤ) (h : IsZero (E.X (-n))) :
    IsZero ((sheafHomComplex X E (structureSheafComplex X)).obj.X n) :=
  IsZero.of_iso (internalHomSheaf_isZero_of_isZero X h) (homStructureSheafDegreeIso X E hE n)

/-- The internal Hom complex `SheafHom(E, O[0])` is bounded when `E` is. -/
theorem sheafHomComplex_structureSheaf_bounded
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) :
    {i : ℤ | ¬ IsZero ((sheafHomComplex X E (structureSheafComplex X)).obj.X i)}.Finite :=
  (hE.image (fun i : ℤ => -i)).subset fun n hn =>
    ⟨-n, fun h => hn (isZero_homStructureSheafDegree X E hE n h), neg_neg n⟩

end AlgebraicGeometry.RingedSite

end
