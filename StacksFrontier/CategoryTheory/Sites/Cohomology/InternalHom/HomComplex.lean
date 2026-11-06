module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.CategoryTheory.Sites.SheafHom
public import StacksFrontier.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom complex of complexes of modules on a ringed site

Let `(C, O)` be a ringed site and let `L` and `M` be complexes of `O`-modules. This file
constructs their internal Hom complex `SheafHom(L, M)`, a complex of `O`-modules whose sections
over an object `U` are the ordinary Hom complex of the restrictions `L|_U` and `M|_U`, and
identifies the cohomology of its complexes of sections with morphisms in the homotopy category:

* locally, `Hⁿ(Γ(U, SheafHom(L, M))) = Hom_{K(O|_U)}(L|_U, M|_U[n])`;
* globally, `Hⁿ(Γ(C, SheafHom(L, M))) = Hom_{K(O)}(L, M[n])`.

In degree `n` the complex is the product, over the pairs `(p, q)` with `p + n = q`, of the
internal Hom sheaves `SheafHom(L^p, M^q)` of Stacks 03EM, with the usual Hom-complex
differential; `localHomComplexIso` and `globalHomComplexIso` identify its sections, degreewise
and compatibly with the differential, with Mathlib's `CochainComplex.HomComplex`. Both
identifications of cohomology are then Mathlib's `CochainComplex.HomComplex.homologyAddEquiv`
followed by `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`.

## Main definitions

* `AlgebraicGeometry.RingedSite.abelianGlobalSectionsFunctor`: global sections of a sheaf of
  abelian groups on the site, as compatible families of sections.
* `AlgebraicGeometry.RingedSite.sectionComplex` and
  `AlgebraicGeometry.RingedSite.globalSectionsComplex`: the complexes of sections of a complex
  of `O`-modules over an object and over the whole site.
* `AlgebraicGeometry.RingedSite.SheafHomComplex`: the data of an internal Hom complex, namely a
  complex of `O`-modules together with the identification of its sections on every slice with
  the Hom complex of the restrictions, the compatibility of those identifications with
  restriction and with the `O(U)`-action, and the global identification.
* `AlgebraicGeometry.RingedSite.sheafHomComplex`: the internal Hom complex, as such data.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomComplexSectionHomologyEquivHomotopyCategory`:
  `Hⁿ(Γ(U, SheafHom(L, M)))` is the group of morphisms `L|_U ⟶ M|_U[n]` in `K(O|_U)`.
* `AlgebraicGeometry.RingedSite.sheafHomComplexHomologyEquivHomotopyCategory`:
  `Hⁿ(Γ(C, SheafHom(L, M)))` is the group of morphisms `L ⟶ M[n]` in `K(O)`.

## Implementation notes

The internal Hom is kept as a complex of `O`-modules rather than only of abelian sheaves, and
its characterisation records the `O(U)`-semilinearity of the local identifications, so that it
really is the internal Hom of `O`-modules. The structure sheaf of a `RingedSite` is already
`CommRingCat`-valued and forgetting commutativity to index sheaves of modules does not discard
the commutativity of the section rings, which is what makes the `O(U)`-action available.

The global identification is part of the data rather than derived from the local ones, because
a general site need not have a terminal object representing global sections. Global sections
are compatible families, so they need no sheafification in the universe of the input module
sections; the global Hom complex is lifted to the output universe before comparison. The
objects of the site, its morphisms, the sections of the structure sheaf and the sections of the
modules all carry independent universes, the output sections living in `max u v m`, which is
where the maps on each slice site live.

Two spellings of the same sheaf of rings meet in this file: sheaves of modules on a ringed site
are taken over `X.ringSheaf`, whereas the internal Hom of Stacks 03EM is stated over
`Oforget X.O.obj`. The two are definitionally equal, but only by unfolding, so `valOf` and
`homOf` below name a sheaf of modules and a morphism of sheaves of modules at the second
spelling; using them keeps every term type-correct at reducible transparency and is what lets
this file need no transparency option at all. For the same reason `addCommGrpPiCone` and
`sheafHomComplexObj` are reducible and `addCommGrpCat_hom'_eq` names the `ConcreteCategory`
coercion.

## References

* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
* [Stacks Project, Tag 0A8Y](https://stacks.math.columbia.edu/tag/0A8Y)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits CochainComplex.HomComplex

universe m u v w i

namespace AlgebraicGeometry.RingedSite


/-- `A.val` read over the presheaf of rings `Oforget X.O.obj`, which is the spelling at which
the internal-Hom API of Stacks 03EM is stated. -/
public abbrev valOf (X : RingedSite.{u, v, w})
    (A : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PresheafOfModules.{m} (Oforget X.O.obj) := A.val

/-- `f.val` read over the presheaf of rings `Oforget X.O.obj`; the morphism counterpart of
`valOf`. -/
public abbrev homOf (X : RingedSite.{u, v, w})
    {A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f : A ⟶ B) : valOf X A ⟶ valOf X B := f.val

/-- The internal Hom sheaf `SheafHom(A, B)` of two sheaves of `O`-modules, whose sections over
`U` are the morphisms `A|_U ⟶ B|_U` of modules on the slice site. -/
public noncomputable def internalHomSheaf (X : RingedSite.{u, v, w})
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
        SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  { val := internalHom X.O.obj (valOf X A) (valOf X B)
    isSheaf := internalHom_isSheaf X.O.obj A.val B.val B.isSheaf }

/-- The internal Hom sheaf into a zero module is zero. -/
public theorem internalHomSheaf_isZero_of_isZero_target (X : RingedSite.{u, v, w})
    {A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (hB : IsZero B) :
    IsZero (internalHomSheaf X A B) := by
  apply (IsZero.iff_id_eq_zero _).2
  ext U s
  have hz := (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      U.unop).map_isZero hB
  exact congrArg SheafOfModules.Hom.val
    (hz.eq_of_tgt (⟨s⟩ : A.over U.unop ⟶ B.over U.unop)
      ⟨(0 : (internalHomSheaf X A B).val.obj U)⟩)

/-- Postcomposition with `f : B ⟶ C`, as a morphism `SheafHom(A, B) ⟶ SheafHom(A, C)`. -/
public noncomputable def internalHomPost (X : RingedSite.{u, v, w})
    {A B C : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : B ⟶ C) :
    internalHomSheaf X A B ⟶ internalHomSheaf X A C :=
  ⟨Stacks.PresheafOfModules.InternalHom.internalHomMapRight
    X.O.obj A.val f.val⟩

/-- Precomposition with `f : A ⟶ B`, as a morphism `SheafHom(B, C) ⟶ SheafHom(A, C)`. -/
public noncomputable def internalHomPre (X : RingedSite.{u, v, w})
    {A B C : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : A ⟶ B) :
    internalHomSheaf X B C ⟶ internalHomSheaf X A C :=
  ⟨PresheafOfModules.Hom.mk
    (fun U ↦
      letI := homModule X.O.obj (valOf X B) (valOf X C) U.unop
      letI := homModule X.O.obj (valOf X A) (valOf X C) U.unop
      ModuleCat.ofHom
        { toFun := fun g ↦ (restrFun X.O.obj U.unop).map (homOf X f) ≫ g
          map_add' := fun _ _ ↦ by simp
          map_smul' := fun r g ↦ by
            change _ ≫ smulHom X.O.obj (valOf X B) (valOf X C) U.unop r g =
              smulHom X.O.obj (valOf X A) (valOf X C) U.unop r
                ((restrFun X.O.obj U.unop).map (homOf X f) ≫ g)
            simp only [smulHom, Category.assoc] })
    (fun {U V} a ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro g
      rfl)⟩

private noncomputable abbrev sheafHomTerm (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  ∏ᶜ fun t : Triplet n => internalHomSheaf X (L.X t.p) (M.X t.q)

private noncomputable def sheafHomDifferential (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    sheafHomTerm X L M n ⟶ sheafHomTerm X L M (n + 1) :=
  CategoryTheory.Limits.Pi.lift fun t : Triplet (n + 1) =>
    CategoryTheory.Limits.Pi.π (fun s : Triplet n => internalHomSheaf X (L.X s.p) (M.X s.q))
        ⟨t.p, t.q - 1, by have ht := t.hpq; omega⟩ ≫
      internalHomPost X (M.d (t.q - 1) t.q) +
    (n + 1).negOnePow •
      (CategoryTheory.Limits.Pi.π (fun s : Triplet n => internalHomSheaf X (L.X s.p) (M.X s.q))
          ⟨t.p + 1, t.q, by have ht := t.hpq; omega⟩ ≫
        internalHomPre X (L.d t.p (t.p + 1)))

/-- Postcomposition with `f` followed by postcomposition with `g` is postcomposition with
`f ≫ g`. -/
theorem internalHomPost_comp (X : RingedSite.{u, v, w})
    (A : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {B C D : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f : B ⟶ C) (g : C ⟶ D) :
    internalHomPost X (A := A) f ≫ internalHomPost X (A := A) g =
      internalHomPost X (A := A) (f ≫ g) := by
  ext U a
  rfl

private theorem internalHomPre_comp (X : RingedSite.{u, v, w})
    {A B C : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (D : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (f : A ⟶ B) (g : B ⟶ C) :
    internalHomPre X (C := D) g ≫ internalHomPre X (C := D) f =
      internalHomPre X (C := D) (f ≫ g) := by
  ext U a
  rfl

private theorem internalHomPrePost_commute (X : RingedSite.{u, v, w})
    {A B C D : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : A ⟶ B)
    (g : C ⟶ D) :
    internalHomPre X (C := C) f ≫ internalHomPost X (A := A) g =
      internalHomPost X (A := B) g ≫ internalHomPre X (C := D) f := by
  ext U a
  rfl

private theorem internalHomPost_zero (X : RingedSite.{u, v, w})
    (A B C : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomPost X (A := A) (0 : B ⟶ C) = 0 := by
  ext U a
  rfl

private theorem internalHomPre_zero (X : RingedSite.{u, v, w})
    (A B C : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomPre X (C := C) (0 : A ⟶ B) = 0 := by
  have hzero (U : X.C) :
      (restrFun X.O.obj U).map (0 : valOf X A ⟶ valOf X B) = 0 := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  ext U a
  show (restrFun X.O.obj (unop U)).map (0 : valOf X A ⟶ valOf X B) ≫
    (a : (restrFun X.O.obj (unop U)).obj (valOf X B) ⟶
      (restrFun X.O.obj (unop U)).obj (valOf X C)) = 0
  rw [hzero]
  exact zero_comp

private noncomputable abbrev sheafHomComplexObj (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex (SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ where
  X n := sheafHomTerm X L M n
  d n m := if h : n + 1 = m then
      sheafHomDifferential X L M n ≫ eqToHom (by rw [h]) else 0
  shape n m h := by
    change n + 1 ≠ m at h
    simp [h]
  d_comp_d' n m k := by
    by_cases h₁ : n + 1 = m
    · by_cases h₂ : m + 1 = k
      · subst m
        subst k
        simp only [dite_eq_left, eqToHom_refl, Category.comp_id]
        intro _ _
        apply CategoryTheory.Limits.Pi.hom_ext
        intro t
        simp [sheafHomDifferential, Category.assoc]
        simp only [internalHomPost_comp X (L.X t.p)
              (M.d (t.q - 1 - 1) (t.q - 1)) (M.d (t.q - 1) t.q),
            internalHomPrePost_commute X (L.d t.p (t.p + 1))
              (M.d (t.q - 1) t.q),
            internalHomPre_comp X (M.X t.q) (L.d t.p (t.p + 1))
              (L.d (t.p + 1) (t.p + 1 + 1)),
            M.d_comp_d, L.d_comp_d, Int.negOnePow_succ, Units.neg_smul,
            internalHomPost_zero, internalHomPre_zero]
        simp
      · simp [h₁, h₂]
    · simp [h₁]

/-- Restriction of sheaves of `O`-modules to the slice site over `U` preserves zero morphisms. -/
noncomputable local instance (X : RingedSite.{u, v, w}) (U : X.C) :
    (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).PreservesZeroMorphisms where
  map_zero {A B} := by
    ext V x
    rfl

/-- Taking sections over `U` of sheaves of abelian groups is an additive functor. -/
noncomputable local instance (X : RingedSite.{u, v, w}) (U : X.C) :
    (sheafToPresheaf X.J AddCommGrpCat.{m} ⋙
      (evaluation X.Cᵒᵖ AddCommGrpCat.{m}).obj (op U)).Additive where
  map_add := by intros; rfl

/-- Global sections of a sheaf of abelian groups, as compatible families of
sections. The target universe also includes the objects of the site. -/
@[sga "4½ Arcata 1.6.5"]
noncomputable def abelianGlobalSectionsFunctor (X : RingedSite.{u, v, w}) :
    Sheaf X.J AddCommGrpCat.{m} ⥤ AddCommGrpCat.{max u m} where
  obj F := AddCommGrpCat.of
    (show AddSubgroup (∀ U, F.obj.obj U) from
      AddGrpCat.sectionsAddSubgroup (F.obj ⋙ forget₂ AddCommGrpCat AddGrpCat))
  map f := AddCommGrpCat.ofHom
    { toFun := fun s ↦ ⟨fun U ↦ f.hom.app U (s.val U), by
        intro U V g
        exact (ConcreteCategory.congr_hom (f.hom.naturality g) (s.val U)).symm.trans
          (congrArg (f.hom.app V) (s.property g))⟩
      map_zero' := by ext U; exact map_zero _
      map_add' := by intros; ext U; exact map_add _ _ _ }
  map_id _ := by ext s U; rfl
  map_comp _ _ := by ext s U; rfl

/-- The global sections functor `abelianGlobalSectionsFunctor` is additive. -/
instance abelianGlobalSectionsFunctor_additive (X : RingedSite.{u, v, w}) :
    (abelianGlobalSectionsFunctor.{m} X).Additive where
  map_add := by intros; ext s; rfl

/-- The underlying complex of sheaves of abelian groups of a complex of module
sheaves. -/
noncomputable abbrev underlyingComplex (X : RingedSite.{u, v, w})
    (K : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex (Sheaf X.J AddCommGrpCat.{m}) ℤ :=
  ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- The complex obtained by forgetting the module structure and taking global
sections degreewise. -/
noncomputable abbrev globalSectionsComplex (X : RingedSite.{u, v, w})
    (K : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex AddCommGrpCat.{max u m} ℤ :=
  ((abelianGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (underlyingComplex X K)

/-- The complex obtained by evaluating a complex of module sheaves at `U` and
forgetting the module structure. -/
noncomputable abbrev sectionComplex (X : RingedSite.{u, v, w})
    (K : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) :
    CochainComplex AddCommGrpCat.{m} ℤ :=
  ((sheafToPresheaf X.J AddCommGrpCat.{m} ⋙
      (evaluation X.Cᵒᵖ AddCommGrpCat.{m}).obj (op U))
        |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj (underlyingComplex X K)

private noncomputable def localHomSectionEquiv (X : RingedSite.{u, v, w}) (U : X.C)
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((internalHom X.O.obj (valOf X A) (valOf X B)).obj (op U)) ≃+
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj A ⟶
        (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj B) where
  toFun f := ⟨f⟩
  invFun f := f.val
  left_inv := by intro f; rfl
  right_inv := by intro f; cases f; rfl
  map_add' := by intros; rfl

private theorem localHom_restrict_apply (X : RingedSite.{u, v, w})
    {U V W : X.C} (f : V ⟶ U) (g : W ⟶ V)
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s : (internalHom X.O.obj (valOf X A) (valOf X B)).obj (op U))
    (x : (A.val.obj (op W))) :
    (((localHomSectionEquiv X V A B
      ((internalHom X.O.obj (valOf X A) (valOf X B)).map f.op s)).val.app (op (Over.mk g))) x) =
    (((localHomSectionEquiv X U A B s).val.app (op (Over.mk (g ≫ f)))) x) := by
  rfl

private theorem localHom_smul_apply (X : RingedSite.{u, v, w})
    (U W : X.C) (r : X.O.obj.obj (op U))
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s : (internalHom X.O.obj (valOf X A) (valOf X B)).obj (op U)) (f : W ⟶ U)
    (x : (A.val.obj (op W))) :
    (((localHomSectionEquiv X U A B (r • s)).val.app (op (Over.mk f))) x) =
      (show ToType (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj
          (op (Over.mk f))) from
          (X.O.obj.map f.op).hom r) •
        (((localHomSectionEquiv X U A B s).val.app (op (Over.mk f))) x) := by
  rfl

/-- The underlying additive map of a morphism of abelian groups, in the spelling the
`ConcreteCategory` API uses. -/
private lemma addCommGrpCat_hom'_eq {A B : AddCommGrpCat.{i}} (f : A ⟶ B) :
    f.hom' = AddCommGrpCat.Hom.hom f := rfl

private noncomputable abbrev addCommGrpPiCone {I : Type i}
    (F : I → AddCommGrpCat.{max i m}) : Cone (Discrete.functor F) := {
    pt := AddCommGrpCat.of (∀ i, F i)
    π := {
      app := fun i => AddCommGrpCat.ofHom {
        toFun := fun x => x i.as
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
      naturality := by
        rintro ⟨i⟩ ⟨j⟩ ⟨h⟩
        cases h
        rfl } }

private noncomputable abbrev addCommGrpPiConeIsLimit {I : Type i}
    (F : I → AddCommGrpCat.{max i m}) : IsLimit (addCommGrpPiCone F) := {
    lift := fun s => AddCommGrpCat.ofHom <| AddMonoidHom.pi fun i => (s.π.app ⟨i⟩).hom
    fac := by
      intro s j
      cases j with
      | mk i => ext x; rfl
    uniq := fun s m hm => AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun x =>
      funext fun i => congrArg (fun f => f x) (hm ⟨i⟩) }

private noncomputable def addCommGrpPiIso {I : Type i}
    (F : I → AddCommGrpCat.{max i m}) :
    (∏ᶜ F) ≅ AddCommGrpCat.of (∀ i, F i) :=
  (Pi.isoLimit (Discrete.functor F)) ≪≫
    Limits.limit.isoLimitCone ⟨addCommGrpPiCone F, addCommGrpPiConeIsLimit F⟩

private theorem addCommGrpPiIso_hom_apply {I : Type i}
    (F : I → AddCommGrpCat.{max i m}) (x : ↑(∏ᶜ F)) (i : I) :
    (AddCommGrpCat.Hom.hom (addCommGrpPiIso F).hom x) i =
      AddCommGrpCat.Hom.hom (Pi.π F i) x := by
  have h : (addCommGrpPiIso F).hom ≫ (addCommGrpPiCone F).π.app ⟨i⟩ =
      Pi.π F i := by
    dsimp [addCommGrpPiIso]
    rw [Category.assoc, limit.isoLimitCone_hom_π, Pi.isoLimit_hom_π]
    rfl
  have hx := congrArg (fun f => (AddCommGrpCat.Hom.hom f) x) h
  simpa [addCommGrpPiCone] using hx

attribute [local simp] addCommGrpPiIso_hom_apply

/-- Sections over `U` of the underlying sheaf of abelian groups of a sheaf of modules. -/
private noncomputable abbrev sectionsFunctor (X : RingedSite.{u, v, w}) (U : X.C) :
    SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      AddCommGrpCat.{max u v m} :=
  SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    sheafToPresheaf X.J AddCommGrpCat.{max u v m} ⋙
      (evaluation X.Cᵒᵖ AddCommGrpCat.{max u v m}).obj (op U)

/-- Taking sections over `U` preserves products of sheaves of modules. -/
private theorem sectionsFunctor_preservesLimit (X : RingedSite.{u, v, w}) (U : X.C) (n : ℤ)
    (F : Triplet n → SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PreservesLimit (Discrete.functor F) (sectionsFunctor.{m} X U) := by
  let G : SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      AddCommGrpCat.{max u v m} :=
    SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U) ⋙
      forget₂ (ModuleCat (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj
          (op U))) AddCommGrpCat
  let : PreservesLimitsOfShape (Discrete (Triplet n))
      (SheafOfModules.evaluation.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) :=
    SheafOfModules.evaluationPreservesLimitsOfShape.{max u v m}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (D := Discrete (Triplet n)) (op U)
  let : PreservesLimit (Discrete.functor F) G := comp_preservesLimit _ _
  exact preservesLimit_of_natIso (Discrete.functor F)
    (NatIso.ofComponents (F := G) (G := sectionsFunctor.{m} X U) (fun _ => Iso.refl _)
      (by intro A B f; rfl))

private noncomputable def localTermIso (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (n : ℤ) :
    (sectionComplex X (sheafHomComplexObj X L M) U).X n ≅
      ((restrictComplex X L U).HomComplex (restrictComplex X M U)).X n := by
  let F : Triplet n → SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    fun t => internalHomSheaf X (L.X t.p) (M.X t.q)
  have := sectionsFunctor_preservesLimit.{m} X U n F
  let G' := sectionsFunctor.{m} X U
  let e₁ := preservesLimitIso G' (Discrete.functor F)
  let H₁ : Triplet n → AddCommGrpCat.{max u v m} := fun t => G'.obj (F t)
  let H₂ : Triplet n → AddCommGrpCat.{max u v m} := fun t =>
    AddCommGrpCat.of ((restrictComplex X L U).X t.p ⟶ (restrictComplex X M U).X t.q)
  let d₁ := Discrete.functor F ⋙ G'
  let d₂ := Discrete.functor H₁
  let e₁₂ : d₁ ≅ d₂ := NatIso.ofComponents (fun _ => Iso.refl _) (by
    rintro ⟨a⟩ ⟨b⟩ ⟨h⟩
    cases h
    rfl)
  let e₂ : (∏ᶜ H₁) ≅ (∏ᶜ H₂) :=
    Limits.Pi.mapIso (fun t : Triplet n =>
      (localHomSectionEquiv X U (L.X t.p) (M.X t.q)).toAddCommGrpIso)
  let e₃ : (∏ᶜ H₂) ≅ AddCommGrpCat.of
      (Cochain (restrictComplex X L U) (restrictComplex X M U) n) :=
    (addCommGrpPiIso H₂).trans (Iso.refl _)
  change G'.obj (∏ᶜ F) ≅ AddCommGrpCat.of
    (Cochain (restrictComplex X L U) (restrictComplex X M U) n)
  exact e₁ ≪≫ Limits.HasLimit.isoOfNatIso e₁₂ ≪≫ e₂ ≪≫ e₃

-- Elaborating the product comparison unfolds the section and restriction functors.
private theorem localTermIso_hom_apply (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (n : ℤ)
    (s : ↑((sectionComplex X (sheafHomComplexObj X L M) U).X n)) (t : Triplet n) :
    ((AddCommGrpCat.Hom.hom (localTermIso X L M U n).hom s) t) =
      (localHomSectionEquiv X U (L.X t.p) (M.X t.q)).toFun
        (((Pi.π (fun a : Triplet n => internalHomSheaf X (L.X a.p) (M.X a.q)) t).val.app
          (op U)).hom s) := by
  let F : Triplet n → SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    fun t => internalHomSheaf X (L.X t.p) (M.X t.q)
  have := sectionsFunctor_preservesLimit.{m} X U n F
  let G' := sectionsFunctor.{m} X U
  simp only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj, ObjectProperty.ι_obj,
    evaluation_obj_obj, CommRingCat.forgetToRingCat_obj, AddEquiv.toEquiv_eq_coe,
    Equiv.toFun_as_coe, EquivLike.coe_coe]
  show (AddCommGrpCat.Hom.hom (addCommGrpPiIso _).hom _ ) _ = _
  rw [addCommGrpPiIso_hom_apply]
  simp only [addCommGrpCat_hom'_eq]
  rw [← AddCommGrpCat.comp_apply, Pi.mapIso_hom_π]
  rw [← AddCommGrpCat.comp_apply, ← Category.assoc, HasLimit.isoOfNatIso_hom_π]
  simp only [NatIso.ofComponents_hom_app, Iso.refl_hom]
  rw [← AddCommGrpCat.comp_apply]
  rw [← Category.assoc]
  rw [CategoryTheory.preservesLimitIso_hom_π_assoc
    (G := G') (F := Discrete.functor F) (Discrete.mk t)]
  simp [Category.assoc]
  rfl

private lemma sheafModuleHom_zsmul_val {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {A B : SheafOfModules.{m} R} (f : A ⟶ B) (k : ℤ) :
    (k • f).val = k • f.val := by
  show (SheafOfModules.forget R).map (k • f) = _
  rw [Functor.map_zsmul]
  rfl

private theorem sheafHomDifferential_projection_apply (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) (U : X.C)
    (s : (sheafHomTerm X L M n).val.obj (op U)) (t : Triplet (n + 1)) :
    (((Pi.π (fun a : Triplet (n + 1) =>
      internalHomSheaf X (L.X a.p) (M.X a.q)) t).val.app (op U)).hom
        (((sheafHomDifferential X L M n).val.app (op U)).hom s)) =
      (((internalHomPost X (M.d (t.q - 1) t.q)).val.app (op U)).hom
        (((Pi.π (fun a : Triplet n =>
          internalHomSheaf X (L.X a.p) (M.X a.q))
            ⟨t.p, t.q - 1, by have ht := t.hpq; omega⟩).val.app (op U)).hom s)) +
    (n + 1).negOnePow •
        (((internalHomPre X (L.d t.p (t.p + 1))).val.app (op U)).hom
          (((Pi.π (fun a : Triplet n =>
            internalHomSheaf X (L.X a.p) (M.X a.q))
              ⟨t.p + 1, t.q, by have ht := t.hpq; omega⟩).val.app (op U)).hom s)) := by
  have hcomp :
      sheafHomDifferential X L M n ≫
          Pi.π (fun a : Triplet (n + 1) => internalHomSheaf X (L.X a.p) (M.X a.q)) t =
        (Pi.π (fun a : Triplet n => internalHomSheaf X (L.X a.p) (M.X a.q))
              ⟨t.p, t.q - 1, by have ht := t.hpq; omega⟩ ≫
            internalHomPost X (M.d (t.q - 1) t.q)) +
          (n + 1).negOnePow •
            (Pi.π (fun a : Triplet n => internalHomSheaf X (L.X a.p) (M.X a.q))
                ⟨t.p + 1, t.q, by have ht := t.hpq; omega⟩ ≫
              internalHomPre X (L.d t.p (t.p + 1))) := by
    simp [sheafHomDifferential]
  calc
    _ = (((sheafHomDifferential X L M n ≫
          Pi.π (fun a : Triplet (n + 1) => internalHomSheaf X (L.X a.p) (M.X a.q)) t).val.app
          (op U)).hom s) := by
        simp [SheafOfModules.comp_val, PresheafOfModules.comp_app]
    _ = _ := by
      simpa [SheafOfModules.add_val, SheafOfModules.comp_val, Units.smul_def,
        PresheafOfModules.add_app, PresheafOfModules.comp_app,
        PresheafOfModules.zsmul_app, sheafModuleHom_zsmul_val, ModuleCat.hom_add,
        LinearMap.add_apply, LinearMap.smul_apply] using
        congrArg (fun f => (f.val.app (op U)).hom s) hcomp

-- Elaborating the product comparison unfolds the section and restriction functors.
private noncomputable def localHomComplexIso (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) :
    sectionComplex X (sheafHomComplexObj X L M) U ≅
      (restrictComplex X L U).HomComplex (restrictComplex X M U) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => localTermIso X L M U n) (by
    intro n m hnm
    have hnm' : n + 1 = m := hnm
    subst m
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply Cochain.ext
    intro p q hpq
    simp only [sectionComplex, underlyingComplex, Functor.mapHomologicalComplex_obj_d,
      sheafHomComplexObj, dite_eq_left, eqToHom_refl, Category.comp_id]
    change (δ n (n + 1)
        (show Cochain (restrictComplex X L U) (restrictComplex X M U) n from
          (localTermIso X L M U n).hom s)).v p q hpq =
      (show Cochain (restrictComplex X L U) (restrictComplex X M U) (n + 1) from
        (localTermIso X L M U (n + 1)).hom
          (((sheafHomDifferential X L M n).val.app (op U)).hom s)).v p q hpq
    rw [δ_v n (n + 1) rfl _ p q hpq (q - 1) (p + 1) rfl rfl]
    simp only [Cochain.v, localTermIso_hom_apply]
    rw [show (ConcreteCategory.hom (localTermIso X L M U (n + 1)).hom)
          (((sheafHomDifferential X L M n).val.app (op U)).hom s) ⟨p, q, hpq⟩ =
        (localHomSectionEquiv X U (L.X p) (M.X q)).toFun
          (((Pi.π (fun a : Triplet (n + 1) =>
              internalHomSheaf X (L.X a.p) (M.X a.q)) ⟨p, q, hpq⟩).val.app (op U)).hom
            (((sheafHomDifferential X L M n).val.app (op U)).hom s)) from
      localTermIso_hom_apply X L M U (n + 1)
        (((sheafHomDifferential X L M n).val.app (op U)).hom s) ⟨p, q, hpq⟩]
    rw [sheafHomDifferential_projection_apply X L M n U s ⟨p, q, hpq⟩]
    rfl)

private theorem localHomComplexIso_component_apply (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (n : ℤ)
    (s : ↑((sectionComplex X (sheafHomComplexObj X L M) U).X n))
    (t : Triplet n) (W : X.C) (g : W ⟶ U)
    (x : (L.X t.p).val.obj (op W)) :
    let hs := (((Pi.π (fun a : Triplet n =>
      internalHomSheaf X (L.X a.p) (M.X a.q)) t).val.app (op U)).hom s)
    (((AddCommGrpCat.Hom.hom ((localHomComplexIso X L M U).hom.f n) s).v
        t.p t.q t.hpq).val.app (op (Over.mk g))) x =
      (((localHomSectionEquiv X U (L.X t.p) (M.X t.q) hs).val.app
        (op (Over.mk g))) x) := by
  show (((AddCommGrpCat.Hom.hom (localTermIso X L M U n).hom s) t).val.app
      (op (Over.mk g))) x = _
  rw [localTermIso_hom_apply]
  rfl

private theorem sheafHomTerm_map_pi_app (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) {U V : X.C}
    (f : V ⟶ U) (s : (sheafHomTerm X L M n).val.obj (op U)) (t : Triplet n) :
    ((Pi.π (fun a : Triplet n => internalHomSheaf X (L.X a.p) (M.X a.q)) t).val.app
      (op V)).hom ((sheafHomTerm X L M n).val.map f.op s) =
    (internalHomSheaf X (L.X t.p) (M.X t.q)).val.map f.op
      (((Pi.π (fun a : Triplet n => internalHomSheaf X (L.X a.p) (M.X a.q)) t).val.app
        (op U)).hom s) := by
  have h := (Pi.π
    (fun a : Triplet n => internalHomSheaf X (L.X a.p) (M.X a.q)) t).val.naturality f.op
  exact congrArg (fun g => (ConcreteCategory.hom g) s) h

private noncomputable def homCone (X : RingedSite.{u, v, w})
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Cone ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (internalHomSheaf X A B)).obj where
  pt := AddCommGrpCat.of (ULift.{v} (A ⟶ B))
  π := {
    app := fun U => AddCommGrpCat.ofHom {
      toFun := fun f => (restrFun X.O.obj U.unop).map (homOf X f.down)
      map_zero' := by rfl
      map_add' := by intros; rfl }
    naturality := by
      intro U V f
      ext a
      rfl }

/-- The components of a cone over the sections of `SheafHom(A, B)` at the identity of `V` and at
`f : V ⟶ U` are related by restriction. -/
private theorem cone_app_id_eq (X : RingedSite.{u, v, w})
    {A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (s : Cone ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (internalHomSheaf X A B)).obj)
    (x : s.pt) {U V : X.C} (f : V ⟶ U) (a : A.val.obj (op V)) :
    (((s.π.app (op V)) x).app (op (Over.mk (𝟙 V)))) a =
      (((s.π.app (op U)) x).app (op (Over.mk f))) a := by
  have h := congrArg (fun k => k x) (s.w f.op)
  change (internalHom X.O.obj (valOf X A) (valOf X B)).map f.op ((s.π.app (op U)) x) =
    (s.π.app (op V)) x at h
  rw [← h]
  exact congrArg (fun k => k a) (presheafHom_map_app_op_mk_id
    (F := A.val.presheaf) (G := B.val.presheaf) f
    ((PresheafOfModules.toPresheaf _).map ((s.π.app (op U)) x)))

private noncomputable def homOfCone (X : RingedSite.{u, v, w})
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s : Cone ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (internalHomSheaf X A B)).obj)
    (x : s.pt) : A ⟶ B :=
  ⟨{ app := fun U => ((s.π.app U) x).app (op (Over.mk (𝟙 U.unop)))
     naturality := by
       rintro ⟨U⟩ ⟨V⟩ ⟨f : V ⟶ U⟩
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro a
       change (((s.π.app (op V)) x).app (op (Over.mk (𝟙 V)))) (A.val.map f.op a) =
         B.val.map f.op ((((s.π.app (op U)) x).app (op (Over.mk (𝟙 U)))) a)
       exact (cone_app_id_eq X s x f _).trans (PresheafOfModules.naturality_apply
         ((s.π.app (op U)) x) (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 U)).op a) }⟩

private noncomputable def homConeIsLimit (X : RingedSite.{u, v, w})
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsLimit (homCone X A B) where
  lift s := AddCommGrpCat.ofHom {
    toFun := fun x ↦ ULift.up (homOfCone X A B s x)
    map_zero' := by
      apply ULift.ext
      ext U a
      change (((s.π.app U) 0).app (op (Over.mk (𝟙 U.unop)))) a = 0
      rw [map_zero]
      rfl
    map_add' := by
      intro x y
      apply ULift.ext
      ext U a
      change (((s.π.app U) (x + y)).app (op (Over.mk (𝟙 U.unop)))) a = _
      rw [map_add]
      rfl }
  fac s U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply PresheafOfModules.hom_ext
    intro V
    ext a
    change (((s.π.app (op V.unop.left)) x).app
      (op (Over.mk (𝟙 V.unop.left)))) a = (((s.π.app U) x).app V) a
    exact cone_app_id_eq X s x V.unop.hom a

  uniq s m hm := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply ULift.ext
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext a
    exact congrArg (fun k => k.app (op (Over.mk (𝟙 U.unop))) a) (congrArg (fun k => k x) (hm U))

section

variable (X : RingedSite.{u, v, w})

/-- The cone of evaluations of a compatible family of global sections. -/
private abbrev compatibleSectionsCone (F : Sheaf X.J AddCommGrpCat.{max u v m}) : Cone F.obj where
  pt := (abelianGlobalSectionsFunctor X).obj F
  π :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ s.val U
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := by
        intro U V f
        ext s
        exact (s.property f).symm }

/-- Compatible families satisfy the universal property of global sections. -/
private noncomputable def compatibleSectionsIsLimit (F : Sheaf X.J AddCommGrpCat.{max u v m}) :
    IsLimit (compatibleSectionsCone.{m} X F) where
  lift c := AddCommGrpCat.ofHom
    { toFun := fun s ↦ ⟨fun U ↦ c.π.app U s, by
        intro U V f
        exact (ConcreteCategory.congr_hom (c.w f) s)⟩
      map_zero' := by ext U; exact map_zero _
      map_add' := by intros; ext U; exact map_add _ _ _ }
  fac c U := by ext s; rfl
  uniq c f hf := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact Subtype.ext (funext fun U ↦ ConcreteCategory.congr_hom (hf U) s)

/-- Compatible global sections agree with the limit of the underlying presheaf. -/
private noncomputable def compatibleSectionsIsoLim : abelianGlobalSectionsFunctor.{max u v m} X ≅
    sheafToPresheaf X.J AddCommGrpCat.{max u v m} ⋙ lim :=
  NatIso.ofComponents
    (fun F ↦ (compatibleSectionsIsLimit.{m} X F).conePointUniqueUpToIso
      (limit.isLimit F.obj)) (by
        intro F G f
        apply (limit.isLimit G.obj).hom_ext
        intro U
        simp [limMap_π, Category.assoc]
        rfl)

end

private noncomputable def globalHomIso (X : RingedSite.{u, v, w})
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (abelianGlobalSectionsFunctor X).obj
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
          (internalHomSheaf X A B)) ≅
        AddCommGrpCat.of (ULift.{v} (A ⟶ B)) :=
  IsLimit.conePointUniqueUpToIso (compatibleSectionsIsLimit.{m} X _) (homConeIsLimit X A B)

private noncomputable abbrev moduleΓ (X : RingedSite.{u, v, w}) :=
  SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      abelianGlobalSectionsFunctor.{max u v m} X

private theorem globalHomIso_hom_app (X : RingedSite.{u, v, w})
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s : (moduleΓ.{m} X).obj (internalHomSheaf X A B)) (U : X.Cᵒᵖ)
    (x : A.val.obj U) :
    (((globalHomIso X A B).hom s).down.val.app U) x =
      ((s.val U).app (op (Over.mk (𝟙 U.unop)))) x := rfl

private theorem globalHomIso_post (X : RingedSite.{u, v, w})
    (A : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {B C : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : B ⟶ C)
    (s : (moduleΓ.{m} X).obj (internalHomSheaf X A B)) :
    ((globalHomIso X A C).hom ((moduleΓ.{m} X).map (internalHomPost X f) s)).down =
      ((globalHomIso X A B).hom s).down ≫ f := by
  ext U x
  rfl

private theorem globalHomIso_pre (X : RingedSite.{u, v, w})
    {A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (C : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (f : A ⟶ B)
    (s : (moduleΓ.{m} X).obj (internalHomSheaf X B C)) :
    ((globalHomIso X A C).hom ((moduleΓ.{m} X).map (internalHomPre X f) s)).down =
      f ≫ ((globalHomIso X B C).hom s).down := by
  ext U x
  rfl

private theorem moduleΓ_preservesProduct
    (X : RingedSite.{u, v, w}) {I : Type i} [Small.{max u v m} I]
    (F : I → SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PreservesLimit (Discrete.functor F) (moduleΓ.{m} X) := by
  let : PreservesLimitsOfShape (Discrete I)
      (SheafOfModules.forget.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    SheafOfModules.forgetPreservesLimitsOfShape (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (D := Discrete I)
  let : PreservesLimit (Discrete.functor F)
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙ sheafToPresheaf X.J
          AddCommGrpCat) := by
    show PreservesLimit (Discrete.functor F)
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
          PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    exact comp_preservesLimit _ _
  let : PreservesLimit (Discrete.functor F)
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    preservesLimit_of_reflects_of_preserves
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (sheafToPresheaf X.J AddCommGrpCat)
  let : PreservesLimit (Discrete.functor F)
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        sheafToPresheaf X.J AddCommGrpCat.{max u v m} ⋙ lim) :=
    inferInstance
  exact preservesLimit_of_natIso (Discrete.functor F)
    (Functor.isoWhiskerLeft (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (compatibleSectionsIsoLim.{m} X).symm)

private noncomputable def globalTermIso (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (globalSectionsComplex X (sheafHomComplexObj X L M)).X n ≅
      AddCommGrpCat.uliftFunctor.{v}.obj ((L.HomComplex M).X n) := by
  let F : Triplet n → SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    fun t => internalHomSheaf X (L.X t.p) (M.X t.q)
  let G := moduleΓ.{m} X
  let : PreservesLimit (Discrete.functor F) G := moduleΓ_preservesProduct.{m} X F
  let H₁ : Triplet n → AddCommGrpCat.{max u v m} := fun t => G.obj (F t)
  let H₂ : Triplet n → AddCommGrpCat.{max u v m} := fun t =>
    AddCommGrpCat.of (ULift.{v} (L.X t.p ⟶ M.X t.q))
  let e₁₂ : Discrete.functor F ⋙ G ≅ Discrete.functor H₁ :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      rintro ⟨a⟩ ⟨b⟩ ⟨h⟩
      cases h
      simp)
  exact preservesLimitIso G (Discrete.functor F) ≪≫
    HasLimit.isoOfNatIso e₁₂ ≪≫
    Pi.mapIso (fun t => globalHomIso X (L.X t.p) (M.X t.q)) ≪≫
    addCommGrpPiIso H₂ ≪≫
    ((AddEquiv.piCongrRight fun _ ↦ AddEquiv.ulift).trans AddEquiv.ulift.symm).toAddCommGrpIso

-- Elaborating the product comparison unfolds the section and restriction functors.
private theorem globalTermIso_hom_apply (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (s : (globalSectionsComplex X (sheafHomComplexObj X L M)).X n) (t : Triplet n) :
    ((globalTermIso X L M n).hom s).down t =
      ((globalHomIso X (L.X t.p) (M.X t.q)).hom
        ((moduleΓ.{m} X).map
          (Pi.π (fun a : Triplet n => internalHomSheaf X (L.X a.p) (M.X a.q)) t) s)).down := by
  dsimp only [globalTermIso, Iso.trans_hom]
  simp only [AddCommGrpCat.comp_apply]
  show (AddCommGrpCat.Hom.hom
    (addCommGrpPiIso (fun t : Triplet n =>
      AddCommGrpCat.of (ULift.{v} (L.X t.p ⟶ M.X t.q)))).hom _ t).down = _
  rw [addCommGrpPiIso_hom_apply]
  rw [← AddCommGrpCat.comp_apply, Pi.mapIso_hom_π]
  rw [AddCommGrpCat.comp_apply]
  congr 2
  rw [← AddCommGrpCat.comp_apply, HasLimit.isoOfNatIso_hom_π]
  simp only [NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id]
  rw [← AddCommGrpCat.comp_apply, preservesLimitIso_hom_π]

private theorem globalDifferential_projection_apply (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (s : (moduleΓ.{m} X).obj (sheafHomTerm X L M n)) (t : Triplet (n + 1)) :
    (moduleΓ.{m} X).map
      (Pi.π (fun a : Triplet (n + 1) => internalHomSheaf X (L.X a.p) (M.X a.q)) t)
      ((moduleΓ.{m} X).map (sheafHomDifferential X L M n) s) =
    (moduleΓ.{m} X).map (internalHomPost X (M.d (t.q - 1) t.q))
      ((moduleΓ.{m} X).map
        (Pi.π (fun a : Triplet n => internalHomSheaf X (L.X a.p) (M.X a.q))
          ⟨t.p, t.q - 1, by have ht := t.hpq; omega⟩) s) +
    (n + 1).negOnePow •
      (moduleΓ.{m} X).map (internalHomPre X (L.d t.p (t.p + 1)))
        ((moduleΓ.{m} X).map
          (Pi.π (fun a : Triplet n => internalHomSheaf X (L.X a.p) (M.X a.q))
            ⟨t.p + 1, t.q, by have ht := t.hpq; omega⟩) s) := by
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp]
  simp only [sheafHomDifferential, Pi.lift_comp_π, Functor.map_add, Units.smul_def,
    Functor.map_zsmul, Functor.map_comp]
  rfl

private noncomputable def globalHomComplexIso (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    globalSectionsComplex X (sheafHomComplexObj X L M) ≅
      (AddCommGrpCat.uliftFunctor.{v}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (L.HomComplex M) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => globalTermIso X L M n) (by
    intro n m hnm
    have hnm' : n + 1 = m := hnm
    subst m
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply ULift.ext
    apply Cochain.ext
    intro p q hpq
    simp only [globalSectionsComplex, underlyingComplex, Functor.mapHomologicalComplex_obj_d,
      sheafHomComplexObj, dite_eq_left, eqToHom_refl, Category.comp_id]
    change (δ n (n + 1)
        (show Cochain L M n from ((globalTermIso X L M n).hom s).down)).v p q hpq =
      (show Cochain L M (n + 1) from
        ((globalTermIso X L M (n + 1)).hom
          ((moduleΓ.{m} X).map (sheafHomDifferential X L M n) s)).down).v p q hpq
    rw [δ_v n (n + 1) rfl _ p q hpq (q - 1) (p + 1) rfl rfl]
    simp only [Cochain.v, globalTermIso_hom_apply]
    rw [globalDifferential_projection_apply]
    simp only [map_add, Units.smul_def, map_zsmul, ULift.add_down, ULift.smul_down]
    rw [globalHomIso_post, globalHomIso_pre])

/-- A realization of the internal sheaf Hom complex. Its sections over every object are the
ordinary Hom complex of the restrictions, and the local identifications are compatible with
restriction. -/
structure SheafHomComplex (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) where
  /-- The internal Hom complex of sheaves of modules. -/
  obj : CochainComplex (SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ
  /-- Sections on an object are the Hom complex of the restrictions to its
  slice site. -/
  sectionsIso : ∀ U : X.C,
    sectionComplex X obj U ≅ (restrictComplex X L U).HomComplex (restrictComplex X M U)
  /-- The local descriptions commute with restriction along arrows of the site. -/
  restrict_natural : ∀ {U V : X.C} (f : V ⟶ U) (n p q : ℤ)
      (hpq : p + n = q) (s : (obj.X n).val.obj (op U))
      {W : X.C} (g : W ⟶ V) (x : (L.X p).val.obj (op W)),
    (((AddCommGrpCat.Hom.hom ((sectionsIso U).hom.f n) s).v p q hpq).val.app
        (op (Over.mk (g ≫ f))) x) =
      (((AddCommGrpCat.Hom.hom ((sectionsIso V).hom.f n)
        ((obj.X n).val.map f.op s)).v p q hpq).val.app (op (Over.mk g)) x)
  /-- The local descriptions respect multiplication by sections of the
  commutative structure sheaf. -/
  smul_natural : ∀ (U : X.C) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
      (n p q : ℤ) (hpq : p + n = q) (s : (obj.X n).val.obj (op U))
      {W : X.C} (f : W ⟶ U) (x : (L.X p).val.obj (op W)),
    (((AddCommGrpCat.Hom.hom ((sectionsIso U).hom.f n) (r • s)).v p q hpq).val.app
        (op (Over.mk f))) x =
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op r) •
        (show (M.X q).val.obj (op W) from
          (((AddCommGrpCat.Hom.hom ((sectionsIso U).hom.f n) s).v p q hpq).val.app
            (op (Over.mk f))) x)
  /-- Globally, sections of the internal Hom complex form the ordinary Hom
  complex, lifted to the universe of the local section complexes. -/
  globalSectionsIso : globalSectionsComplex X obj ≅
    (AddCommGrpCat.uliftFunctor.{v}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (L.HomComplex M)

/-- The canonical internal sheaf Hom complex `SheafHom•(L, M)`: in degree `n` its sections over
an object `U` are the degree-`n` cochains from `L|_U` to `M|_U`, that is the product over the
pairs `p + n = q` of the sections of `SheafHom(L^p, M^q)`, with the differential
`d(f) = d_M ∘ f - (-1)^n f ∘ d_L`, together with its description on every slice site and the
compatibility of these descriptions. -/
@[stacks 0A8X, no_expose]
noncomputable def sheafHomComplex (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
        SheafHomComplex X L M :=
  {
      obj := sheafHomComplexObj X L M
      sectionsIso := fun U => localHomComplexIso X L M U
      restrict_natural := by
        intro U V f n p q hpq s W g x
        let t : Triplet n := ⟨p, q, hpq⟩
        change (((AddCommGrpCat.Hom.hom ((localHomComplexIso X L M U).hom.f n) s).v
            p q hpq).val.app (op (Over.mk (g ≫ f)))) x = _
        rw [localHomComplexIso_component_apply X L M U n s t W (g ≫ f) x]
        dsimp [sheafHomComplexObj]
        change
          (localHomSectionEquiv X U (L.X p) (M.X q)
            (((Pi.π (fun a : Triplet n =>
              internalHomSheaf X (L.X a.p) (M.X a.q)) t).val.app (op U)).hom s)).val.app
              (op (Over.mk (g ≫ f))) x =
          (((AddCommGrpCat.Hom.hom ((localHomComplexIso X L M V).hom.f n)
            ((sheafHomTerm X L M n).val.map f.op s)).v p q hpq).val.app
            (op (Over.mk g))) x
        rw [localHomComplexIso_component_apply X L M V n
          ((sheafHomTerm X L M n).val.map f.op s) t W g x]
        rw [sheafHomTerm_map_pi_app]
        exact (localHom_restrict_apply X f g (L.X p) (M.X q)
          (((Pi.π (fun a : Triplet n => internalHomSheaf X (L.X a.p) (M.X a.q)) t).val.app
            (op U)).hom s) x).symm
      smul_natural := by
        intro U r n p q hpq s W f x
        let t : Triplet n := ⟨p, q, hpq⟩
        change (((AddCommGrpCat.Hom.hom ((localHomComplexIso X L M U).hom.f n)
            (r • s)).v p q hpq).val.app (op (Over.mk f))) x = _
        rw [localHomComplexIso_component_apply X L M U n (r • s) t W f x]
        rw [localHomComplexIso_component_apply X L M U n s t W f x]
        rw [map_smul]
        exact localHom_smul_apply X U W r (L.X p) (M.X q)
          (((Pi.π (fun a : Triplet n => internalHomSheaf X (L.X a.p) (M.X a.q)) t).val.app
            (op U)).hom s) f x
      globalSectionsIso := globalHomComplexIso X L M }

/-- The internal Hom complex of `sheafHomComplex` is the explicit complex
`sheafHomComplexObj`. -/
private theorem sheafHomComplex_obj (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (sheafHomComplex X L M).obj = sheafHomComplexObj X L M := rfl

/-- The local descriptions of `sheafHomComplex` are the explicit isomorphisms
`localHomComplexIso`. -/
private theorem sheafHomComplex_sectionsIso (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) :
    (sheafHomComplex X L M).sectionsIso U = localHomComplexIso X L M U := rfl

/-- The global description of `sheafHomComplex` is the explicit isomorphism
`globalHomComplexIso`. -/
private theorem sheafHomComplex_globalSectionsIso (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (sheafHomComplex X L M).globalSectionsIso = globalHomComplexIso X L M := rfl

private theorem globalTermIso_v_app (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n p q : ℤ) (hpq : p + n = q)
    (s : (globalSectionsComplex X (sheafHomComplexObj X L M)).X n) (U : X.C)
    (x : (L.X p).val.obj (op U)) :
    (((AddCommGrpCat.Hom.hom (globalTermIso X L M n).hom s).down.v p q hpq).val.app
        (op U)) x =
      (((AddCommGrpCat.Hom.hom ((localHomComplexIso X L M U).hom.f n)
          (s.val (op U))).v p q hpq).val.app (op (Over.mk (𝟙 U)))) x := by
  refine Eq.trans ?_
    (localHomComplexIso_component_apply X L M U n (s.val (op U)) ⟨p, q, hpq⟩ U (𝟙 U) x).symm
  simp only [Cochain.v, globalTermIso_hom_apply]
  rw [globalHomIso_hom_app]
  rfl

/-- A global section of the internal Hom complex is the compatible family of its sections, so
the cochain `L ⟶ M` it determines has, at each object `U`, the same value as the cochain
`L|_U ⟶ M|_U` determined by its sections over `U`, evaluated at the identity of `U`. -/
theorem sheafHomComplex_globalSectionsIso_v_app (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n p q : ℤ) (hpq : p + n = q)
    (s : (globalSectionsComplex X (sheafHomComplex X L M).obj).X n) (U : X.C)
    (x : (L.X p).val.obj (op U)) :
    (((AddCommGrpCat.Hom.hom ((sheafHomComplex X L M).globalSectionsIso.hom.f n) s).down.v
        p q hpq).val.app (op U)) x =
      (((AddCommGrpCat.Hom.hom (((sheafHomComplex X L M).sectionsIso U).hom.f n)
          (s.val (op U))).v p q hpq).val.app (op (Over.mk (𝟙 U)))) x :=
  globalTermIso_v_app X L M n p q hpq s U x


/-- The `n`-th cohomology of the global sections of the internal sheaf Hom complex from `L` to
`M` is canonically the group of morphisms from `L` to `M[n]` in the homotopy category. -/
@[stacks 0A8Z]
noncomputable def sheafHomComplexHomologyEquivHomotopyCategory
    (X : RingedSite.{u, v, w})
    (L M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (globalSectionsComplex X (sheafHomComplex X L M).obj).homology n ≃+
      ((HomotopyCategory.quotient (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).obj (M⟦n⟧)) := by
  let e := (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
    (sheafHomComplex X L M).globalSectionsIso
  refine e.addCommGroupIsoToAddEquiv.trans ?_
  let eLift := ((L.HomComplex M).sc n).mapHomologyIso AddCommGrpCat.uliftFunctor.{v}
  exact eLift.addCommGroupIsoToAddEquiv.trans <|
    AddEquiv.ulift.trans <|
      (CochainComplex.HomComplex.homologyAddEquiv L M n).trans
        CochainComplex.HomComplex.CohomologyClass.homAddEquiv


/-- The `n`-th cohomology of the sections over `U` of the internal Hom complex from `L` to `M`
is the group of morphisms `L|_U ⟶ M|_U[n]` in the homotopy category of `O|_U`-modules. -/
@[stacks 0A8Y]
def sheafHomComplexSectionHomologyEquivHomotopyCategory
    (X : RingedSite.{u, u, u})
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (n : ℤ) :
    (sectionComplex X (sheafHomComplex X L M).obj U).homology n ≃+
    ((HomotopyCategory.quotient
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
          (ComplexShape.up ℤ)).obj
            (restrictComplex X L U) ⟶
        (HomotopyCategory.quotient
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
          (ComplexShape.up ℤ)).obj
            ((restrictComplex X M U)⟦n⟧)) :=
  let H := sheafHomComplex X L M
  let e := H.sectionsIso U
  let eHomology := (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso e
  eHomology.addCommGroupIsoToAddEquiv |>.trans <|
    (CochainComplex.HomComplex.homologyAddEquiv
      (restrictComplex X L U) (restrictComplex X M U) n).trans <|
      CochainComplex.HomComplex.CohomologyClass.homAddEquiv

end AlgebraicGeometry.RingedSite

end
