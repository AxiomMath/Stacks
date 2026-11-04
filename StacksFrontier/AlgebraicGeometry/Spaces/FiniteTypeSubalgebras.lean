module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Finite type quasi-coherent subalgebras of an algebra on an algebraic space

The vocabulary of Stacks 082B — the category of finite type quasi-coherent subalgebras of an
algebra sheaf on the small étale site of an algebraic space, its inclusion diagram and the
canonical cocone of inclusions — together with the fact that makes that vocabulary usable: a
monomorphism of algebra sheaves is injective on sections.

That fact is what the reduction of Stacks 082C(1) to Stacks 082B in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteAlgebraColimits.lean` carried as an unproved
hypothesis `hinj`.  It is discharged here, so the two assertions of Stacks 082C(1) now follow
from the two assertions of Stacks 082B with no side condition.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.kernelPair` is the kernel pair of a morphism of algebra
  sheaves: the fibre product of the underlying sheaves of rings, made an algebra sheaf by the
  diagonal.  `AlgebraicGeometry.Space.AlgebraSheaf.kernelPairFst` and
  `AlgebraicGeometry.Space.AlgebraSheaf.kernelPairSnd` are its two projections and
  `AlgebraicGeometry.Space.AlgebraSheaf.ringDiagonal` the diagonal itself.
* `AlgebraicGeometry.Space.FiniteTypeSubalgebra` is the category of finite type quasi-coherent
  subalgebras of an algebra sheaf, `AlgebraicGeometry.Space.finiteTypeSubalgebraDiagram` its
  inclusion diagram and `AlgebraicGeometry.Space.finiteTypeSubalgebraCocone` the canonical
  cocone of inclusions with vertex the ambient algebra.  These are the three objects Stacks
  082B is about.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.mono_right_of_mono`: the forgetful functor
  `AlgebraicGeometry.Space.AlgebraSheaf.forget` *preserves* monomorphisms, and
  `AlgebraicGeometry.Space.AlgebraSheaf.injective_app_of_mono`: a monomorphism of algebra
  sheaves is injective on the sections over every object of the small étale site.  In
  particular `AlgebraicGeometry.Space.AlgebraSheaf.injective_subobject_arrow_app`: the arrow of
  a subobject is sectionwise injective.
* In the namespace `AlgebraicGeometry.Space`, the primed names
  `isFinite_subobject_iff_isFiniteType'`,
  `isQuasicoherentAndIsFinite_eq_isQuasicoherentAndIsFiniteType'`,
  `isFiltered_finiteSubalgebra_of_isFiltered_finiteTypeSubalgebra'` and
  `isColimit_finiteSubalgebraCocone_of_isColimit_finiteTypeSubalgebraCocone'`
  are the four statements of `FiniteAlgebraColimits.lean` with `hinj` discharged; the last two
  are **Stacks 082C(1) deduced from Stacks 082B**, stated against
  `AlgebraicGeometry.Space.FiniteTypeSubalgebra` and
  `AlgebraicGeometry.Space.finiteTypeSubalgebraCocone`.
* `AlgebraicGeometry.Space.isFiltered_finiteTypeSubalgebra_of_cocone_objs` reduces the
  directedness assertion of Stacks 082B to nonemptiness and the existence of upper bounds, the
  category of subalgebras being thin.

## Implementation notes

The kernel pair is what makes `AlgebraicGeometry.Space.AlgebraSheaf.forget` preserve
monomorphisms, and it is available even though general pullbacks of algebra sheaves are not.
The obstruction to a general pullback is the universe gap in the definition of an algebra
sheaf: the sections of the structure sheaf lie in `CommRingCat.{u}` and those of the algebra in
`CommRingCat.{m}`, so a structure-algebra map into a limit of `CommRingCat.{m}`-valued sheaves
cannot be produced by that limit's universal property and would need the elementwise
description of its sections.  For the kernel pair of a single `f : A ⟶ C` no such description
is needed: the required map is the *diagonal* `A.right ⟶ A.right ×_{C.right} A.right`, which is
a morphism of sheaves of rings and so may be composed with the structure-algebra map of `A`.
That is `AlgebraicGeometry.Space.AlgebraSheaf.kernelPair`.  An alternative route — building the
fibre product by hand as the subpresheaf of `A × A` cut out by `f`, which does describe the
sections elementwise — was rejected: it needs the sheaf condition for a `CommRingCat`-valued
presheaf proved from scratch, whereas the kernel pair above uses only the limits that
`CategoryTheory.Sheaf.createsLimitsOfShape` already supplies.

`AlgebraicGeometry.Space.FiniteTypeSubalgebra` and
`AlgebraicGeometry.Space.finiteTypeSubalgebraCocone` are the categories and the cocone that
the reduction theorems of `FiniteAlgebraColimits.lean` spell out inline; they are definitionally
the terms appearing there, which is why the two Stacks 082C(1) statements below can be obtained
from them by `exact`.

Neither assertion of Stacks 082B is proved here, so the tag `082B` is **not** placed.  What is
missing is the mathematics of the source, and the two assertions are missing different things.

Directedness needs an image factorization in `AlgebraicGeometry.Space.AlgebraSheaf` — the
quasi-coherent subalgebra generated by two finite type quasi-coherent subalgebras, which is the
image of their coproduct in `A` — and, for nonemptiness, the image of the structure sheaf in
`A`, whose construction is where the universe gap bites again, the structure sheaf not being an
algebra sheaf.  `isFiltered_finiteTypeSubalgebra_of_cocone_objs` reduces the assertion to
exactly those two pieces.  It does not depend on Stacks 07SU.

The colimit assertion does.  Stacks 082B is Lemma 70.9.5, whose proof is omitted and refers to
the proof of Lemma 70.9.2 (Stacks 0829), the same statement for quasi-coherent *modules*; and
the proof of 0829 writes the module as a directed colimit of finitely presented quasi-coherent
modules by Lemma 70.9.1 (Stacks 07V9) and takes the images of the stages.  Stacks 07V9 rests on
absolute Noetherian approximation, Proposition 70.8.1 (Stacks 07SU).  So the colimit assertion
of 082B is blocked on 07SU by the source's own route, through 0829 and 07V9.  The affine case
is not the obstruction: a commutative algebra is the directed supremum of its finite type
subalgebras already in Mathlib, by `Subalgebra.coe_iSup_of_directed` and
`Subalgebra.iSupLift`.

## References

* [Stacks Project, Tag 082B](https://stacks.math.columbia.edu/tag/082B)
* [Stacks Project, Tag 082C](https://stacks.math.columbia.edu/tag/082C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)

namespace AlgebraSheaf

variable {B S hS F hF}

/-! ### The kernel pair of a morphism of algebra sheaves -/

/-- The diagonal of the fibre product of the underlying sheaf of rings of `A` with itself over
`C`, for `f : A ⟶ C`. -/
noncomputable def ringDiagonal {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    A.right ⟶ pullback f.right f.right :=
  pullback.lift (𝟙 A.right) (𝟙 A.right) rfl

/-- The diagonal followed by the first projection is the identity. -/
@[simp]
theorem ringDiagonal_fst {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    ringDiagonal f ≫ pullback.fst f.right f.right = 𝟙 A.right :=
  pullback.lift_fst _ _ _

/-- The diagonal followed by the second projection is the identity. -/
@[simp]
theorem ringDiagonal_snd {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    ringDiagonal f ≫ pullback.snd f.right f.right = 𝟙 A.right :=
  pullback.lift_snd _ _ _

/-- The kernel pair of a morphism of algebra sheaves, as an algebra sheaf: the underlying sheaf
of rings is the fibre product of `A` with itself over `C`, and the structure-algebra map is the
one of `A` followed by the diagonal. -/
noncomputable def kernelPair {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    AlgebraSheaf.{u, m} B S hS F hF where
  right := pullback f.right f.right
  algebraMap U := ((ringDiagonal f).hom.app U).hom.comp (A.algebraMap U)
  algebraMap_natural {U V} g r := by
    have h := ConcreteCategory.congr_hom ((ringDiagonal f).hom.naturality g)
      (A.algebraMap U r)
    simp only [ConcreteCategory.comp_apply] at h
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← A.algebraMap_natural g r]
    exact h.symm

/-- The underlying sheaf of rings of the kernel pair of `f` is the fibre product of `f.right` with
itself. -/
@[simp]
theorem kernelPair_right {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    (kernelPair f).right = pullback f.right f.right :=
  rfl

/-- The first projection of the kernel pair of `f`, as a morphism of algebra sheaves. -/
noncomputable def kernelPairFst {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    kernelPair f ⟶ A where
  right := pullback.fst f.right f.right
  comm U r := by
    have h : (((ringDiagonal f ≫ pullback.fst f.right f.right).hom.app U)).hom
        (A.algebraMap U r) = A.algebraMap U r := by
      rw [ringDiagonal_fst]; rfl
    rw [ObjectProperty.FullSubcategory.comp_hom] at h
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    exact h

/-- The second projection of the kernel pair of `f`, as a morphism of algebra sheaves. -/
noncomputable def kernelPairSnd {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    kernelPair f ⟶ A where
  right := pullback.snd f.right f.right
  comm U r := by
    have h : (((ringDiagonal f ≫ pullback.snd f.right f.right).hom.app U)).hom
        (A.algebraMap U r) = A.algebraMap U r := by
      rw [ringDiagonal_snd]; rfl
    rw [ObjectProperty.FullSubcategory.comp_hom] at h
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    exact h

/-- The underlying morphism of sheaves of rings of `kernelPairFst f` is the first projection. -/
@[simp]
theorem kernelPairFst_right {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    (kernelPairFst f).right = pullback.fst f.right f.right :=
  rfl

/-- The underlying morphism of sheaves of rings of `kernelPairSnd f` is the second projection. -/
@[simp]
theorem kernelPairSnd_right {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    (kernelPairSnd f).right = pullback.snd f.right f.right :=
  rfl

/-- The two projections of the kernel pair of `f` have the same composite with `f`. -/
theorem kernelPairFst_comp {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    kernelPairFst f ≫ f = kernelPairSnd f ≫ f :=
  Hom.ext pullback.condition

/-! ### Monomorphisms of algebra sheaves -/

/-- The forgetful functor `AlgebraicGeometry.Space.AlgebraSheaf.forget` **preserves**
monomorphisms.  Both projections of the kernel pair of `f` are morphisms of algebra sheaves, so
if `f` is a monomorphism of algebra sheaves the two projections already agree in
`Sheaf _ CommRingCat`, which makes `f.right` a monomorphism there. -/
theorem mono_right_of_mono {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) [Mono f] :
    Mono f.right := by
  have key : pullback.fst f.right f.right = pullback.snd f.right f.right :=
    congrArg Hom.right ((cancel_mono f).1 (kernelPairFst_comp f))
  exact ⟨fun g h hgh => (pullback.lift_fst g h hgh).symm.trans
    ((pullback.lift g h hgh ≫= key).trans (pullback.lift_snd g h hgh))⟩

/-- **A monomorphism of algebra sheaves is injective on sections.**  Monomorphisms of sheaves of
rings are sectionwise injective because `CategoryTheory.sheafToPresheaf` creates limits and
limits of presheaves are computed objectwise; `mono_right_of_mono` transports the hypothesis
from algebra sheaves to sheaves of rings. -/
theorem injective_app_of_mono {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) [Mono f]
    (U : (SmallEtale B S hS F)ᵒᵖ) : Function.Injective ((f.right.hom.app U).hom) := by
  have := mono_right_of_mono f
  have : Mono ((sheafToPresheaf (SmallEtale.topology B S hS F) CommRingCat.{m}).map f.right) :=
    inferInstance
  have : Mono (f.right.hom.app U) := (NatTrans.mono_iff_mono_app f.right.hom).1 this U
  have : Mono ((CategoryTheory.forget CommRingCat.{m}).map (f.right.hom.app U)) := inferInstance
  rwa [CategoryTheory.mono_iff_injective] at this

/-- The arrow of a subobject of an algebra sheaf is injective on sections.  This is the
hypothesis `hinj` of the reduction theorems of Stacks 082C(1). -/
theorem injective_subobject_arrow_app {A : AlgebraSheaf.{u, m} B S hS F hF} (C : Subobject A)
    (U : (SmallEtale B S hS F)ᵒᵖ) :
    Function.Injective ((C.arrow.right.hom.app U).hom) :=
  injective_app_of_mono C.arrow U

/-- **The commutative algebra of Stacks 082C(1)**, with the hypothesis on `f` being that it is a
monomorphism rather than that its sections are injective: a finite type subalgebra of an
integral algebra is finite. -/
theorem IsFinite.of_isFiniteType_of_mono {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    [Mono f] (hC : C.IsIntegral) (hA : A.IsFiniteType) : A.IsFinite :=
  IsFinite.of_isFiniteType_of_injective f (fun U => injective_app_of_mono f U) hC hA

end AlgebraSheaf

/-!
### Finite type quasi-coherent subalgebras

The three objects of Stacks 082B: the category of finite type quasi-coherent subalgebras of an
algebra sheaf, its inclusion diagram, and the cocone of the inclusions.  They are the terms that
the reduction theorems of `FiniteAlgebraColimits.lean` write out inline.
-/

/-- The finite type quasi-coherent subalgebras of `A`. -/
abbrev FiniteTypeSubalgebra (A : AlgebraSheaf.{u, m} B S hS F hF) :=
  ObjectProperty.FullSubcategory fun C : Subobject A =>
    (C : AlgebraSheaf.{u, m} B S hS F hF).IsQuasicoherent ∧
      (C : AlgebraSheaf.{u, m} B S hS F hF).IsFiniteType

/-- The inclusion diagram of the finite type quasi-coherent subalgebras of `A`. -/
noncomputable def finiteTypeSubalgebraDiagram (A : AlgebraSheaf.{u, m} B S hS F hF) :
    FiniteTypeSubalgebra B S hS F hF A ⥤ AlgebraSheaf.{u, m} B S hS F hF :=
  ObjectProperty.ι _ ⋙ Subobject.underlying

/-- The cocone of the canonical inclusions of the finite type quasi-coherent subalgebras of `A`
into `A`. -/
noncomputable def finiteTypeSubalgebraCocone (A : AlgebraSheaf.{u, m} B S hS F hF) :
    Cocone (finiteTypeSubalgebraDiagram B S hS F hF A) :=
  Cocone.mk A
    { app := fun C => C.obj.arrow
      naturality := fun _ _ f => Subobject.underlying_arrow f.hom }

/-- Directedness of the finite type quasi-coherent subalgebras of `A` — the first assertion of
Stacks 082B — reduces to nonemptiness and the existence of upper bounds: the category is thin,
so the equalization axiom of a filtered category holds with the identity. -/
theorem isFiltered_finiteTypeSubalgebra_of_cocone_objs (A : AlgebraSheaf.{u, m} B S hS F hF)
    (h₀ : Nonempty (FiniteTypeSubalgebra B S hS F hF A))
    (h : ∀ C D : FiniteTypeSubalgebra B S hS F hF A,
      ∃ (E : FiniteTypeSubalgebra B S hS F hF A) (_ : C ⟶ E) (_ : D ⟶ E), True) :
    IsFiltered (FiniteTypeSubalgebra B S hS F hF A) :=
  haveI := isThin_fullSubcategory_subobject
    (B := B) (S := S) (hS := hS) (F := F) (hF := hF) (A := A) _
  { cocone_objs := h
    cocone_maps := fun _ Y _ _ => ⟨Y, 𝟙 Y, rfl⟩
    nonempty := h₀ }

/-! ### Stacks 082C(1) from Stacks 082B

The four statements of `FiniteAlgebraColimits.lean` with the hypothesis `hinj` discharged by
`AlgebraicGeometry.Space.AlgebraSheaf.injective_subobject_arrow_app`.  The last two are Stacks
082C(1) deduced from Stacks 082B, with no hypothesis beyond integrality of `A` and the two
assertions of Stacks 082B themselves.
-/

/-- For an integral algebra sheaf, a subalgebra is finite exactly when it is of finite type. -/
theorem isFinite_subobject_iff_isFiniteType' (A : AlgebraSheaf.{u, m} B S hS F hF)
    (hA : A.IsIntegral) (C : Subobject A) :
    (C : AlgebraSheaf.{u, m} B S hS F hF).IsFinite ↔
      (C : AlgebraSheaf.{u, m} B S hS F hF).IsFiniteType :=
  isFinite_subobject_iff_isFiniteType B S hS F hF A hA
    (fun C U => AlgebraSheaf.injective_subobject_arrow_app C U) C

/-- For an integral algebra sheaf, being a finite quasi-coherent subalgebra and being a finite
type quasi-coherent subalgebra are the same property of a subobject. -/
theorem isQuasicoherentAndIsFinite_eq_isQuasicoherentAndIsFiniteType'
    (A : AlgebraSheaf.{u, m} B S hS F hF) (hA : A.IsIntegral) :
    (fun C : Subobject A => (C : AlgebraSheaf.{u, m} B S hS F hF).IsQuasicoherent ∧
        (C : AlgebraSheaf.{u, m} B S hS F hF).IsFinite) =
      fun C : Subobject A => (C : AlgebraSheaf.{u, m} B S hS F hF).IsQuasicoherent ∧
        (C : AlgebraSheaf.{u, m} B S hS F hF).IsFiniteType :=
  isQuasicoherentAndIsFinite_eq_isQuasicoherentAndIsFiniteType B S hS F hF A hA
    fun C U => AlgebraSheaf.injective_subobject_arrow_app C U

/-- **Stacks 082C(1), directedness, from Stacks 082B.**  The finite quasi-coherent subalgebras
of an integral algebra sheaf are directed as soon as its finite type quasi-coherent subalgebras
are. -/
theorem isFiltered_finiteSubalgebra_of_isFiltered_finiteTypeSubalgebra'
    (A : AlgebraSheaf.{u, m} B S hS F hF) (hA : A.IsIntegral)
    (h : IsFiltered (FiniteTypeSubalgebra B S hS F hF A)) :
    IsFiltered (FiniteSubalgebra B S hS F hF A) :=
  isFiltered_finiteSubalgebra_of_isFiltered_finiteTypeSubalgebra B S hS F hF A hA
    (fun C U => AlgebraSheaf.injective_subobject_arrow_app C U) h

/-- **Stacks 082C(1), the colimit, from Stacks 082B.**  An integral algebra sheaf is the colimit
of its finite quasi-coherent subalgebras as soon as it is the colimit of its finite type
quasi-coherent subalgebras. -/
theorem isColimit_finiteSubalgebraCocone_of_isColimit_finiteTypeSubalgebraCocone'
    (A : AlgebraSheaf.{u, m} B S hS F hF) (hA : A.IsIntegral)
    (h : Nonempty (IsColimit (finiteTypeSubalgebraCocone B S hS F hF A))) :
    Nonempty (IsColimit (finiteSubalgebraCocone B S hS F hF A)) :=
  isColimit_finiteSubalgebraCocone_of_isColimit_finiteTypeSubalgebraCocone B S hS F hF A hA
    (fun C U => AlgebraSheaf.injective_subobject_arrow_app C U) h

end AlgebraicGeometry.Space

end
