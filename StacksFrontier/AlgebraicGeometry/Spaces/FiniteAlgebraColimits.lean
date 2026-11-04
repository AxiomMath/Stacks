module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Algebras on an algebraic space and their finite subalgebras

Sheaves of commutative algebras over the structure sheaf of the small étale site of an
algebraic space `F`, and the finiteness properties of such an algebra that are tested on the
affine étale charts of `F`.  This is the vocabulary in which Stacks 082A, 082B, 082C and 086Z
are stated, together with the one step of 082C(1) that is pure commutative algebra: a finite
type quasi-coherent subalgebra of an integral quasi-coherent algebra is finite.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf` is a sheaf of commutative rings on the small étale
  site of `F` together with a sectionwise algebra structure over the structure sheaf.  Its
  category, the forgetful functor to sheaves of rings, and the underlying sheaf of modules
  are `AlgebraicGeometry.Space.AlgebraSheaf.Hom`,
  `AlgebraicGeometry.Space.AlgebraSheaf.forget` and
  `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule`.
* `AlgebraicGeometry.Space.AlgebraSheaf.IsQuasicoherent` is quasi-coherence of the underlying
  module, and `AlgebraicGeometry.Space.AlgebraSheaf.IsFinite`, `.IsIntegral`, `.IsFiniteType`
  and `.IsFinitePresentation` are the properties of the sectionwise algebra maps on the affine
  étale charts.
* `AlgebraicGeometry.Space.FiniteSubalgebra` is the category of finite quasi-coherent
  subalgebras of an algebra, `AlgebraicGeometry.Space.finiteSubalgebraDiagram` its inclusion
  diagram and `AlgebraicGeometry.Space.finiteSubalgebraCocone` the canonical cocone of
  inclusions with vertex the ambient algebra.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegral.of_injective` is the descent of
  integrality to a subalgebra: if the sections of `f : A ⟶ C` are injective and `C` is
  integral, then `A` is integral.
* `AlgebraicGeometry.Space.AlgebraSheaf.IsFinite.of_isFiniteType_of_injective` is the step of
  Stacks 082C(1) that takes place in commutative algebra: a finite type subalgebra of an
  integral algebra is finite.  Both the hypothesis and the conclusion are tested on affine
  étale charts, where the content is Stacks 02JJ, i.e. Mathlib's
  `RingHom.finite_iff_isIntegral_and_finiteType`.
* `AlgebraicGeometry.Space.isQuasicoherentAndIsFinite_eq_isQuasicoherentAndIsFiniteType`
  identifies, for an integral algebra, the finite quasi-coherent subalgebras with the finite
  type quasi-coherent subalgebras.
* In namespace `AlgebraicGeometry.Space`:
  `isFiltered_finiteSubalgebra_of_isFiltered_finiteTypeSubalgebra` and
  `isColimit_finiteSubalgebraCocone_of_isColimit_finiteTypeSubalgebraCocone` transport the two
  assertions of Stacks 082B along that identification, which reduces Stacks 082C(1) to Stacks
  082B.
* `AlgebraicGeometry.Space.isFiltered_finiteSubalgebra_of_cocone_objs` reduces filteredness of
  the finite subalgebras to the existence of upper bounds, the category being thin.

## Implementation notes

The algebra structure is stored as a *sectionwise* family of ring homomorphisms
`𝒪_F(U) →+* A(U)` rather than as a morphism of sheaves of rings, because the sections of the
structure sheaf live in the universe `u` of the schemes while the sections of the algebra are
allowed to live in an independent universe `m`.  In the single-universe case `m = u` the two
descriptions agree, which is `AlgebraicGeometry.Space.AlgebraSheaf.hom` and
`AlgebraicGeometry.Space.AlgebraSheaf.ofHom`.

Finiteness, integrality, finite type and finite presentation are *not* phrased as properties
of the underlying module or of a morphism of algebraic spaces: they are the corresponding
properties of the ring maps `𝒪_F(U) →+* A(U)` for `U` an étale chart whose underlying scheme
is affine.  This is how Stacks 082A/082B/082C/086Z test them, and it is what makes the
commutative algebra of Stacks 02JJ directly applicable.

`AlgebraicGeometry.Space.AlgebraSheaf.IsIntegral.of_injective` and
`AlgebraicGeometry.Space.AlgebraSheaf.IsFinite.of_isFiniteType_of_injective` take injectivity
of the sections of `f` as a hypothesis rather than `Mono f`: the forgetful functor to sheaves
of rings is faithful, so it *reflects* monomorphisms, but preserving them would need pullbacks
in `AlgebraicGeometry.Space.AlgebraSheaf`, which are not constructed here.  See the module
documentation of the subalgebra section for what a subobject-level form would require.

## References

* [Stacks Project, Tag 02JJ](https://stacks.math.columbia.edu/tag/02JJ)
* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 082B](https://stacks.math.columbia.edu/tag/082B)
* [Stacks Project, Tag 082C](https://stacks.math.columbia.edu/tag/082C)
* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)

/-- A sheaf of commutative algebras over the structure sheaf of the small étale site of the
algebraic space `F`.  The ring of sections is allowed to live in a universe `m` independent of
the universe `u` of the schemes, which is why the algebra structure is recorded as a
sectionwise family of ring homomorphisms. -/
structure AlgebraSheaf where
  /-- The underlying sheaf of commutative rings. -/
  right : Sheaf (SmallEtale.topology B S hS F) CommRingCat.{m}
  /-- The structure-algebra map on each étale chart. -/
  algebraMap (U : (SmallEtale B S hS F)ᵒᵖ) :
    (structureSheaf B S hS F hF).obj.obj U →+* right.obj.obj U
  /-- The structure-algebra maps commute with restriction. -/
  algebraMap_natural {U V : (SmallEtale B S hS F)ᵒᵖ} (f : U ⟶ V)
      (r : (structureSheaf B S hS F hF).obj.obj U) :
    right.obj.map f (algebraMap U r) =
      algebraMap V ((structureSheaf B S hS F hF).obj.map f r)

namespace AlgebraSheaf

variable {B S hS F hF}

/-- A morphism of algebra sheaves is a morphism of the underlying sheaves of rings which is
compatible with the structure-algebra maps. -/
@[ext]
structure Hom (A C : AlgebraSheaf.{u, m} B S hS F hF) where
  /-- The underlying morphism of sheaves of rings. -/
  right : A.right ⟶ C.right
  /-- Compatibility with the structure-algebra maps. -/
  comm (U : (SmallEtale B S hS F)ᵒᵖ)
      (r : (structureSheaf B S hS F hF).obj.obj U) :
    right.hom.app U (A.algebraMap U r) = C.algebraMap U r

/-- Algebra sheaves form a category, with morphisms `AlgebraSheaf.Hom`. -/
instance : Category (AlgebraSheaf.{u, m} B S hS F hF) where
  Hom := Hom
  id A := ⟨𝟙 A.right, fun _ _ => rfl⟩
  comp f g := ⟨f.right ≫ g.right, fun U r => by
    change g.right.hom.app U (f.right.hom.app U _) = _
    rw [f.comm, g.comm]⟩

/-- The underlying morphism of sheaves of rings of the identity is the identity. -/
@[simp]
theorem id_right (A : AlgebraSheaf.{u, m} B S hS F hF) :
    Hom.right (𝟙 A) = 𝟙 A.right :=
  rfl

/-- The underlying morphism of sheaves of rings of a composite is the composite. -/
@[simp]
theorem comp_right {A C D : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) (g : C ⟶ D) :
    (f ≫ g).right = f.right ≫ g.right :=
  rfl

/-- Forget the algebra structure, keeping the underlying sheaf of rings. -/
def forget : AlgebraSheaf.{u, m} B S hS F hF ⥤
    Sheaf (SmallEtale.topology B S hS F) CommRingCat.{m} where
  obj A := A.right
  map f := f.right

/-- The forgetful functor from algebra sheaves to sheaves of rings is faithful. -/
instance : (forget (B := B) (S := S) (hS := hS) (F := F) (hF := hF)).Faithful where
  map_injective h := Hom.ext h

/-- The sheaf of rings underlying an algebra sheaf. -/
abbrev ringSheaf (A : AlgebraSheaf.{u, m} B S hS F hF) := A.right

/-- In a single universe the algebra structure of an algebra sheaf is a morphism of sheaves of
rings out of the structure sheaf. -/
def hom (A : AlgebraSheaf.{u, u} B S hS F hF) :
    structureSheaf B S hS F hF ⟶ A.right where
  hom :=
    { app := fun U => CommRingCat.ofHom (A.algebraMap U)
      naturality := fun _ _ f => by
        ext r
        exact (A.algebraMap_natural f r).symm }

/-- An algebra sheaf built from a morphism of sheaves of rings out of the structure sheaf. -/
def ofHom {R : Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u}}
    (f : structureSheaf B S hS F hF ⟶ R) :
    AlgebraSheaf.{u, u} B S hS F hF where
  right := R
  algebraMap U := (f.hom.app U).hom
  algebraMap_natural g r := (ConcreteCategory.congr_hom (f.hom.naturality g) r).symm

/-- The sheaf of `𝒪_F`-modules underlying an algebra sheaf, formed on the algebra's own
sections: the module structure is the one induced by the structure-algebra maps, and no
separate module sheaf is chosen. -/
noncomputable def underlyingModule (A : AlgebraSheaf.{u, m} B S hS F hF) :
    Modules.{u, m} B S hS F hF := by
  let R := (structureSheaf B S hS F hF).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}
  let M := A.right.obj ⋙ forget₂ CommRingCat.{m} RingCat.{m} ⋙
    forget₂ RingCat.{m} AddCommGrpCat.{m}
  letI : ∀ U, Module (R.obj U) (M.obj U) :=
    fun U => Module.compHom (A.right.obj.obj U) (A.algebraMap U)
  refine
    { val := PresheafOfModules.ofPresheaf (R := R) M ?_
      isSheaf := (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf A.right))).isSheaf }
  intro U V f r x
  change A.right.obj.obj U at x
  change A.right.obj.map f (A.algebraMap U r * x) =
    A.algebraMap V ((structureSheaf B S hS F hF).obj.map f r) * A.right.obj.map f x
  rw [map_mul, A.algebraMap_natural]

/-- Quasi-coherence of an algebra sheaf: quasi-coherence of its underlying sheaf of modules on
the small étale ringed site. -/
abbrev IsQuasicoherent (A : AlgebraSheaf.{u, m} B S hS F hF) : Prop :=
  SheafOfModules.IsQuasicoherentOnSite.{u + 1, u, u, m} (underlyingModule A)

/-- An algebra sheaf is *finite* when its structure-algebra map is finite on every affine
étale chart. -/
def IsFinite (A : AlgebraSheaf.{u, m} B S hS F hF) : Prop :=
  ∀ U : SmallEtale B S hS F,
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
      RingHom.Finite (A.algebraMap (.op U))

/-- An algebra sheaf is *integral* when its structure-algebra map is integral on every affine
étale chart. -/
def IsIntegral (A : AlgebraSheaf.{u, m} B S hS F hF) : Prop :=
  ∀ U : SmallEtale B S hS F,
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
      RingHom.IsIntegral (A.algebraMap (.op U))

/-- An algebra sheaf is *of finite type* when its structure-algebra map is of finite type on
every affine étale chart. -/
def IsFiniteType (A : AlgebraSheaf.{u, m} B S hS F hF) : Prop :=
  ∀ U : SmallEtale B S hS F,
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
      RingHom.FiniteType (A.algebraMap (.op U))

/-- An algebra sheaf is *of finite presentation* when its structure-algebra map is of finite
presentation on every affine étale chart. -/
def IsFinitePresentation (A : AlgebraSheaf.{u, m} B S hS F hF) : Prop :=
  ∀ U : SmallEtale B S hS F,
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
      RingHom.FinitePresentation (A.algebraMap (.op U))

/-- An algebra sheaf is finite if and only if it is integral and of finite type. -/
theorem isFinite_iff_isIntegral_and_isFiniteType (A : AlgebraSheaf.{u, m} B S hS F hF) :
    A.IsFinite ↔ A.IsIntegral ∧ A.IsFiniteType := by
  refine ⟨fun h => ⟨fun U hU => ?_, fun U hU => ?_⟩, fun h U hU => ?_⟩
  · exact (RingHom.finite_iff_isIntegral_and_finiteType.1 (h U hU)).1
  · exact (RingHom.finite_iff_isIntegral_and_finiteType.1 (h U hU)).2
  · exact RingHom.finite_iff_isIntegral_and_finiteType.2 ⟨h.1 U hU, h.2 U hU⟩

/-- A finite algebra sheaf is integral. -/
theorem IsFinite.isIntegral {A : AlgebraSheaf.{u, m} B S hS F hF} (h : A.IsFinite) :
    A.IsIntegral :=
  ((isFinite_iff_isIntegral_and_isFiniteType A).1 h).1

/-- A finite algebra sheaf is of finite type. -/
theorem IsFinite.isFiniteType {A : AlgebraSheaf.{u, m} B S hS F hF} (h : A.IsFinite) :
    A.IsFiniteType :=
  ((isFinite_iff_isIntegral_and_isFiniteType A).1 h).2

/-- An algebra sheaf of finite presentation is of finite type. -/
theorem IsFinitePresentation.isFiniteType {A : AlgebraSheaf.{u, m} B S hS F hF}
    (h : A.IsFinitePresentation) : A.IsFiniteType :=
  fun U hU => RingHom.FiniteType.of_finitePresentation (h U hU)

/-- The sections of a morphism of algebra sheaves carry the structure-algebra map of the
source to the structure-algebra map of the target. -/
theorem comp_algebraMap {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    (U : (SmallEtale B S hS F)ᵒᵖ) :
    ((f.right.hom.app U).hom).comp (A.algebraMap U) = C.algebraMap U :=
  RingHom.ext fun r => f.comm U r

/-- Integrality descends to a subalgebra: if the sections of `f : A ⟶ C` are injective and
`C` is integral, then so is `A`.

On an affine étale chart this is `RingHom.IsIntegral.tower_bot`: the structure-algebra map of
`A` is the bottom of the tower `𝒪_F(U) → A(U) → C(U)` whose composite is integral and whose
top map is injective. -/
theorem IsIntegral.of_injective {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    (hf : ∀ U : (SmallEtale B S hS F)ᵒᵖ, Function.Injective ((f.right.hom.app U).hom))
    (hC : C.IsIntegral) : A.IsIntegral := by
  intro U hU
  refine RingHom.IsIntegral.tower_bot (A.algebraMap (.op U)) ((f.right.hom.app (.op U)).hom)
    (hf (.op U)) ?_
  rw [comp_algebraMap f (.op U)]
  exact hC U hU

/-- **The commutative algebra of Stacks 082C(1).** A finite type subalgebra of an integral
algebra is finite.

The hypothesis is that the sections of `f : A ⟶ C` are injective; on an affine étale chart the
content is Stacks 02JJ, that a finite type integral ring map is finite. -/
theorem IsFinite.of_isFiniteType_of_injective {A C : AlgebraSheaf.{u, m} B S hS F hF}
    (f : A ⟶ C)
    (hf : ∀ U : (SmallEtale B S hS F)ᵒᵖ, Function.Injective ((f.right.hom.app U).hom))
    (hC : C.IsIntegral) (hA : A.IsFiniteType) : A.IsFinite :=
  (isFinite_iff_isIntegral_and_isFiniteType A).2 ⟨IsIntegral.of_injective f hf hC, hA⟩

end AlgebraSheaf

/-!
### Finite quasi-coherent subalgebras

A subalgebra of an algebra sheaf `A` is a subobject of `A` in
`AlgebraicGeometry.Space.AlgebraSheaf`, and the diagram of Stacks 082C(1) is the inclusion
diagram of those subobjects that are quasi-coherent and finite.

The statements below reduce Stacks 082C(1) to Stacks 082B — the same assertions for the
*finite type* quasi-coherent subalgebras — using that an integral algebra has no finite type
subalgebra that is not finite.  They carry the hypothesis that the inclusion of a subobject is
sectionwise injective, which is not available: it is the assertion that the forgetful functor
`AlgebraicGeometry.Space.AlgebraSheaf.forget` *preserves* monomorphisms, and since that
functor is faithful it only *reflects* them.  Proving it needs pullbacks in
`AlgebraicGeometry.Space.AlgebraSheaf`, and the obstruction to constructing them is the
universe gap in the definition of an algebra sheaf: the sections of the structure sheaf lie in
`CommRingCat.{u}` and those of the algebra in `CommRingCat.{m}`, so the structure-algebra map
of a pullback cannot be produced from the universal property of a limit of
`CommRingCat.{m}`-valued sheaves and needs the elementwise description of the sections of that
limit.
-/

/-- The finite quasi-coherent subalgebras of `A`. -/
abbrev FiniteSubalgebra (A : AlgebraSheaf.{u, m} B S hS F hF) :=
  ObjectProperty.FullSubcategory fun C : Subobject A =>
    (C : AlgebraSheaf.{u, m} B S hS F hF).IsQuasicoherent ∧
      (C : AlgebraSheaf.{u, m} B S hS F hF).IsFinite

/-- The inclusion diagram of the finite quasi-coherent subalgebras of `A`. -/
noncomputable def finiteSubalgebraDiagram (A : AlgebraSheaf.{u, m} B S hS F hF) :
    FiniteSubalgebra B S hS F hF A ⥤ AlgebraSheaf.{u, m} B S hS F hF :=
  ObjectProperty.ι _ ⋙ Subobject.underlying

/-- The cocone of the canonical inclusions of the finite quasi-coherent subalgebras of `A`
into `A`. -/
noncomputable def finiteSubalgebraCocone (A : AlgebraSheaf.{u, m} B S hS F hF) :
    Cocone (finiteSubalgebraDiagram B S hS F hF A) :=
  Cocone.mk A
    { app := fun C => C.obj.arrow
      naturality := fun _ _ f => Subobject.underlying_arrow f.hom }

/-- Any full subcategory of the subobjects of an object is thin: between two subobjects there
is at most one morphism. -/
theorem isThin_fullSubcategory_subobject {A : AlgebraSheaf.{u, m} B S hS F hF}
    (P : ObjectProperty (Subobject A)) : Quiver.IsThin P.FullSubcategory :=
  fun _ _ => ⟨fun _ _ => ObjectProperty.hom_ext _ (Subsingleton.elim _ _)⟩

/-- Filteredness of the finite quasi-coherent subalgebras of `A` reduces to nonemptiness and
the existence of upper bounds: the category is thin, so the equalization axiom of a filtered
category holds with the identity. -/
theorem isFiltered_finiteSubalgebra_of_cocone_objs (A : AlgebraSheaf.{u, m} B S hS F hF)
    (h₀ : Nonempty (FiniteSubalgebra B S hS F hF A))
    (h : ∀ C D : FiniteSubalgebra B S hS F hF A,
      ∃ (E : FiniteSubalgebra B S hS F hF A) (_ : C ⟶ E) (_ : D ⟶ E), True) :
    IsFiltered (FiniteSubalgebra B S hS F hF A) :=
  haveI := isThin_fullSubcategory_subobject
    (B := B) (S := S) (hS := hS) (F := F) (hF := hF) (A := A) _
  { cocone_objs := h
    cocone_maps := fun _ Y _ _ => ⟨Y, 𝟙 Y, rfl⟩
    nonempty := h₀ }

/-- For an integral algebra sheaf, a subalgebra is finite exactly when it is of finite type.

The forward direction is formal; the converse is the commutative algebra of Stacks 02JJ,
applied on the affine étale charts of `F`. -/
theorem isFinite_subobject_iff_isFiniteType (A : AlgebraSheaf.{u, m} B S hS F hF)
    (hA : A.IsIntegral)
    (hinj : ∀ (C : Subobject A) (U : (SmallEtale B S hS F)ᵒᵖ),
      Function.Injective ((C.arrow.right.hom.app U).hom))
    (C : Subobject A) :
    (C : AlgebraSheaf.{u, m} B S hS F hF).IsFinite ↔
      (C : AlgebraSheaf.{u, m} B S hS F hF).IsFiniteType :=
  ⟨AlgebraSheaf.IsFinite.isFiniteType,
    AlgebraSheaf.IsFinite.of_isFiniteType_of_injective C.arrow (hinj C) hA⟩

/-- For an integral algebra sheaf, being a finite quasi-coherent subalgebra and being a finite
type quasi-coherent subalgebra are the same property of a subobject.  This is the identity
that turns Stacks 082B into Stacks 082C(1). -/
theorem isQuasicoherentAndIsFinite_eq_isQuasicoherentAndIsFiniteType
    (A : AlgebraSheaf.{u, m} B S hS F hF) (hA : A.IsIntegral)
    (hinj : ∀ (C : Subobject A) (U : (SmallEtale B S hS F)ᵒᵖ),
      Function.Injective ((C.arrow.right.hom.app U).hom)) :
    (fun C : Subobject A => (C : AlgebraSheaf.{u, m} B S hS F hF).IsQuasicoherent ∧
        (C : AlgebraSheaf.{u, m} B S hS F hF).IsFinite) =
      fun C : Subobject A => (C : AlgebraSheaf.{u, m} B S hS F hF).IsQuasicoherent ∧
        (C : AlgebraSheaf.{u, m} B S hS F hF).IsFiniteType :=
  funext fun C => propext (and_congr_right fun _ =>
    isFinite_subobject_iff_isFiniteType B S hS F hF A hA hinj C)

/-- **Stacks 082C(1), reduced to Stacks 082B.** Filteredness of the finite quasi-coherent
subalgebras of an integral algebra sheaf follows from filteredness of its finite type
quasi-coherent subalgebras.

The hypothesis `h` is the directedness assertion of Stacks 082B. -/
theorem isFiltered_finiteSubalgebra_of_isFiltered_finiteTypeSubalgebra
    (A : AlgebraSheaf.{u, m} B S hS F hF) (hA : A.IsIntegral)
    (hinj : ∀ (C : Subobject A) (U : (SmallEtale B S hS F)ᵒᵖ),
      Function.Injective ((C.arrow.right.hom.app U).hom))
    (h : IsFiltered (ObjectProperty.FullSubcategory
      fun C : Subobject A => (C : AlgebraSheaf.{u, m} B S hS F hF).IsQuasicoherent ∧
        (C : AlgebraSheaf.{u, m} B S hS F hF).IsFiniteType)) :
    IsFiltered (FiniteSubalgebra B S hS F hF A) := by
  rwa [← isQuasicoherentAndIsFinite_eq_isQuasicoherentAndIsFiniteType B S hS F hF A hA hinj] at h

/-- **Stacks 082C(1), reduced to Stacks 082B.** An integral algebra sheaf is the colimit of its
finite quasi-coherent subalgebras as soon as it is the colimit of its finite type
quasi-coherent subalgebras.

The hypothesis `h` is the colimit assertion of Stacks 082B, with its diagram and cocone
written out: they are `AlgebraicGeometry.Space.finiteSubalgebraDiagram` and
`AlgebraicGeometry.Space.finiteSubalgebraCocone` with finiteness replaced by finite type. -/
theorem isColimit_finiteSubalgebraCocone_of_isColimit_finiteTypeSubalgebraCocone
    (A : AlgebraSheaf.{u, m} B S hS F hF) (hA : A.IsIntegral)
    (hinj : ∀ (C : Subobject A) (U : (SmallEtale B S hS F)ᵒᵖ),
      Function.Injective ((C.arrow.right.hom.app U).hom))
    (h : Nonempty (IsColimit (Cocone.mk (F := ObjectProperty.ι
        (fun C : Subobject A => (C : AlgebraSheaf.{u, m} B S hS F hF).IsQuasicoherent ∧
          (C : AlgebraSheaf.{u, m} B S hS F hF).IsFiniteType) ⋙ Subobject.underlying) A
      { app := fun C => C.obj.arrow
        naturality := fun _ _ f => Subobject.underlying_arrow f.hom }))) :
    Nonempty (IsColimit (finiteSubalgebraCocone B S hS F hF A)) := by
  rwa [← isQuasicoherentAndIsFinite_eq_isQuasicoherentAndIsFiniteType B S hS F hF A hA hinj] at h

end AlgebraicGeometry.Space

end
