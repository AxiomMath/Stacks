module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.RingTheory.Smooth.FieldExtensionCompleteIntersectionColimit

/-!
# A separable field extension as a limit of smooth schemes

Let `L/K` be a separable extension of fields. By [Stacks, Tag 07BV] the smooth `K`-subalgebras of
`L` form a directed family whose union is `L`, so `L` is the filtered colimit of the smooth
`K`-algebras `A ⊆ L`. Taking spectra, `Spec L` is the directed limit of the affine schemes
`Spec A`, which are smooth over `Spec K` and have affine transition morphisms. For a scheme `S`
over `K`, base change along `S ⟶ Spec K` keeps all of this: `Spec L ×_K S` is the directed limit
of the schemes `Spec A ×_K S`, which are smooth over `S` and have affine transition morphisms.

## Main definitions

* `Stacks.EtaleCohomology.FieldExtensionLimit.SmoothSubalgebra` — the smooth `K`-subalgebras of
  `L`, ordered by inclusion. Directed and nonempty when `L/K` is separable.
* `Stacks.EtaleCohomology.FieldExtensionLimit.ringDiagram`,
  `Stacks.EtaleCohomology.FieldExtensionLimit.ringCocone` — the inclusions `A ⊆ L`, as a cocone
  in `CommRingCat`.
* `Stacks.EtaleCohomology.FieldExtensionLimit.specOver`,
  `Stacks.EtaleCohomology.FieldExtensionLimit.specOverCone` — the spectra `Spec A` over
  `Spec K`, with the cone from `Spec L`.
* `Stacks.EtaleCohomology.FieldExtensionLimit.baseChangeDiagram`,
  `Stacks.EtaleCohomology.FieldExtensionLimit.baseChangeDiagramToBase`,
  `Stacks.EtaleCohomology.FieldExtensionLimit.baseChangeCone` — the system `Spec A ×_K S` with its
  structure morphisms to `S`, and the cone from `Spec L ×_K S`.

## Main results

* `Stacks.EtaleCohomology.FieldExtensionLimit.isColimitRingCocone` — `L` is the colimit of its
  smooth `K`-subalgebras.
* `Stacks.EtaleCohomology.FieldExtensionLimit.isLimitSpecOverCone` — `Spec L` is the limit of
  the `Spec A` over `Spec K`.
* `Stacks.EtaleCohomology.FieldExtensionLimit.isLimitBaseChangeCone` — `Spec L ×_K S` is the
  limit of the `Spec A ×_K S`.
* `Stacks.EtaleCohomology.FieldExtensionLimit.smooth_baseChangeDiagramToBase_app` and
  `Stacks.EtaleCohomology.FieldExtensionLimit.isAffineHom_baseChangeDiagram_map` — the levels are
  smooth over `S` and the transition morphisms are affine.

## Implementation notes

The colimit in `CommRingCat` is checked on underlying types, where a directed union of subsets
is a filtered colimit. The forgetful functor reflects filtered colimits. `Spec` is a right
adjoint, so it turns the colimit into a limit. The forgetful functor from `Over (Spec K)` creates
connected limits, so the limit lifts to `Over (Spec K)`. There, base change `Over.pullback` is a
right adjoint, and the forgetful functor from `Over S` preserves connected limits.

## References

* [Stacks Project, Tag 07BV](https://stacks.math.columbia.edu/tag/07BV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.FieldExtensionLimit

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The smooth `K`-subalgebras of `L`, ordered by inclusion. -/
abbrev SmoothSubalgebra : Type u := {A : Subalgebra K L // Algebra.Smooth K A}

/-- For a separable extension the smooth `K`-subalgebras of `L` form a directed family, by
[Stacks, Tag 07BV]. -/
instance [Algebra.IsSeparableExtension K L] : IsDirected (SmoothSubalgebra K L) (· ≤ ·) where
  directed A B := by
    obtain ⟨C, hC, hAC, hBC⟩ :=
      (Subalgebra.directedOn_smooth_and_exists_mem K L).1 A.1 A.2 B.1 B.2
    exact ⟨⟨C, hC⟩, hAC, hBC⟩

/-- For a separable extension there is a smooth `K`-subalgebra of `L`, by [Stacks, Tag 07BV]. -/
instance [Algebra.IsSeparableExtension K L] : Nonempty (SmoothSubalgebra K L) :=
  let ⟨A, hA, _⟩ := (Subalgebra.directedOn_smooth_and_exists_mem K L).2 0
  ⟨⟨A, hA⟩⟩

/-- The diagram of smooth `K`-subalgebras of `L` and their inclusions, in `CommRingCat`. -/
def ringDiagram : SmoothSubalgebra K L ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of A.1
  map h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h)).toRingHom

/-- The structure map `K ⟶ A` of a smooth `K`-subalgebra. -/
def fromBase (A : SmoothSubalgebra K L) : CommRingCat.of K ⟶ (ringDiagram K L).obj A :=
  CommRingCat.ofHom (algebraMap K A.1)

/-- The inclusion `A ⟶ L` of a smooth `K`-subalgebra. -/
def toTop (A : SmoothSubalgebra K L) : (ringDiagram K L).obj A ⟶ CommRingCat.of L :=
  CommRingCat.ofHom A.1.val.toRingHom

/-- The structure maps `K ⟶ A` commute with the inclusions of smooth `K`-subalgebras. -/
@[reassoc]
theorem fromBase_comp_map {A B : SmoothSubalgebra K L} (h : A ⟶ B) :
    fromBase K L A ≫ (ringDiagram K L).map h = fromBase K L B :=
  rfl

/-- The inclusions `A ⟶ L` commute with the inclusions of smooth `K`-subalgebras. -/
@[reassoc]
theorem map_comp_toTop {A B : SmoothSubalgebra K L} (h : A ⟶ B) :
    (ringDiagram K L).map h ≫ toTop K L B = toTop K L A :=
  rfl

/-- The composite `K ⟶ A ⟶ L` is the structure map `K ⟶ L`. -/
theorem fromBase_comp_toTop (A : SmoothSubalgebra K L) :
    fromBase K L A ≫ toTop K L A = CommRingCat.ofHom (algebraMap K L) :=
  rfl

/-- The inclusions of the smooth `K`-subalgebras into `L`, as a cocone. -/
def ringCocone : Cocone (ringDiagram K L) where
  pt := CommRingCat.of L
  ι :=
    { app := toTop K L
      naturality _ _ h := (map_comp_toTop K L h).trans (Category.comp_id _).symm }

/-- **`L` is the colimit of its smooth `K`-subalgebras**, for `L/K` separable: their union is
`L` by [Stacks, Tag 07BV], and a directed union is a filtered colimit. -/
def isColimitRingCocone [Algebra.IsSeparableExtension K L] : IsColimit (ringCocone K L) :=
  have : ReflectsColimitsOfShape (SmoothSubalgebra K L) (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  isColimitOfReflects (forget CommRingCat)
    (Types.FilteredColimit.isColimitOf' _ ((forget CommRingCat).mapCocone (ringCocone K L))
      (fun x ↦ by
        obtain ⟨A, hA, hx⟩ := (Subalgebra.directedOn_smooth_and_exists_mem K L).2 x
        exact ⟨⟨A, hA⟩, ⟨x, hx⟩, rfl⟩)
      (fun A x y h ↦ by
        have hxy : x = y := Subtype.ext h
        exact ⟨A, 𝟙 A, by rw [hxy]⟩))

/-- The spectra of the smooth `K`-subalgebras of `L`, over `Spec K`. -/
def specOver : (SmoothSubalgebra K L)ᵒᵖ ⥤ Over (Spec (.of K)) :=
  ((ringDiagram K L).op ⋙ Scheme.Spec).toOver (Spec (.of K))
    (fun A ↦ Spec.map (fromBase K L A.unop))
    (fun h ↦ (Spec.map_comp _ _).symm.trans (congrArg Spec.map (fromBase_comp_map K L h.unop)))

/-- The cone from `Spec L` over the spectra of the smooth `K`-subalgebras of `L`. -/
def specOverCone : Cone (specOver K L) where
  pt := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  π :=
    { app A := Over.homMk (Spec.map (toTop K L A.unop))
        ((Spec.map_comp _ _).symm.trans (congrArg Spec.map (fromBase_comp_toTop K L A.unop)))
      naturality _ _ h := by
        ext : 1
        exact (Category.id_comp _).trans ((congrArg Spec.map (map_comp_toTop K L h.unop)).symm.trans
          (Spec.map_comp _ _)) }

/-- **`Spec L` is the limit of the `Spec A`**, over `Spec K`, for `L/K` separable and `A` running
over the smooth `K`-subalgebras of `L`. -/
def isLimitSpecOverCone [Algebra.IsSeparableExtension K L] : IsLimit (specOverCone K L) :=
  have : IsConnected (SmoothSubalgebra K L)ᵒᵖ := IsCofiltered.isConnected _
  isLimitOfReflects (Over.forget _) (isLimitOfPreserves Scheme.Spec (isColimitRingCocone K L).op)

variable {K L} {S : Scheme.{u}} (sS : S ⟶ Spec (.of K))

/-- The system of schemes `Spec A ×_K S`, for `A` running over the smooth `K`-subalgebras of
`L`. -/
def baseChangeDiagram : (SmoothSubalgebra K L)ᵒᵖ ⥤ Scheme.{u} :=
  specOver K L ⋙ Over.pullback sS ⋙ Over.forget S

/-- The structure morphisms `Spec A ×_K S ⟶ S`. -/
def baseChangeDiagramToBase :
    baseChangeDiagram (L := L) sS ⟶ (Functor.const (SmoothSubalgebra K L)ᵒᵖ).obj S where
  app A := ((Over.pullback sS).obj ((specOver K L).obj A)).hom
  naturality _ _ h := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map]
    exact Over.w ((Over.pullback sS).map ((specOver K L).map h))

/-- The cone from `Spec L ×_K S` over the schemes `Spec A ×_K S`. -/
def baseChangeCone : Cone (baseChangeDiagram (L := L) sS) :=
  (Over.pullback sS ⋙ Over.forget S).mapCone (specOverCone K L)

/-- The point of `baseChangeCone` is the fibre product `Spec L ×_K S`. -/
theorem baseChangeCone_pt :
    (baseChangeCone (L := L) sS).pt =
      pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))) sS :=
  rfl

/-- The legs of `baseChangeCone` are morphisms over `S`. -/
@[reassoc (attr := simp)]
theorem baseChangeCone_π_app_comp (A : (SmoothSubalgebra K L)ᵒᵖ) :
    (baseChangeCone (L := L) sS).π.app A ≫ (baseChangeDiagramToBase (L := L) sS).app A =
      pullback.snd _ _ :=
  Over.w ((Over.pullback sS).map ((specOverCone K L).π.app A))

/-- **`Spec L ×_K S` is the limit of the `Spec A ×_K S`**, for `L/K` separable and `A` running
over the smooth `K`-subalgebras of `L`. -/
def isLimitBaseChangeCone [Algebra.IsSeparableExtension K L] :
    IsLimit (baseChangeCone (L := L) sS) :=
  have : IsConnected (SmoothSubalgebra K L)ᵒᵖ := IsCofiltered.isConnected _
  isLimitOfPreserves (Over.pullback sS ⋙ Over.forget S) (isLimitSpecOverCone K L)

/-- **The levels are smooth over `S`**: `Spec A ×_K S ⟶ S` is the base change of the smooth
morphism `Spec A ⟶ Spec K`. -/
theorem smooth_baseChangeDiagramToBase_app (A : (SmoothSubalgebra K L)ᵒᵖ) :
    Smooth ((baseChangeDiagramToBase (L := L) sS).app A) := by
  have : Algebra.Smooth K A.unop.1 := A.unop.2
  have h₁ : Smooth (Spec.map (fromBase K L A.unop)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr this)
  have : Smooth ((specOver K L).obj A).hom := h₁
  exact inferInstanceAs (Smooth (pullback.snd _ _))

/-- **The transition morphisms are affine**: `Spec B ×_K S ⟶ Spec A ×_K S` is the base change of
the morphism `Spec B ⟶ Spec A` of affine schemes. -/
theorem isAffineHom_baseChangeDiagram_map ⦃A B : (SmoothSubalgebra K L)ᵒᵖ⦄ (h : A ⟶ B) :
    IsAffineHom ((baseChangeDiagram (L := L) sS).map h) := by
  have sq : IsPullback ((baseChangeDiagram (L := L) sS).map h) (pullback.fst _ _)
      (pullback.fst _ _) ((specOver K L).map h).left := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback ((specOver K L).obj B).hom sS).flip
    have h₁ : (baseChangeDiagram (L := L) sS).map h ≫ pullback.snd _ _ = pullback.snd _ _ :=
      pullback.lift_snd _ _ _
    have h₂ : ((specOver K L).map h).left ≫ ((specOver K L).obj B).hom =
        ((specOver K L).obj A).hom :=
      Over.w ((specOver K L).map h)
    rw [h₁, h₂]
    exact (IsPullback.of_hasPullback ((specOver K L).obj A).hom sS).flip
  have : IsAffineHom ((specOver K L).map h).left :=
    (inferInstance : IsAffineHom (Spec.map ((ringDiagram K L).map h.unop)))
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip this

end Stacks.EtaleCohomology.FieldExtensionLimit

end
