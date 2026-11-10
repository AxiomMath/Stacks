module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.GraphOfRelativeMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusInRelativeMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSiteFactorization

/-!
# Relative morphisms form an open subfunctor of the Hilbert functor (Stacks 0D1B)

Let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces over a scheme `S` of a big fppf
site. The graph transformation of Stacks 0D1A carries a relative morphism `(a, b)` at a test scheme
`T` to the graph of `b`, a point of the Hilbert functor of `Z ×_Q X` over `Q`. Stacks 0D1B asserts
that this transformation

```text
Mor_Q(Z, X) ⟶ Hilb_{Z ×_Q X / Q}
```

is representable by open immersions.

A subfunctor `Y ⊆ (Z ×_Q X)_T` is a graph exactly when the projection `k = pr_Z|_Y : Y ⟶ Z_T` is
an isomorphism; this holds for an arbitrary subfunctor, not only for a point of the Hilbert
functor. The projection `k` is the restriction to `Y` of a canonical retraction of `(Z ×_Q X)_T`
onto `Z_T` of which every graph map is a section; when `k` has a section `r`, the morphism `b` is
`r ≫ Y.ι ≫ pr_{Z ×_Q X} ≫ pr_X`, and when `r` is a two-sided inverse the graph of `b` is `Y`. By
Stacks 05XD (`AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isIso_baseChange`) the locus of
`T` over which `k` is invertible is an open subscheme of `T`.

## Main definitions

* `AlgebraicGeometry.Space.graphRetraction`: the canonical retraction `(Z ×_Q X)_W ⟶ Z_W`, the
  projection to `Z` of the ambient fibre product paired with the projection to `W`.
* `AlgebraicGeometry.Space.graphProjection`: the morphism `k = pr_Z|_Y` attached to a subfunctor
  `Y` of `(Z ×_Q X)_W`.
* `AlgebraicGeometry.Space.graphSectionMorphism` and
  `AlgebraicGeometry.Space.relativeMorphismOfSection`: the morphism `b`, and the relative morphism
  whose graph is `Y`, recovered from a section of `k`.
* `AlgebraicGeometry.Space.relativeHomSectionOfGraph`: that relative morphism read as a section of
  the relative morphism functor over the test scheme.

## Main results

* `AlgebraicGeometry.Space.graphMap_comp_graphRetraction`: every graph map is a section of the
  canonical retraction.
* `AlgebraicGeometry.Space.graphMap_eq_of_components`: the graph of a relative morphism is the
  unique morphism with its three components.
* `AlgebraicGeometry.Space.range_graphMap_relativeMorphismOfSection`: the graph of
  `AlgebraicGeometry.Space.relativeMorphismOfSection` is `Y`.
* `AlgebraicGeometry.Space.isIso_graphProjection_iff`: a subfunctor of `(Z ×_Q X)_T` is the graph
  of a relative morphism exactly when its projection to `Z_T` is an isomorphism.
* `AlgebraicGeometry.Space.graphTransformation_app_relativeHomSectionOfGraph`: the graph
  transformation hits every point of the Hilbert functor whose projection is an isomorphism.
* `AlgebraicGeometry.Space.isPullback_graphProjection_preimage` and
  `AlgebraicGeometry.Space.isIso_graphProjection_preimage_iff`: the projection of a subfunctor is
  stable under base change of the test object, and its base change over the base is invertible
  exactly when the projection of the inverse image is.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_isIso_graphProjection`: Stacks 05XD for a point
  of the Hilbert functor, as an open subscheme of the test scheme.
* `AlgebraicGeometry.Space.graphTransformation_relative_isOpenImmersion`: **Stacks 0D1B**, the
  graph transformation is representable by open immersions.

## References

* [Stacks Project, Tag 0D1B](https://stacks.math.columbia.edu/tag/0D1B)
* [Stacks Project, Tag 0D1A](https://stacks.math.columbia.edu/tag/0D1A)
* [Stacks Project, Tag 05XD](https://stacks.math.columbia.edu/tag/05XD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_RelativeMorphismsOpenInHilbert {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_RelativeMorphismsOpenInHilbert
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ Q) (x : X ⟶ Q)

/-- The canonical retraction `(Z ×_Q X)_W ⟶ Z_W` of the base change of the ambient space of the
graph construction onto the base change of `Z`: the projection to `Z` of the ambient fibre product,
paired with the projection to `W`. -/
def graphRetraction {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Q) :
    pullback (pullback.fst z x ≫ z) a ⟶ pullback a z :=
  pullback.lift (pullback.snd (pullback.fst z x ≫ z) a)
    (pullback.fst (pullback.fst z x ≫ z) a ≫ pullback.fst z x)
    (by rw [Category.assoc]; exact pullback.condition.symm)

/-- The canonical retraction followed by the projection `Z_W ⟶ W` is the projection
`(Z ×_Q X)_W ⟶ W`. -/
@[reassoc (attr := simp)]
theorem graphRetraction_fst {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Q) :
    graphRetraction z x a ≫ pullback.fst a z = pullback.snd (pullback.fst z x ≫ z) a :=
  pullback.lift_fst _ _ _

/-- The canonical retraction followed by the projection `Z_W ⟶ Z` is the projection
`(Z ×_Q X)_W ⟶ Z ×_Q X` followed by the projection to `Z`. -/
@[reassoc (attr := simp)]
theorem graphRetraction_snd {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Q) :
    graphRetraction z x a ≫ pullback.snd a z =
      pullback.fst (pullback.fst z x ≫ z) a ≫ pullback.fst z x :=
  pullback.lift_snd _ _ _

/-- The graph of a relative morphism is a section of the canonical retraction. -/
theorem graphMap_comp_graphRetraction {T : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) :
    graphMap p ≫ graphRetraction z x p.base = 𝟙 (pullback p.base z) := by
  apply pullback.hom_ext <;> simp [graphMap_snd, graphMap_fst_fst]

/-- The projection `k = pr_Z|_Y : Y ⟶ Z_W` of a subfunctor `Y` of the base change `(Z ×_Q X)_W`:
the inclusion of `Y` followed by the canonical retraction. -/
def graphProjection {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Q)
    (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a)) : Y.toFunctor ⟶ pullback a z :=
  Y.ι ≫ graphRetraction z x a

/-- The projection of `Y` followed by the projection `Z_W ⟶ W` is the inclusion of `Y` followed by
the projection `(Z ×_Q X)_W ⟶ W`. -/
@[reassoc (attr := simp)]
theorem graphProjection_comp_fst {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Q)
    (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a)) :
    graphProjection z x a Y ≫ pullback.fst a z =
      Y.ι ≫ pullback.snd (pullback.fst z x ≫ z) a := by
  rw [graphProjection, Category.assoc, graphRetraction_fst]

/-- The projection of `Y` followed by the projection `Z_W ⟶ Z` is the inclusion of `Y` followed by
the projection of `(Z ×_Q X)_W` to `Z`. -/
@[reassoc (attr := simp)]
theorem graphProjection_comp_snd {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Q)
    (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a)) :
    graphProjection z x a Y ≫ pullback.snd a z =
      Y.ι ≫ pullback.fst (pullback.fst z x ≫ z) a ≫ pullback.fst z x := by
  rw [graphProjection, Category.assoc, graphRetraction_snd]

/-- The inclusion of the range of a monomorphism of presheaves of types is that monomorphism read
through the isomorphism onto its range. -/
theorem range_ι_eq_inv_toRange_comp {C : Type*} [Category C] {F F' : C ⥤ Type u} (f : F' ⟶ F)
    [Mono f] : (Subfunctor.range f).ι = (asIso (Subfunctor.toRange f)).inv ≫ f :=
  (((asIso (Subfunctor.toRange f)).inv_comp_eq).2 (Subfunctor.toRange_ι f).symm).symm

/-- The graph of a relative morphism is the unique morphism into the base change of `Z ×_Q X` with
its three components: the projection to the test scheme, the projection to `Z`, and the morphism
itself. -/
theorem graphMap_eq_of_components {T : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T))
    (g : pullback p.base z ⟶ pullback (pullback.fst z x ≫ z) p.base)
    (h₁ : g ≫ pullback.snd (pullback.fst z x ≫ z) p.base = pullback.fst p.base z)
    (h₂ : g ≫ pullback.fst (pullback.fst z x ≫ z) p.base ≫ pullback.fst z x =
      pullback.snd p.base z)
    (h₃ : g ≫ pullback.fst (pullback.fst z x ≫ z) p.base ≫ pullback.snd z x = p.morphism) :
    graphMap p = g := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;>
    simp [graphMap_fst_fst, graphMap_fst_snd, graphMap_snd, h₁, h₂, h₃]

section OfSection

variable {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A section of the projection of `Y`, followed by the inclusion of `Y`, projects to `W` as the
projection of the base change of `Z`. -/
theorem comp_ι_comp_snd (a : W ⟶ Q) (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a))
    (r : pullback a z ⟶ Y.toFunctor)
    (hr : r ≫ graphProjection z x a Y = 𝟙 (pullback a z)) :
    (r ≫ Y.ι) ≫ pullback.snd (pullback.fst z x ≫ z) a = pullback.fst a z := by
  rw [Category.assoc, ← graphProjection_comp_fst, reassoc_of% hr]

/-- A section of the projection of `Y`, followed by the inclusion of `Y`, projects to `Z` as the
projection of the base change of `Z`. -/
theorem comp_ι_comp_fst_fst (a : W ⟶ Q) (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a))
    (r : pullback a z ⟶ Y.toFunctor)
    (hr : r ≫ graphProjection z x a Y = 𝟙 (pullback a z)) :
    (r ≫ Y.ι) ≫ pullback.fst (pullback.fst z x ≫ z) a ≫ pullback.fst z x =
      pullback.snd a z := by
  rw [Category.assoc, ← graphProjection_comp_snd, reassoc_of% hr]

/-- The morphism `b : Z_W ⟶ X` recovered from a subfunctor of `(Z ×_Q X)_W` together with a
section of its projection to `Z_W`: the section followed by the projection to `X`. -/
def graphSectionMorphism (a : W ⟶ Q) (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a))
    (r : pullback a z ⟶ Y.toFunctor) : pullback a z ⟶ X :=
  r ≫ Y.ι ≫ pullback.fst (pullback.fst z x ≫ z) a ≫ pullback.snd z x

/-- For a section `r` of the projection of `Y`, the morphism
`AlgebraicGeometry.Space.graphSectionMorphism` followed by `x` is the projection `Z_W ⟶ Z` followed
by `z`. -/
theorem graphSectionMorphism_comp (a : W ⟶ Q)
    (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a)) (r : pullback a z ⟶ Y.toFunctor)
    (hr : r ≫ graphProjection z x a Y = 𝟙 (pullback a z)) :
    graphSectionMorphism z x a Y r ≫ x = pullback.snd a z ≫ z := by
  have h₁ : pullback.snd z x ≫ x = pullback.fst z x ≫ z := pullback.condition.symm
  rw [graphSectionMorphism, ← comp_ι_comp_fst_fst z x a Y r hr]
  simp only [Category.assoc, h₁]

end OfSection

/-- The relative morphism whose graph is a given subfunctor of `(Z ×_Q X)_T`, built from a section
of the projection of that subfunctor to `Z_T`: its first component is the base of the subfunctor
and its second is `AlgebraicGeometry.Space.graphSectionMorphism`. -/
def relativeMorphismOfSection {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Q)
    (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a)) (r : pullback a z ⟶ Y.toFunctor)
    (hr : r ≫ graphProjection z x a Y = 𝟙 (pullback a z)) :
    RelativeMorphism B S hS Z X Q z x (yoneda.obj T) where
  base := a
  morphism := graphSectionMorphism z x a Y r
  commutes := graphSectionMorphism_comp z x a Y r hr

/-- The base of `AlgebraicGeometry.Space.relativeMorphismOfSection` is the base `a` of the
subfunctor. -/
@[simp]
theorem relativeMorphismOfSection_base {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Q)
    (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a)) (r : pullback a z ⟶ Y.toFunctor)
    (hr : r ≫ graphProjection z x a Y = 𝟙 (pullback a z)) :
    (relativeMorphismOfSection z x a Y r hr).base = a := rfl

/-- The graph map of `AlgebraicGeometry.Space.relativeMorphismOfSection` is the section followed by
the inclusion of the subfunctor. -/
theorem graphMap_relativeMorphismOfSection {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Q)
    (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a)) (r : pullback a z ⟶ Y.toFunctor)
    (hr : r ≫ graphProjection z x a Y = 𝟙 (pullback a z)) :
    graphMap (relativeMorphismOfSection z x a Y r hr) = r ≫ Y.ι :=
  graphMap_eq_of_components z x _ _ (comp_ι_comp_snd z x a Y r hr)
    (comp_ι_comp_fst_fst z x a Y r hr) (Category.assoc _ _ _)

/-- When the section is a two-sided inverse of the projection, the graph of
`AlgebraicGeometry.Space.relativeMorphismOfSection` is the subfunctor it was built from: a
subfunctor of `(Z ×_Q X)_T` whose projection to `Z_T` is an isomorphism really is a graph. -/
theorem range_graphMap_relativeMorphismOfSection {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Q)
    (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a)) (r : pullback a z ⟶ Y.toFunctor)
    (hr : r ≫ graphProjection z x a Y = 𝟙 (pullback a z))
    (hr' : graphProjection z x a Y ≫ r = 𝟙 Y.toFunctor) :
    Subfunctor.range (graphMap (relativeMorphismOfSection z x a Y r hr)) = Y := by
  have : IsIso r := ⟨graphProjection z x a Y, hr, hr'⟩
  have h : Subfunctor.range (r ≫ Y.ι) = Y := by
    rw [Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top,
      Subfunctor.range_ι]
  exact (congrArg Subfunctor.range (graphMap_relativeMorphismOfSection z x a Y r hr)).trans h

/-- The projection to `Z_T` of the graph of a relative morphism is an isomorphism: it is the
inverse of the isomorphism of `Z_T` onto that graph. -/
instance isIso_graphProjection_range_graphMap {T : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) :
    IsIso (graphProjection z x p.base (Subfunctor.range (graphMap p))) := by
  rw [graphProjection, range_ι_eq_inv_toRange_comp, Category.assoc,
    graphMap_comp_graphRetraction, Category.comp_id]
  infer_instance

/-- A subfunctor `Y` of the base change `(Z ×_Q X)_T` is the graph of a relative morphism exactly
when its projection `k = pr_Z|_Y : Y ⟶ Z_T` is an isomorphism. -/
theorem isIso_graphProjection_iff {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Q)
    (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a)) :
    IsIso (graphProjection z x a Y) ↔
      ∃ (b : pullback a z ⟶ X) (hb : b ≫ x = pullback.snd a z ≫ z),
        Subfunctor.range (graphMap (⟨a, b, hb⟩ :
          RelativeMorphism B S hS Z X Q z x (yoneda.obj T))) = Y := by
  refine ⟨fun _ ↦ ⟨graphSectionMorphism z x a Y (inv (graphProjection z x a Y)),
    graphSectionMorphism_comp z x a Y _ (IsIso.inv_hom_id _),
    range_graphMap_relativeMorphismOfSection z x a Y _ (IsIso.inv_hom_id _)
      (IsIso.hom_inv_id _)⟩, ?_⟩
  rintro ⟨b, hb, rfl⟩
  exact isIso_graphProjection_range_graphMap z x _

section Representability

variable (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

/-- The section of the relative morphism functor over `T` attached to a point `Y` of the Hilbert
functor of `Z ×_Q X` over `Q` and a section `r` of its projection to the base change of `Z`. -/
def relativeHomSectionOfGraph {T : BigFppfOver B S hS}
    (Y : HilbertFamilyOver (graphAmbientMap B S hS z x hZ hX hQ) T)
    (r : pullback Y.toBase z ⟶ Y.family.Z.toFunctor)
    (hr : r ≫ graphProjection z x Y.toBase Y.family.Z = 𝟙 (pullback Y.toBase z)) :
    (relativeHom B S hS Z X Q z x hZ hX hQ).obj (Opposite.op T) :=
  (relativeHomSections B S hS Z X Q z x hZ hX hQ T).symm
    (relativeMorphismOfSection z x Y.toBase Y.family.Z r hr)

/-- The graph transformation carries `AlgebraicGeometry.Space.relativeHomSectionOfGraph` back to
the point of the Hilbert functor it was built from: the transformation hits every point whose
projection to the base change of `Z` is an isomorphism. -/
theorem graphTransformation_app_relativeHomSectionOfGraph (hsep : IsSeparated B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z)
    (hproper : IsProper B S hS z) {T : BigFppfOver B S hS}
    (Y : HilbertFamilyOver (graphAmbientMap B S hS z x hZ hX hQ) T)
    (r : pullback Y.toBase z ⟶ Y.family.Z.toFunctor)
    (hr : r ≫ graphProjection z x Y.toBase Y.family.Z = 𝟙 (pullback Y.toBase z))
    (hr' : graphProjection z x Y.toBase Y.family.Z ≫ r = 𝟙 Y.family.Z.toFunctor) :
    (graphTransformation hZ hX hQ hsep hfp hflat hproper).app (Opposite.op T)
        (ULift.up (relativeHomSectionOfGraph z x hZ hX hQ Y r hr)) = Y := by
  have hsec : relativeHomSections B S hS Z X Q z x hZ hX hQ T
      (relativeHomSectionOfGraph z x hZ hX hQ Y r hr) =
      relativeMorphismOfSection z x Y.toBase Y.family.Z r hr := Equiv.apply_symm_apply _ _
  refine Eq.trans (congrArg
    (fun q : RelativeMorphism B S hS Z X Q z x (yoneda.obj T) =>
      (⟨q.base, graphHilbertFamily hZ hX hQ q hsep hfp hflat hproper⟩ :
        HilbertFamilyOver (graphAmbientMap B S hS z x hZ hX hQ) T)) hsec) ?_
  exact HilbertFamilyOver.ext rfl
    (heq_of_eq (range_graphMap_relativeMorphismOfSection z x Y.toBase Y.family.Z r hr hr'))

/-! ### The open locus of Stacks 05XD, read on the schemes of the site -/

/-- The canonical retraction is natural in the base: it carries the comparison map of the two base
changes of `Z ×_Q X` to the comparison map of the two base changes of `Z`. -/
theorem graphRetraction_comp_mapFst {W W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : W' ⟶ W)
    (a : W ⟶ Q) :
    graphRetraction z x (t ≫ a) ≫ pullback.mapFst t a z =
      pullback.mapSnd t (pullback.fst z x ≫ z) a ≫ graphRetraction z x a := by
  apply pullback.hom_ext <;> simp

/-- **The canonical retraction of `(Z ×_Q X)_W` onto `Z_W` is stable under base change of `W`.**
The square formed by the two retractions and the comparison maps of the two base changes of
`Z ×_Q X` and of `Z` is cartesian. -/
theorem isPullback_graphRetraction {W W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : W' ⟶ W)
    (a : W ⟶ Q) :
    IsPullback (pullback.mapSnd t (pullback.fst z x ≫ z) a) (graphRetraction z x (t ≫ a))
      (graphRetraction z x a) (pullback.mapFst t a z) := by
  refine IsPullback.of_bot ?_ (graphRetraction_comp_mapFst z x t a).symm
    (pullback.isPullback_mapFst t a z).flip
  simpa only [graphRetraction_fst] using
    (pullback.isPullback_mapSnd t (pullback.fst z x ≫ z) a).flip

/-- **The projection of the inverse image of a subfunctor is a base change of its projection.**
The square formed by the two projections and the comparison maps of the two base changes of `Z` is
cartesian. -/
theorem isPullback_graphProjection_preimage {W W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : W' ⟶ W)
    (a : W ⟶ Q) (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a)) :
    IsPullback (Y.fromPreimage (pullback.mapSnd t (pullback.fst z x ≫ z) a))
      (graphProjection z x (t ≫ a) (Y.preimage (pullback.mapSnd t (pullback.fst z x ≫ z) a)))
      (graphProjection z x a Y) (pullback.mapFst t a z) :=
  (Subfunctor.isPullback_preimage _ Y).paste_vert (isPullback_graphRetraction z x t a)

/-- **The base change over the base of the projection of `Y` is invertible exactly when the
projection of the inverse image of `Y` is.** The two agree up to the comparison isomorphism
`CategoryTheory.Limits.pullback.isoMapFst`. -/
theorem isIso_graphProjection_preimage_iff {W W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : W' ⟶ W)
    (a : W ⟶ Q) (Y : Subfunctor (pullback (pullback.fst z x ≫ z) a))
    (m : pullback (pullback.fst z x ≫ z) (t ≫ a) ⟶ pullback (pullback.fst z x ≫ z) a)
    (hm : m = pullback.mapSnd t (pullback.fst z x ≫ z) a) :
    IsIso (graphProjection z x (t ≫ a) (Y.preimage m)) ↔
      IsIso (baseChangeOverBase B S hS (graphProjection z x a Y)
        (Y.ι ≫ pullback.snd (pullback.fst z x ≫ z) a) (pullback.fst a z)
        (graphProjection_comp_fst z x a Y) t) := by
  subst hm
  have hcomm : IsPullback (pullback.fst (pullback.fst a z) t) (pullback.isoMapFst t a z).inv
      (𝟙 (pullback a z)) (pullback.mapFst t a z) := by
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [Category.comp_id, Iso.eq_inv_comp]
    exact pullback.isoMapFst_hom_comp_fst t a z
  have hC := (isPullback_baseChangeOverBase B S hS (graphProjection z x a Y)
    (Y.ι ≫ pullback.snd (pullback.fst z x ≫ z) a) (pullback.fst a z)
    (graphProjection_comp_fst z x a Y) t).paste_vert hcomm
  rw [Category.comp_id] at hC
  set e := (isPullback_graphProjection_preimage z x t a Y).isoIsPullback _ _ hC
  have hsnd : e.hom ≫ (baseChangeOverBase B S hS (graphProjection z x a Y)
        (Y.ι ≫ pullback.snd (pullback.fst z x ≫ z) a) (pullback.fst a z)
        (graphProjection_comp_fst z x a Y) t ≫ (pullback.isoMapFst t a z).inv) =
      graphProjection z x (t ≫ a)
        (Y.preimage (pullback.mapSnd t (pullback.fst z x ≫ z) a)) :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have key : baseChangeOverBase B S hS (graphProjection z x a Y)
      (Y.ι ≫ pullback.snd (pullback.fst z x ≫ z) a) (pullback.fst a z)
      (graphProjection_comp_fst z x a Y) t =
      e.inv ≫ graphProjection z x (t ≫ a)
        (Y.preimage (pullback.mapSnd t (pullback.fst z x ≫ z) a)) ≫
          (pullback.isoMapFst t a z).hom := by
    rw [← hsnd]
    simp
  rw [key, isIso_comp_left_iff, isIso_comp_right_iff]

/-- For a point `Y` of the Hilbert functor of `Z ×_Q X` over `Q` at `T`, there is an open subscheme
of `T` through which a morphism of the site factors exactly when the projection of the
base-changed family to the base change of `Z` is an isomorphism. -/
theorem exists_isOpenImmersion_isIso_graphProjection (hproper : IsProper B S hS z)
    (T : BigFppfOver B S hS)
    (Y : HilbertFamilyOver (graphAmbientMap B S hS z x hZ hX hQ) T) :
    ∃ (V : BigFppfOver B S hS) (s : V ⟶ T),
      MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
        (BigFppfOver.toScheme B S hS) s ∧
      ∀ (T' : BigFppfOver B S hS) (h : T' ⟶ T),
        (∃ t : T' ⟶ V, t ≫ s = h) ↔
          IsIso (graphProjection z x (Y.baseChange h).toBase (Y.baseChange h).family.Z) := by
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hqproper : IsProper B S hS (pullback.fst Y.toBase z) :=
    isProper_pullback_fst B S hS hZ hQ hT z Y.toBase hproper
  obtain ⟨W, hW, hWprop⟩ := exists_isOpenSubspace_iff_isIso_baseChange B S hS
    Y.family.closed.1 (isAlgebraicSpace_pullback B S hS Y.toBase z hT hZ hQ) hT
    (graphProjection z x Y.toBase Y.family.Z)
    (Y.family.Z.ι ≫ pullback.snd (pullback.fst z x ≫ z) Y.toBase) (pullback.fst Y.toBase z)
    (graphProjection_comp_fst z x Y.toBase Y.family.Z) Y.family.finitePresentation.1
    Y.family.flat Y.family.proper.2.2 hqproper.2.1.1
    (hproper.2.2 (yoneda.obj T) hT Y.toBase) hqproper.1
  obtain ⟨V, s, hs, hfac⟩ := exists_isOpenImmersion_forall_factorsThrough_iff B S hS W hW.2
  refine ⟨V, s, hs, fun T' h => (hfac T' h).trans
    ((hWprop (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T') (yoneda.map h)).trans
      (isIso_graphProjection_preimage_iff z x (yoneda.map h) Y.toBase Y.family.Z
        (schemeBaseChangeMap (graphAmbientMap B S hS z x hZ hX hQ)
          (HilbertFamilyOver.restrict h Y.toBase))
        (schemeBaseChangeMap_graphAmbientMap hZ hX hQ h Y.toBase)).symm)⟩

/-- The graph transformation `Mor_Q(Z, X) ⟶ Hilb_{Z ×_Q X / Q}` is representable by open
immersions. -/
@[stacks 0D1B]
theorem graphTransformation_relative_isOpenImmersion (hsep : IsSeparated B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z)
    (hproper : IsProper B S hS z) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
        (BigFppfOver.toScheme B S hS)).relative
      (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1, u})
      (graphTransformation hZ hX hQ hsep hfp hflat hproper) := by
  have _ : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
    (BigFppfOver.toScheme B S hS)).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative.of_exists
  intro T g
  obtain ⟨Y, rfl⟩ := uliftYonedaEquiv.symm.surjective g
  obtain ⟨V, s, hs, hV⟩ := exists_isOpenImmersion_isIso_graphProjection z x hZ hX hQ hproper T Y
  obtain ⟨rV, hrV₁, hrV₂⟩ := ((hV V s).1 ⟨𝟙 V, Category.id_comp s⟩).out
  have hmono : Mono s := by
    have h₁ : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map s) := hs
    exact (BigFppfOver.toScheme B S hS).mono_of_mono_map
      (inferInstanceAs (Mono ((BigFppfOver.toScheme B S hS).map s)))
  have key : ∀ (T' : BigFppfOver B S hS) (h : T' ⟶ V),
      (graphTransformation hZ hX hQ hsep hfp hflat hproper).app (Opposite.op T')
          (ULift.up ((relativeHom B S hS Z X Q z x hZ hX hQ).map h.op
            (relativeHomSectionOfGraph z x hZ hX hQ (Y.baseChange s) rV hrV₂))) =
        Y.baseChange (h ≫ s) := by
    intro T' h
    refine Eq.trans (types_congr_hom
      ((graphTransformation hZ hX hQ hsep hfp hflat hproper).naturality h.op)
      (ULift.up (relativeHomSectionOfGraph z x hZ hX hQ (Y.baseChange s) rV hrV₂))) ?_
    refine Eq.trans (congrArg (fun w => (hilbertPresheaf
        (graphAmbientMap B S hS z x hZ hX hQ)).map h.op w)
      (graphTransformation_app_relativeHomSectionOfGraph z x hZ hX hQ hsep hfp hflat hproper
        (Y.baseChange s) rV hrV₂ hrV₁)) ?_
    exact HilbertFamilyOver.baseChange_comp s h Y
  refine ⟨V, uliftYonedaEquiv.symm (ULift.up
    (relativeHomSectionOfGraph z x hZ hX hQ (Y.baseChange s) rV hrV₂)), s, ?_, hs⟩
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨T'⟩
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨h⟩
    exact key T' h
  · rintro ⟨h⟩ ⟨h'⟩ ⟨-, hl⟩
    exact congrArg ULift.up (hmono.right_cancellation h h' (congrArg ULift.down hl))
  · rintro ⟨p⟩ ⟨h⟩ hrb
    have heq : (graphTransformation hZ hX hQ hsep hfp hflat hproper).app (Opposite.op T')
        (ULift.up p) = Y.baseChange h := hrb
    have hiso : IsIso (graphProjection z x (Y.baseChange h).toBase
        (Y.baseChange h).family.Z) := by
      rw [← heq]
      exact isIso_graphProjection_range_graphMap z x
        (relativeHomSections B S hS Z X Q z x hZ hX hQ T' p)
    obtain ⟨t, ht⟩ := (hV T' h).2 hiso
    refine ⟨ULift.up t, ?_, congrArg ULift.up ht⟩
    refine graphTransformation_injective hZ hX hQ hsep hfp hflat hproper T' ?_
    exact (key T' t).trans (by rw [ht]; exact heq.symm)

end Representability

end AlgebraicGeometry.Space

end
