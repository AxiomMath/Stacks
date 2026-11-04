module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.RingTheory.SimpleRing.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksCore.Tactic.StacksAttribute

/-!
# Elementary étale neighbourhoods as a fibre functor on the small étale site

Let `x` be a point of a scheme `X`. An étale neighbourhood `(U, u)` of `(X, x)` is *elementary*
when the induced extension of residue fields `κ(x) ⟶ κ(u)` is trivial. Such a neighbourhood is
the same thing as an object `U` of the small étale site `X.Etale` together with a lift of the
canonical morphism `Spec κ(x) ⟶ X` to `U`: a lift has image a point `u` over `x` and splits the
residue field extension, which for an extension of fields forces it to be trivial, and conversely
the inverse of the residue field isomorphism produces the lift.

The point of saying it this way is that the lifts assemble into a functor
`elementaryEtaleFiber X x : X.Etale ⥤ Type u`, so that Mathlib's theory of fibre functors applies
verbatim: the category of elements of a `Type`-valued functor preserving finite limits is
cofiltered, and the affine refinements of a lift form a `u`-small weakly initial family. The
second property transfers to the category `AlgebraicGeometry.ElementaryEtaleNeighborhood X x` of
elementary étale neighbourhoods, and that is what makes the colimit of a presheaf on the small
étale site over the elementary étale neighbourhoods of a point exist.

## Main definitions

* `Stacks.EtaleCohomology.elementaryEtaleFiber` — the lifts of `Spec κ(x) ⟶ X` to an object of
  the small étale site, as a functor to `Type u`.
* `Stacks.EtaleCohomology.toElementaryEtaleNeighborhood` — the functor from the category of
  elements of that fibre functor to the category of elementary étale neighbourhoods.
* `Stacks.EtaleCohomology.elementaryEtaleNeighborhoodToSmallEtale` — an elementary étale
  neighbourhood, read as an object of the small étale site.

## Main results

* `Stacks.EtaleCohomology.isIso_residueFieldMap_of_comp_eq_fromSpecResidueField` — a lift of
  `Spec κ(x) ⟶ X` through a morphism `f` makes the residue field map of `f` at the image point an
  isomorphism; this is what makes the associated neighbourhood elementary.
* `Stacks.EtaleCohomology.toElementaryEtaleNeighborhoodObjIso` — every elementary étale
  neighbourhood is isomorphic to the one attached to a lift.
* `Stacks.EtaleCohomology.isCofiltered_elementaryEtaleNeighborhood` — the category of elementary
  étale neighbourhoods is cofiltered (Tag 057B).
* `Stacks.EtaleCohomology.initiallySmall_elementaryEtaleNeighborhood` — it admits a `u`-small
  weakly initial family, so `u`-small colimits suffice to form colimits over its opposite.

## Implementation notes

The elementariness of a lift is proved by transporting the defining equation through
`AlgebraicGeometry.Scheme.SpecToEquivOfField`, which identifies a morphism `Spec K ⟶ Y` with a
point of `Y` together with an embedding of its residue field into `K`. The equation says that the
composite embedding `κ(x) ⟶ κ(u) ⟶ κ(x)` is the canonical identification, so the first factor is
split; a ring homomorphism out of a simple ring into a nonzero ring is injective, so the
retraction is bijective and both factors are isomorphisms.

The category of elementary étale neighbourhoods and the proof that its opposite is filtered are
taken from `StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization`; this file
adds only the passage to the small étale site and the smallness statement, neither of which the
henselization development needs, since it exhibits an explicit colimit cocone rather than
asserting that the colimit exists.

## References

* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
* [Stacks Project, Tag 057A](https://stacks.math.columbia.edu/tag/057A)
* [Stacks Project, Tag 057B](https://stacks.math.columbia.edu/tag/057B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- If a composite of homomorphisms of commutative rings is an isomorphism, the ring in the middle
is simple and the target is nonzero, then the first factor is an isomorphism: the second factor is
surjective because the composite is, and injective because its source is simple. -/
public theorem isIso_of_comp_eq_isIso_of_isSimpleRing {A B C : CommRingCat.{u}}
    [IsSimpleRing B] [Nontrivial C] {g : A ⟶ B} {h : B ⟶ C} {k : A ⟶ C}
    (hk : g ≫ h = k) (hkiso : IsIso k) : IsIso g := by
  have hgh : IsIso (g ≫ h) := hk ▸ hkiso
  have hbij := (ConcreteCategory.isIso_iff_bijective (g ≫ h)).1 hgh
  have hsurj : Function.Surjective h := fun c => by
    obtain ⟨a, ha⟩ := hbij.2 c
    exact ⟨_, ha⟩
  have : IsIso h := (ConcreteCategory.isIso_iff_bijective h).2 ⟨h.hom.injective, hsurj⟩
  exact IsIso.of_isIso_comp_right _ h

variable {X : Scheme.{u}} {x : X}

/-- **The residue field extension at a split point is trivial.** If `f : Y ⟶ X` admits a lift
`p : Spec κ(x) ⟶ Y` of the canonical morphism `Spec κ(x) ⟶ X`, then the residue field map of `f`
at the image of `p` is an isomorphism. -/
public theorem isIso_residueFieldMap_of_comp_eq_fromSpecResidueField {Y : Scheme.{u}} (f : Y ⟶ X)
    (p : Spec (X.residueField x) ⟶ Y) (hp : p ≫ f = X.fromSpecResidueField x)
    (z : Spec (X.residueField x)) : IsIso (f.residueFieldMap (p z)) := by
  obtain rfl : z = IsLocalRing.closedPoint (↑(X.residueField x) : Type u) :=
    Subsingleton.elim _ _
  have hfrom : (Scheme.SpecToEquivOfField (↑(X.residueField x) : Type u) X)
      (X.fromSpecResidueField x) = ⟨x, 𝟙 (X.residueField x)⟩ := by
    apply (Scheme.SpecToEquivOfField (↑(X.residueField x) : Type u) X).symm.injective
    simp only [Equiv.symm_apply_apply, Scheme.SpecToEquivOfField_symm_apply, Spec.map_id]
    exact (Category.id_comp _).symm
  have key := congrArg (Scheme.SpecToEquivOfField (↑(X.residueField x) : Type u) X) hp
  rw [hfrom, Scheme.SpecToEquivOfField_eq_iff] at key
  obtain ⟨e, he⟩ := key
  simp only [Scheme.SpecToEquivOfField_apply_snd, Category.comp_id] at he
  exact isIso_of_comp_eq_isIso_of_isSimpleRing
    ((Scheme.descResidueField_stalkClosedPointTo_comp
      (K := (↑(X.residueField x) : Type u)) (f := f) p).symm.trans he)
    (X.residueFieldCongr e).isIso_hom

/-- The lifts of the canonical morphism `Spec κ(x) ⟶ X` to the objects of the small étale site of
`X`, as a functor to `Type u`. Its category of elements is the category of elementary étale
neighbourhoods of `(X, x)`. -/
public def elementaryEtaleFiber (X : Scheme.{u}) (x : X) : X.Etale ⥤ Type u :=
  Scheme.Etale.forget X ⋙ coyoneda.obj (op (Over.mk (X.fromSpecResidueField x)))

/-- The underlying morphism of schemes of a lift. -/
public def elementaryEtaleFiberHom {W : X.Etale} (p : (elementaryEtaleFiber X x).obj W) :
    Spec (X.residueField x) ⟶ W.left := p.left

/-- The defining property of a lift: composing it with the structure morphism gives the canonical
morphism `Spec κ(x) ⟶ X`. -/
public theorem elementaryEtaleFiber_w {W : X.Etale} (p : (elementaryEtaleFiber X x).obj W) :
    elementaryEtaleFiberHom p ≫ (W.hom : W.left ⟶ X) = X.fromSpecResidueField x := Over.w p

/-- The image under a lift of the unique point of `Spec κ(x)` is a point lying over `x`. -/
public theorem elementaryEtaleFiber_map_point {W : X.Etale}
    (p : (elementaryEtaleFiber X x).obj W) (z : Spec (X.residueField x)) :
    (W.hom : W.left ⟶ X) (elementaryEtaleFiberHom p z) = x := by
  have h := congrArg (fun g : Spec (X.residueField x) ⟶ X => g z) (elementaryEtaleFiber_w p)
  rw [Scheme.fromSpecResidueField_apply] at h
  exact h

/-- The étale neighbourhood of `(X, x)` underlying a lift of `Spec κ(x) ⟶ X`. -/
public def etaleNeighborhoodOfFiber {W : X.Etale} (p : (elementaryEtaleFiber X x).obj W) :
    EtaleNeighborhood X x where
  scheme := W.left
  point := elementaryEtaleFiberHom p (default : Spec (X.residueField x))
  toBase := (W.hom : W.left ⟶ X)
  etale_toBase := W.prop
  map_point := elementaryEtaleFiber_map_point p _

/-- The scheme of the étale neighbourhood of a lift is the source of the étale morphism. -/
@[simp]
public theorem etaleNeighborhoodOfFiber_scheme {W : X.Etale}
    (p : (elementaryEtaleFiber X x).obj W) : (etaleNeighborhoodOfFiber p).scheme = W.left := rfl

/-- The distinguished point of the étale neighbourhood of a lift is the image of the unique point
of `Spec κ(x)`. -/
@[simp]
public theorem etaleNeighborhoodOfFiber_point {W : X.Etale}
    (p : (elementaryEtaleFiber X x).obj W) :
    (etaleNeighborhoodOfFiber p).point =
      elementaryEtaleFiberHom p (default : Spec (X.residueField x)) := rfl

/-- The morphism to `X` of the étale neighbourhood of a lift is the structure morphism of the
object of the small étale site. -/
@[simp]
public theorem etaleNeighborhoodOfFiber_toBase {W : X.Etale}
    (p : (elementaryEtaleFiber X x).obj W) :
    (etaleNeighborhoodOfFiber p).toBase = (W.hom : W.left ⟶ X) := rfl

/-- The étale neighbourhood underlying a lift of `Spec κ(x) ⟶ X` is elementary. -/
public theorem isElementary_etaleNeighborhoodOfFiber {W : X.Etale}
    (p : (elementaryEtaleFiber X x).obj W) : (etaleNeighborhoodOfFiber p).IsElementary := by
  rw [EtaleNeighborhood.isElementary_iff, etaleNeighborhoodOfFiber_toBase,
    etaleNeighborhoodOfFiber_point]
  exact isIso_residueFieldMap_of_comp_eq_fromSpecResidueField (W.hom : W.left ⟶ X)
    (elementaryEtaleFiberHom p) (elementaryEtaleFiber_w p) _

/-- The functor from the category of elements of `elementaryEtaleFiber X x` to the category of
elementary étale neighbourhoods of `(X, x)`: a lift is sent to the étale neighbourhood it defines,
and a morphism of lifts to the underlying morphism of schemes. -/
public def toElementaryEtaleNeighborhood (X : Scheme.{u}) (x : X) :
    (elementaryEtaleFiber X x).Elements ⥤ ElementaryEtaleNeighborhood X x where
  obj j := ⟨etaleNeighborhoodOfFiber j.2, isElementary_etaleNeighborhoodOfFiber j.2⟩
  map {j j'} f := ObjectProperty.homMk
    { hom := f.1.left
      over := MorphismProperty.Over.w f.1
      map_point := by
        have h := congrArg
          (fun g : Over.mk (X.fromSpecResidueField x) ⟶ (Scheme.Etale.forget X).obj j'.1 =>
            g.left (default : Spec (X.residueField x))) f.2
        exact h }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An elementary étale neighbourhood of `(X, x)`, read as an object of the small étale site. -/
public def elementaryEtaleNeighborhoodToSmallEtale (X : Scheme.{u}) (x : X) :
    ElementaryEtaleNeighborhood X x ⥤ X.Etale where
  obj N := Scheme.Etale.mk N.obj.toBase
  map f := MorphismProperty.Over.homMk f.hom.hom f.hom.over trivial
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The scheme underlying an elementary étale neighbourhood, read as an object of the small étale
site, is the scheme of the neighbourhood. -/
@[simp]
public theorem elementaryEtaleNeighborhoodToSmallEtale_obj_left
    (N : ElementaryEtaleNeighborhood X x) :
    ((elementaryEtaleNeighborhoodToSmallEtale X x).obj N).left = N.obj.scheme := rfl

/-- The structure morphism of an elementary étale neighbourhood, read as an object of the small
étale site, is the morphism of the neighbourhood to `X`. -/
@[simp]
public theorem elementaryEtaleNeighborhoodToSmallEtale_obj_hom
    (N : ElementaryEtaleNeighborhood X x) :
    (((elementaryEtaleNeighborhoodToSmallEtale X x).obj N).hom : N.obj.scheme ⟶ X) =
      N.obj.toBase := rfl

/-- The inverse of the residue field isomorphism of an elementary étale neighbourhood. -/
public def invResidueFieldMap (N : ElementaryEtaleNeighborhood X x) :
    N.obj.scheme.residueField N.obj.point ⟶ X.residueField x :=
  @inv _ _ _ _ N.obj.residueFieldMap N.property

/-- The residue field map of the structure morphism of an elementary étale neighbourhood, followed
by the inverse of its residue field isomorphism, is the canonical identification of `κ(x)` with
the residue field at the image of the distinguished point. -/
public theorem residueFieldMap_comp_invResidueFieldMap (N : ElementaryEtaleNeighborhood X x) :
    N.obj.toBase.residueFieldMap N.obj.point ≫ invResidueFieldMap N =
      (X.residueFieldCongr N.obj.map_point).hom := by
  have hN : IsIso N.obj.residueFieldMap := N.property
  have h1 : (X.residueFieldCongr N.obj.map_point).inv ≫
      (N.obj.toBase.residueFieldMap N.obj.point ≫ invResidueFieldMap N) = 𝟙 _ := by
    rw [← Category.assoc, ← EtaleNeighborhood.residueFieldMap_def]
    exact IsIso.hom_inv_id _
  rw [← cancel_epi ((X.residueFieldCongr N.obj.map_point).inv), h1, Iso.inv_hom_id]

/-- The underlying morphism of schemes of the lift attached to an elementary étale
neighbourhood. -/
public def fiberHomOfElementaryEtaleNeighborhood (N : ElementaryEtaleNeighborhood X x) :
    Spec (X.residueField x) ⟶ N.obj.scheme :=
  Spec.map (invResidueFieldMap N) ≫ N.obj.scheme.fromSpecResidueField N.obj.point

/-- The lift of `Spec κ(x) ⟶ X` attached to an elementary étale neighbourhood: the inverse of its
residue field isomorphism, followed by the canonical morphism out of the residue field at the
distinguished point. -/
public def fiberOfElementaryEtaleNeighborhood (N : ElementaryEtaleNeighborhood X x) :
    (elementaryEtaleFiber X x).obj ((elementaryEtaleNeighborhoodToSmallEtale X x).obj N) := by
  refine Over.homMk (fiberHomOfElementaryEtaleNeighborhood N) ?_
  change fiberHomOfElementaryEtaleNeighborhood N ≫ N.obj.toBase = X.fromSpecResidueField x
  rw [fiberHomOfElementaryEtaleNeighborhood, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc,
    residueFieldMap_comp_invResidueFieldMap, Scheme.residueFieldCongr_fromSpecResidueField]

/-- The lift attached to an elementary étale neighbourhood has the distinguished point as its
image. -/
public theorem fiberOfElementaryEtaleNeighborhood_apply (N : ElementaryEtaleNeighborhood X x) :
    elementaryEtaleFiberHom (fiberOfElementaryEtaleNeighborhood N)
      (default : Spec (X.residueField x)) = N.obj.point := by
  show fiberHomOfElementaryEtaleNeighborhood N (default : Spec (X.residueField x)) =
    N.obj.point
  simp [fiberHomOfElementaryEtaleNeighborhood]

/-- The neighbourhood attached to the lift `fiberOfElementaryEtaleNeighborhood N` is isomorphic to
`N` by the identity on the underlying scheme: the two differ only in how the distinguished point
is named. -/
public def etaleNeighborhoodIsoOfFiber (N : ElementaryEtaleNeighborhood X x) :
    etaleNeighborhoodOfFiber (fiberOfElementaryEtaleNeighborhood N) ≅ N.obj where
  hom :=
    { hom := 𝟙 N.obj.scheme
      over := by simp
      map_point := fiberOfElementaryEtaleNeighborhood_apply N }
  inv :=
    { hom := 𝟙 N.obj.scheme
      over := by simp
      map_point := (fiberOfElementaryEtaleNeighborhood_apply N).symm }
  hom_inv_id := EtaleNeighborhood.Hom.ext (by simp)
  inv_hom_id := EtaleNeighborhood.Hom.ext (by simp)

/-- **Every elementary étale neighbourhood comes from a lift.** The neighbourhood attached to the
lift `fiberOfElementaryEtaleNeighborhood N` is isomorphic to `N`. -/
public def toElementaryEtaleNeighborhoodObjIso (N : ElementaryEtaleNeighborhood X x) :
    (toElementaryEtaleNeighborhood X x).obj
      (Functor.elementsMk _ _ (fiberOfElementaryEtaleNeighborhood N)) ≅ N :=
  ObjectProperty.isoMk _ (etaleNeighborhoodIsoOfFiber N)

/-- **Stacks 057B.** The category of elementary étale neighbourhoods of a point of a scheme is
cofiltered: two neighbourhoods are dominated by their fibre product and two morphisms of
elementary neighbourhoods are equalized after a refinement, both by Tag 057A. -/
@[stacks 057B]
public instance isCofiltered_elementaryEtaleNeighborhood (X : Scheme.{u}) (x : X) :
    IsCofiltered (ElementaryEtaleNeighborhood X x) :=
  (isFiltered_op_iff_isCofiltered (ElementaryEtaleNeighborhood X x)).1 inferInstance

/-- The lifts of `Spec κ(x) ⟶ X` form a cofiltered category of elements, because the small étale
site has finite limits and both the forgetful functor to `Over X` and a corepresentable functor
preserve them. -/
public instance isCofiltered_elementaryEtaleFiber_elements (X : Scheme.{u}) (x : X) :
    IsCofiltered (elementaryEtaleFiber X x).Elements :=
  Functor.isCofiltered_elements
    (Scheme.Etale.forget X ⋙ coyoneda.obj (op (Over.mk (X.fromSpecResidueField x))))

/-- The lifts of `Spec κ(x) ⟶ X` admit a `u`-small weakly initial family: every lift factors
through an affine open neighbourhood of its image, and the affine schemes étale over `X` form an
essentially `u`-small category. -/
public instance initiallySmall_elementaryEtaleFiber_elements (X : Scheme.{u}) (x : X) :
    InitiallySmall.{u} (elementaryEtaleFiber X x).Elements :=
  initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
    (Functor.Elements.precomp (Scheme.AffineEtale.Spec X)
      (elementaryEtaleFiber X x)).essImage (by
    rintro ⟨W, p⟩
    cases W with | _ Y f
    obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective p
    dsimp at y hy
    obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec (.of R) ⟶ Y)
        (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
      obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
        (x := y.base default) (U := ⊤) (by simp)
      refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    exact ⟨_,
      ⟨Functor.elementsMk _ (Scheme.AffineEtale.mk (j ≫ f)) (Over.homMk y'), ⟨Iso.refl _⟩⟩,
      ⟨⟨MorphismProperty.Over.homMk j rfl trivial, by cat_disch⟩⟩⟩)

/-- The elementary étale neighbourhoods of a point admit a `u`-small weakly initial family: the
lifts of `Spec κ(x) ⟶ X` do, and every elementary étale neighbourhood is isomorphic to the one
attached to a lift. -/
public instance initiallySmall_elementaryEtaleNeighborhood (X : Scheme.{u}) (x : X) :
    InitiallySmall.{u} (ElementaryEtaleNeighborhood X x) := by
  obtain ⟨T, hT, hTinit⟩ :=
    InitiallySmall.exists_small_weakly_initial_set.{u} (elementaryEtaleFiber X x).Elements
  have : Small.{u} T := hT
  refine initiallySmall_of_small_weakly_initial_set
    ((toElementaryEtaleNeighborhood X x).obj '' T) (fun N => ?_)
  obtain ⟨j, hj, ⟨g⟩⟩ := hTinit (Functor.elementsMk _ _ (fiberOfElementaryEtaleNeighborhood N))
  exact ⟨(toElementaryEtaleNeighborhood X x).obj j, ⟨j, hj, rfl⟩,
    ⟨(toElementaryEtaleNeighborhood X x).map g ≫ (toElementaryEtaleNeighborhoodObjIso N).hom⟩⟩

/-- `u`-small colimits suffice to form colimits indexed by the opposite of the category of
elementary étale neighbourhoods of a point. -/
public instance hasColimitsOfShape_elementaryEtaleNeighborhood (X : Scheme.{u}) (x : X)
    {A : Type*} [Category A] [HasColimitsOfSize.{u, u} A] :
    HasColimitsOfShape (ElementaryEtaleNeighborhood X x)ᵒᵖ A :=
  hasColimitsOfShape_of_finallySmall _ _

end Stacks.EtaleCohomology

end
