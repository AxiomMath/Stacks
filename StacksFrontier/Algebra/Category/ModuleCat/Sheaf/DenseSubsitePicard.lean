module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteSheafTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.DenseSubsiteRingedSite

/-!
# The Picard group is unchanged by restriction to a dense subsite

Let `X` be a ringed site and let `G : C ⥤ X.C` exhibit `(C, J)` as a dense subsite of
`(X.C, X.J)`, so that `AlgebraicGeometry.RingedSite.denseRestrict J X G` is the site `(C, J)`
with the restricted structure sheaf. Assuming the Comparison Lemma for sheaves of abelian
groups, restriction of sections along `G` is an isomorphism from the Picard group of `X` onto
the Picard group of the restriction, and it sends the class of an invertible sheaf of modules to
the class of its restriction.

This is Stacks 03DG method (2) for the Picard group: the Picard group of a ringed topos does not
depend on the site presenting it.

## Main definitions and results

* `AlgebraicGeometry.RingedSite.denseRestrictModules`: restriction of sheaves of modules to the
  dense subsite.
* `AlgebraicGeometry.RingedSite.denseRestrictModulesTensorIso`: it commutes with the tensor
  product sheaf.
* `AlgebraicGeometry.RingedSite.isInvertible_denseRestrictModules_obj` and
  `AlgebraicGeometry.RingedSite.isInvertible_of_isInvertible_denseRestrictModules_obj`:
  restriction preserves and reflects invertibility.
* `AlgebraicGeometry.RingedSite.denseRestrictInvertibleModules`: the induced functor on the
  categories of invertible sheaves of modules; it is full, faithful and essentially surjective.
* `AlgebraicGeometry.RingedSite.picardGroupDenseRestrictAddEquiv`: **the Picard group of a
  ringed site is the Picard group of its restriction to a dense subsite.**
* `AlgebraicGeometry.RingedSite.picardGroupDenseRestrictAddEquiv_classOf`: the isomorphism sends
  the class of an invertible sheaf of modules to the class of its restriction, which pins it
  rather than only asserting that the two groups are isomorphic.

## Implementation notes

Restriction of sheaves of modules is `Stacks.DenseSubsiteModules.moduleRestriction`, which is
fully faithful for a dense subsite with no further hypothesis and essentially surjective as soon
as the Comparison Lemma holds for `AddCommGrpCat`. Its source and target are spelled here with
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`, which is the spelling the Picard
group and the tensor product sheaf use; `AlgebraicGeometry.RingedSite.ringSheaf` of either site
is definitionally that sheaf of rings but not syntactically, and instance search for the full
subcategory of invertible modules does not see through the difference, so the three instances are
transported once by `inferInstanceAs` and everything downstream is stated in the one spelling.

Invertibility travels in both directions by the tensor-inverse criterion
`Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit` of Tag 0B8K, using
`Stacks.DenseSubsiteModules.moduleRestriction_sheafTensorRight` for the tensor product and the
fact that restriction carries the structure sheaf to the structure sheaf, which holds on the
nose because `moduleRestriction` is `SheafOfModules.pushforward (𝟙 _)`. The reflecting direction
needs essential surjectivity, to produce a tensor inverse upstairs out of one downstairs, and
full faithfulness, to pull its defining isomorphism back.

On Picard groups the comparison is skeleton transport: both Picard groups are identified with
the skeleton of the category of invertible sheaves of modules by the `classEquiv` field of
`Stacks.SheafOfModules.Picard.picardGroupData`, and a full, faithful, essentially surjective
functor induces a bijection of skeleta (`CategoryTheory.Functor.mapSkeleton_injective` and
`CategoryTheory.Functor.mapSkeleton_surjective`). Additivity is then checked on classes, where
both additions are the tensor product sheaf by
`Stacks.SheafOfModules.Picard.classOf_tensor`.

The hypotheses are the ones the Picard group and the tensor product sheaf already demand, now on
both topologies, together with the Comparison Lemma for `AddCommGrpCat`. The
`HasSheafCompose (forget₂ CommRingCat RingCat)` instances are not hypotheses: they hold on every
site by `AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat`, and are supplied as
`letI` where the tensor comparison asks for them.

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG), method (2)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
* [Stacks Project, Tag 040C](https://stacks.math.columbia.edu/tag/040C)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.SheafOfModules

universe w u₁ v₁ u₂ v₂

namespace AlgebraicGeometry.RingedSite

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (X : RingedSite.{u₂, v₂, w}) (G : C ⥤ X.C) [G.IsDenseSubsite J X.J]

/-! ### The sheafification hypotheses on the restricted site

The topology of `AlgebraicGeometry.RingedSite.denseRestrict J X G` is `J`, but only
definitionally, so instance search does not carry a hypothesis on `J` over to it. These
instances do the carrying. -/

/-- Sheaves of abelian groups on the restricted site admit weak sheafification whenever they do
on `J`. -/
instance hasWeakSheafify_denseRestrict [HasWeakSheafify J AddCommGrpCat.{w}] :
    HasWeakSheafify (denseRestrict J X G).J AddCommGrpCat.{w} :=
  inferInstanceAs (HasWeakSheafify J AddCommGrpCat.{w})

/-- On the restricted site, the morphisms of presheaves of abelian groups inverted by
sheafification are the locally bijective ones whenever this holds for `J`. -/
instance wEqualsLocallyBijective_denseRestrict
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    (denseRestrict J X G).J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  inferInstanceAs (J.WEqualsLocallyBijective AddCommGrpCat.{w})

/-- The abelian group structure on the Picard group of the restricted ringed site, named for the
same reason as `Stacks.Cohomology.Torsors.Generators.picardGroupAddCommGroup`: instance search
does not find it through the projections of `AlgebraicGeometry.RingedSite.denseRestrict`. -/
instance addCommGroupPicardGroupDenseRestrict [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    AddCommGroup (Picard.PicardGroup (denseRestrict J X G).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property) :=
  Stacks.Cohomology.Torsors.Generators.picardGroupAddCommGroup (denseRestrict J X G)

/-! ### Restriction of sheaves of modules -/

/-- **Restriction of sheaves of modules to a dense subsite.** A sheaf of modules over the
structure sheaf of `X` restricts to a sheaf of modules over the structure sheaf of
`AlgebraicGeometry.RingedSite.denseRestrict J X G`. -/
abbrev denseRestrictModules :
    SheafOfModules.{w} (TensorSheafification.structureSheaf X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) ⥤
      SheafOfModules.{w} (TensorSheafification.structureSheaf (denseRestrict J X G).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property) :=
  Stacks.DenseSubsiteModules.moduleRestriction J X.J G (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- Restriction of sheaves of modules to a dense subsite is faithful. -/
instance faithful_denseRestrictModules : (denseRestrictModules J X G).Faithful :=
  inferInstanceAs (Stacks.DenseSubsiteModules.moduleRestriction J X.J G
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Faithful

/-- Restriction of sheaves of modules to a dense subsite is full. -/
instance full_denseRestrictModules : (denseRestrictModules J X G).Full :=
  inferInstanceAs (Stacks.DenseSubsiteModules.moduleRestriction J X.J G
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Full

/-- Restriction of sheaves of modules to a dense subsite is essentially surjective, given the
Comparison Lemma for sheaves of abelian groups. -/
instance essSurj_denseRestrictModules
    [(G.sheafPushforwardContinuous AddCommGrpCat.{w} J X.J).IsEquivalence] :
    (denseRestrictModules J X G).EssSurj :=
  inferInstanceAs (Stacks.DenseSubsiteModules.moduleRestriction J X.J G
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).EssSurj

/-- Restriction of sheaves of modules to a dense subsite carries the structure sheaf to the
structure sheaf, on the nose. -/
theorem denseRestrictModules_obj_unit :
    (denseRestrictModules J X G).obj
        (SheafOfModules.unit (TensorSheafification.structureSheaf X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)) =
      SheafOfModules.unit (TensorSheafification.structureSheaf (denseRestrict J X G).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property) :=
  rfl

/-! ### Invertibility -/

section Invertible

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Restriction to a dense subsite commutes with the tensor product sheaf.** -/
def denseRestrictModulesTensorIso
    (L N : SheafOfModules.{w}
      (TensorSheafification.structureSheaf X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)) :
    (denseRestrictModules J X G).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj L).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor (denseRestrict J X G).O).obj
          ((denseRestrictModules J X G).obj L)).obj ((denseRestrictModules J X G).obj N) :=
  letI : X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) :=
    X.hasSheafCompose_forget₂_ringCat
  letI : J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) :=
    (denseRestrict J X G).hasSheafCompose_forget₂_ringCat
  (Stacks.DenseSubsiteModules.moduleRestriction_sheafTensorRight J X.J G X.O N).app L

/-- **Restriction to a dense subsite preserves invertibility.** A tensor inverse of `L`
restricts to a tensor inverse of the restriction of `L`. -/
theorem isInvertible_denseRestrictModules_obj
    (L : SheafOfModules.{w}
      (TensorSheafification.structureSheaf X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property))
    (hL : IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L) :
    IsInvertible (denseRestrict J X G).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property
      ((denseRestrictModules J X G).obj L) := by
  obtain ⟨N, ⟨e⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.O.obj) (hO := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) L).mp hL
  refine (isInvertible_iff_exists_tensor_iso_unit
    (O := (denseRestrict J X G).O.obj)
    (hO := (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property)
    ((denseRestrictModules J X G).obj L)).mpr ⟨(denseRestrictModules J X G).obj N, ⟨?_⟩⟩
  exact (denseRestrictModulesTensorIso J X G L N).symm ≪≫ (denseRestrictModules J X G).mapIso e

/-- **Restriction to a dense subsite reflects invertibility.** A tensor inverse of the
restriction of `L` is itself the restriction of a sheaf of modules, and that sheaf is a tensor
inverse of `L` because the restriction functor is fully faithful. -/
theorem isInvertible_of_isInvertible_denseRestrictModules_obj
    [(G.sheafPushforwardContinuous AddCommGrpCat.{w} J X.J).IsEquivalence]
    (L : SheafOfModules.{w}
      (TensorSheafification.structureSheaf X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property))
    (h : IsInvertible (denseRestrict J X G).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property
      ((denseRestrictModules J X G).obj L)) :
    IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L := by
  obtain ⟨N₀, ⟨e₀⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := (denseRestrict J X G).O.obj)
    (hO := (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property)
    ((denseRestrictModules J X G).obj L)).mp h
  refine (isInvertible_iff_exists_tensor_iso_unit
    (O := X.O.obj) (hO := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) L).mpr
    ⟨(denseRestrictModules J X G).objPreimage N₀,
      ⟨(denseRestrictModules J X G).preimageIso ?_⟩⟩
  exact denseRestrictModulesTensorIso J X G L ((denseRestrictModules J X G).objPreimage N₀) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor (denseRestrict J X G).O).obj
      ((denseRestrictModules J X G).obj L)).mapIso
        ((denseRestrictModules J X G).objObjPreimageIso N₀) ≪≫ e₀

end Invertible

/-! ### The induced comparison of the categories of invertible modules -/

section InvertibleModules

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{w} J X.J).IsEquivalence]

/-- **Restriction to a dense subsite, on invertible sheaves of modules.** -/
def denseRestrictInvertibleModules :
    InvertibleModules X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ⥤
      InvertibleModules (denseRestrict J X G).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property :=
  ObjectProperty.lift _
    (ObjectProperty.ι (IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) ⋙ denseRestrictModules J X G)
    fun L => isInvertible_denseRestrictModules_obj J X G L.obj L.property

omit [(G.sheafPushforwardContinuous AddCommGrpCat.{w} J X.J).IsEquivalence] in
/-- The sheaf of modules underlying the restriction of an invertible sheaf of modules is the
restriction of the sheaf of modules underlying it. -/
@[simp]
theorem denseRestrictInvertibleModules_obj_obj
    (L : InvertibleModules X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) :
    ((denseRestrictInvertibleModules J X G).obj L).obj =
      (denseRestrictModules J X G).obj L.obj :=
  rfl

/-- Restriction to a dense subsite is faithful on invertible sheaves of modules. -/
instance faithful_denseRestrictInvertibleModules :
    (denseRestrictInvertibleModules J X G).Faithful :=
  inferInstanceAs (ObjectProperty.lift _
    (ObjectProperty.ι (IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) ⋙ denseRestrictModules J X G)
    _).Faithful

/-- Restriction to a dense subsite is full on invertible sheaves of modules. -/
instance full_denseRestrictInvertibleModules : (denseRestrictInvertibleModules J X G).Full :=
  inferInstanceAs (ObjectProperty.lift _
    (ObjectProperty.ι (IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) ⋙ denseRestrictModules J X G)
    _).Full

/-- Restriction to a dense subsite is essentially surjective on invertible sheaves of modules:
a preimage of the underlying sheaf of modules is invertible because restriction reflects
invertibility. -/
instance essSurj_denseRestrictInvertibleModules :
    (denseRestrictInvertibleModules J X G).EssSurj where
  mem_essImage M := by
    have := M.property
    refine ⟨⟨(denseRestrictModules J X G).objPreimage M.obj,
      isInvertible_of_isInvertible_denseRestrictModules_obj J X G _
        (isInvertible_of_iso (denseRestrict J X G).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property
          ((denseRestrictModules J X G).objObjPreimageIso M.obj).symm)⟩,
      ⟨ObjectProperty.isoMk _ ((denseRestrictModules J X G).objObjPreimageIso M.obj)⟩⟩

end InvertibleModules

/-! ### The Picard group -/

section Picard

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{w} J X.J).IsEquivalence]

/-- Restriction to a dense subsite is a bijection on isomorphism classes of invertible sheaves
of modules. -/
def denseRestrictSkeletonEquiv :
    Skeleton (InvertibleModules X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) ≃
      Skeleton (InvertibleModules (denseRestrict J X G).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property) :=
  Equiv.ofBijective (denseRestrictInvertibleModules J X G).mapSkeleton.obj
    ⟨Functor.mapSkeleton_injective _, Functor.mapSkeleton_surjective _⟩

/-- The bijection of Picard groups induced by restriction to a dense subsite: both are the
isomorphism classes of invertible sheaves of modules. -/
def denseRestrictPicardEquiv :
    Picard.PicardGroup X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ≃
      Picard.PicardGroup (denseRestrict J X G).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property :=
  ((Picard.picardGroupData X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).classEquiv.symm.trans
      (denseRestrictSkeletonEquiv J X G)).trans
    (Picard.picardGroupData (denseRestrict J X G).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property).classEquiv

/-- The comparison of Picard groups sends the class of an invertible sheaf of modules to the
class of its restriction. -/
theorem denseRestrictPicardEquiv_classOf
    (L : SheafOfModules.{w}
      (TensorSheafification.structureSheaf X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property))
    (hL : IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L) :
    denseRestrictPicardEquiv J X G (Picard.classOf X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L hL) =
      Picard.classOf (denseRestrict J X G).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property
        ((denseRestrictModules J X G).obj L)
        (isInvertible_denseRestrictModules_obj J X G L hL) := by
  change (Picard.picardGroupData (denseRestrict J X G).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property).classEquiv
        (denseRestrictSkeletonEquiv J X G
          ((Picard.picardGroupData X.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).classEquiv.symm
            ((Picard.picardGroupData X.O.obj
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).classEquiv
              (toSkeleton (C := InvertibleModules X.O.obj
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
                ⟨L, hL⟩)))) = _
  rw [Equiv.symm_apply_apply]
  exact congrArg _ ((denseRestrictInvertibleModules J X G).mapSkeleton_obj_toSkeleton ⟨L, hL⟩)

/-- Restriction to a dense subsite is additive on Picard groups: the addition of either Picard
group is the tensor product sheaf, and restriction commutes with the tensor product sheaf. -/
theorem denseRestrictPicardEquiv_map_add
    (p q : Picard.PicardGroup X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) :
    denseRestrictPicardEquiv J X G (p + q) =
      denseRestrictPicardEquiv J X G p + denseRestrictPicardEquiv J X G q := by
  obtain ⟨L, hL, rfl⟩ := Picard.exists_classOf_eq X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property p
  obtain ⟨N, hN, rfl⟩ := Picard.exists_classOf_eq X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property q
  have := hL
  have := hN
  have := isInvertible_denseRestrictModules_obj J X G L hL
  have := isInvertible_denseRestrictModules_obj J X G N hN
  have hLN := isInvertible_tensorSheaf X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    L N
  have hLN' := isInvertible_tensorSheaf (denseRestrict J X G).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property
    ((denseRestrictModules J X G).obj L) ((denseRestrictModules J X G).obj N)
  rw [Picard.classOf_tensor _ _ L N hL hN hLN, denseRestrictPicardEquiv_classOf J X G _ hLN,
    denseRestrictPicardEquiv_classOf J X G L hL, denseRestrictPicardEquiv_classOf J X G N hN,
    Picard.classOf_tensor _ _ _ _ _ _ hLN']
  exact (Picard.classOf_eq_classOf_iff (denseRestrict J X G).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property _ _ _ hLN').2
    ⟨denseRestrictModulesTensorIso J X G L N⟩

/-- **The Picard group of a ringed site is the Picard group of its restriction to a dense
subsite.** The isomorphism is restriction of sheaves of modules, by
`picardGroupDenseRestrictAddEquiv_classOf`. -/
def picardGroupDenseRestrictAddEquiv :
    Picard.PicardGroup X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ≃+
      Picard.PicardGroup (denseRestrict J X G).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property where
  toEquiv := denseRestrictPicardEquiv J X G
  map_add' := denseRestrictPicardEquiv_map_add J X G

/-- **The comparison of Picard groups is restriction of sheaves of modules**: it sends the class
of an invertible sheaf of modules to the class of its restriction. This pins
`picardGroupDenseRestrictAddEquiv` rather than only asserting that the two Picard groups are
isomorphic. -/
@[simp]
theorem picardGroupDenseRestrictAddEquiv_classOf
    (L : SheafOfModules.{w}
      (TensorSheafification.structureSheaf X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property))
    (hL : IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L) :
    picardGroupDenseRestrictAddEquiv J X G
        (Picard.classOf X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L hL) =
      Picard.classOf (denseRestrict J X G).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (denseRestrict J X G).O).property
        ((denseRestrictModules J X G).obj L)
        (isInvertible_denseRestrictModules_obj J X G L hL) :=
  denseRestrictPicardEquiv_classOf J X G L hL

end Picard

end AlgebraicGeometry.RingedSite

end
