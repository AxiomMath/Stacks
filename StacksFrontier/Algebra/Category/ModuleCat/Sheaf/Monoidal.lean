module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.CategoryTheory.Localization.Monoidal
public import StacksCore.Tactic.StacksAttribute

/-!
# The monoidal structure on sheaves of modules

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)`.  Presheaves of `𝒪`-modules carry the
objectwise tensor product, sheaves of `𝒪`-modules are the localization of presheaves of
`𝒪`-modules at the morphisms sheafification inverts, and the monoidal structure transports along
that localization. Both ring-sheaf presentations use the explicit generic localization
construction: named ordinary data definitions, with monoidal functors assembled by `.toMonoidal`.

## `SheafOfModules` and `Stacks.SheafOfModules.Tensor`: the canonical ring sheaf

Written for `O = Stacks.SheafOfModules.Tensor.ringSheaf R` of a sheaf of commutative rings `R`.
The monoidal structures allow an arbitrary ring and module universe `w`, in particular the
required `max u v w`; the auxiliary instances of the `Stacks.SheafOfModules.Tensor` namespace are
at `R : Sheaf J CommRingCat.{w}` and module universe `w`, with `w` free of the two site universes
(see the implementation notes).  The monoidality of the localizing class is
`PresheafOfModules.isMonoidal_W_inverseImage_toPresheaf`, proved in
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/MonoidalClosed.lean` through the internal hom.

* `SheafOfModules.monoidalCategory`, `SheafOfModules.braidedCategory`,
  `SheafOfModules.symmetricCategory`: the symmetric monoidal structure `⊗_O` on `Mod(O)`.
* `SheafOfModules.sheafification_monoidal`: module sheafification is a monoidal functor, so
  the tensor product of `Mod(O)` is the sheafification of the sectionwise tensor product.
* `Stacks.SheafOfModules.Tensor.hasZeroObject`: the zero sheaf of modules.  The additivity of
  `⊗_O` in each variable, and the existence of the total tensor complexes, are not here: they
  are proved where `⊗_O` itself is defined, in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/BifunctorReductionMachinery.lean`
  (`presheafOfModules_monoidalPreadditive`,
  `Stacks.SheafOfModules.Tensor.sheafTensor_additive`,
  `Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive`,
  `Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor`), which this file imports.

## `Stacks.SheafOfModules`: the `structureSheaf` spelling

Written for `Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪` of a presheaf of
  commutative rings
`𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}` together with a proof that its underlying ring presheaf is a sheaf,
at module universe `w`.  Here the monoidality of the localizing class is Tag 05NA, in the form
proved in `StacksDraft.Ch17.Sec16.Tag05NA`.

* `Stacks.SheafOfModules.localIso` is the localizing class of the sheafification functor.
* `Stacks.SheafOfModules.sheafifyUnitIso` identifies the sheafification of the presheaf tensor
  unit with the sheaf tensor unit `SheafOfModules.unit`.
* `Stacks.SheafOfModules.monoidalCategory` is the monoidal structure on sheaves of modules.
* `Stacks.SheafOfModules.sheafifyTensorIso` is the compatibility isomorphism of sheafification
  with the tensor products, `ℱ^# ⊗ 𝒢^# ≅ (ℱ ⊗ 𝒢)^#`.
* `Stacks.SheafOfModules.braidedCategory` and `Stacks.SheafOfModules.symmetricCategory` are the
  braiding and its symmetry, transported from the presheaf level.
* `Stacks.SheafOfModules.isMonoidal_localIso`: the localizing class is monoidal.  This is the
  content of Tag 05NA that the construction consumes.
* `Stacks.SheafOfModules.tensorUnit_eq`: the tensor unit is `SheafOfModules.unit` on the nose,
  not merely up to isomorphism.
* `Stacks.SheafOfModules.tensorObjIso`: the tensor product of two sheaves of modules is
  canonically the tensor product sheaf from `Stacks.SheafOfModules.Tensor.sheafTensor`,
    the sheafification of the
  objectwise tensor product.

## Implementation notes

Both monoidal structures are produced by localization rather than built by hand, so their
associators and unitors are not given by explicit formulas *here*; what pins the second one down
is `tensorObjIso` together with `sheafifyTensorIso`, which say that the tensor product is the
sheafified presheaf tensor product compatibly with sheafification.  Its tensor unit, by contrast,
is *chosen* in the localization construction, and it is chosen to be `SheafOfModules.unit`, so
`tensorUnit_eq` holds by `rfl`.

The structural morphisms do have sectionwise formulas elsewhere.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections` proves
`associator_hom_val_app_tmul`, `associator_inv_val_app_tmul`, `leftUnitor_hom_val_app_tmul` and
`rightUnitor_hom_val_app_tmul`, which compute each structural morphism on the
sheafification-unit image of a local pure tensor.  The route runs through
`TensorSheafCoherence`, whose `associator_eq_tensorSheafAssociator` conjugates the associator by
the Tag-05NA comparisons `tensorSheafAssocLeft`/`tensorSheafAssocRight`, read **pointwise**
rather than globally, the presheaf associator being objectwise `rfl`.

`monoidalCategory` is an `instance_reducible` definition rather than a global instance in both
namespaces, following Mathlib's `CategoryTheory.Sheaf.monoidalCategory`: a global monoidal
instance on `SheafOfModules` would be found by instance search in every statement about sheaves
of modules, including those where the intended tensor product is a different one.  Downstream
statements should activate it with `attribute [local instance]` or `letI`.

Each development is at a single module universe, equal to the universe of its ring sheaf.  This
is forced, not chosen: Mathlib's monoidal structure on presheaves of modules is stated only for
`PresheafOfModules.{u}` over a ring presheaf of the shape `R ⋙ forget₂ CommRingCat RingCat` with
`R : Cᵒᵖ ⥤ CommRingCat.{u}`, so there is no monoidal structure at the presheaf level to localize
at any other module universe.

That constraint ties the module universe to the *ring* universe and to nothing else, which is
why the auxiliary instances of the `Stacks.SheafOfModules.Tensor` namespace —
`hasZeroObject`, `sheafifyMod_additive`, `presheafTensor_additive`,
`presheafTensor_obj_additive`, `sheafTensor_additive`, `sheafTensor_obj_additive` — are stated
at a module universe `w` free of the two site universes rather than at `max u v`.  They were
originally pinned to `max u v`, which additionally forced the ring universe to dominate both
site universes, and that extra pin is what kept them from firing on a site whose objects lie
above the module universe: for the small étale site of an algebraic space, which is a
`RingedTopos.{u, u + 1, u}`, the structure sheaf is in `CommRingCat.{u}` while
`max (u + 1) u = u + 1`.  Nothing in the proofs needed it — the underlying
`presheafOfModules_monoidalPreadditive` is stated at `C : Type*` with no size condition at all,
and `Stacks.SheafOfModules.Tensor.ringSheaf` is already free in `w` because
`hasSheafCompose_forget₂_ringCat` supplies the `HasSheafCompose` that Mathlib's size-restricted
instances would not.  Freeing the binders is what makes Stacks 06YS,
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize`, applicable there; it
carries these two additivity instances as hypotheses and is otherwise already free in all four
universes.

The site `(C, J)` is an arbitrary site, with `C : Type u` and `Category.{v} C`; nothing here is
special to the site of opens of a topological space.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

universe v u w

section LocalIsomorphisms
open CategoryTheory MonoidalCategory

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The class of morphisms of presheaves of `𝒪`-modules which sheafification inverts: the
local isomorphisms, i.e. the morphisms which are locally injective and locally surjective. This
is the localizing class of the sheafification functor. -/
abbrev localIso : MorphismProperty (PresheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)) :=
  J.W.inverseImage (PresheafOfModules.toPresheaf
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The local isomorphisms are stable under tensoring on the left. This is Tag 05NA's
`W_whiskerRight` moved across the braiding of presheaves of modules. -/
theorem localIso_whiskerLeft
    (X : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
    {A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      𝒪)} (f : A ⟶ B)
    (hf : localIso (J := J) 𝒪 f) :
    localIso (J := J) 𝒪 (X ◁ f) :=
  ((localIso (J := J) 𝒪).arrow_mk_iso_iff
      (Arrow.isoMk (β_ X A) (β_ X B) (by simp)) :
    localIso (J := J) 𝒪 (X ◁ f) ↔ localIso (J := J) 𝒪 (f ▷ X)).2
    (Stacks.SheafOfModules.TensorSheafification.W_whiskerRight 𝒪 f X hf)

/-- The class of morphisms inverted by sheafification is a monoidal class of morphisms: it is
multiplicative and stable under whiskering on both sides. This is Tag 05NA, and it is the
hypothesis under which the monoidal structure descends to the localization. -/
instance isMonoidal_localIso : (localIso (J := J) 𝒪).IsMonoidal where
  whiskerLeft X _ _ f hf := localIso_whiskerLeft 𝒪 X f hf
  whiskerRight f hf Y := Stacks.SheafOfModules.TensorSheafification.W_whiskerRight 𝒪 f Y hf

end Stacks.SheafOfModules

end LocalIsomorphisms

section RingSheafSpelling
open CategoryTheory Opposite MonoidalCategory Limits Localization.Monoidal

noncomputable section

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable (R : Sheaf J CommRingCat.{w})
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The monoidal category structure on sheaves of modules.** -/
@[instance_reducible]
def monoidalCategory :
    MonoidalCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  letI : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := R.obj)
  Localization.monoidalCategory
    (monoidalLocalIsomorphisms :=
      Stacks.SheafOfModules.isMonoidal_localIso (𝒪 := R.obj))
    (PresheafOfModules.sheafification
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
    (J.W.inverseImage (PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) (Iso.refl _)

attribute [local instance] monoidalCategory

/-- The monoidal structure on sheaves of modules is braided. -/
@[instance_reducible]
def braidedCategory :
    BraidedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  letI : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := R.obj)
  Localization.braidedCategory
    (monoidalLocalIsomorphisms :=
      Stacks.SheafOfModules.isMonoidal_localIso (𝒪 := R.obj))
    (sourceBraided := (PresheafOfModulesOfCommRing.symmetricCategory (R := R.obj)).toBraidedCategory)
    (PresheafOfModules.sheafification
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
    (J.W.inverseImage (PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) (Iso.refl _)

/-- The monoidal structure on sheaves of modules is symmetric. -/
@[instance_reducible]
def symmetricCategory :
    SymmetricCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  letI : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := R.obj)
  Localization.symmetricCategory
    (monoidalLocalIsomorphisms :=
      Stacks.SheafOfModules.isMonoidal_localIso (𝒪 := R.obj))
    (sourceSymmetric := PresheafOfModulesOfCommRing.symmetricCategory (R := R.obj))
    (PresheafOfModules.sheafification
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
    (J.W.inverseImage (PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) (Iso.refl _)

/-- Module sheafification is a monoidal functor. -/
instance sheafification_monoidal :
    letI : MonoidalCategory
        (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :=
      PresheafOfModulesOfCommRing.monoidalCategory (R := R.obj)
    (PresheafOfModules.sheafification
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).Monoidal :=
  letI : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := R.obj)
  (Localization.coreMonoidal
    (monoidalLocalIsomorphisms :=
      Stacks.SheafOfModules.isMonoidal_localIso (𝒪 := R.obj))
    (PresheafOfModules.sheafification
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
    (J.W.inverseImage (PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) (Iso.refl _)).toMonoidal

end SheafOfModules

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- `Mod(O)` has a zero object (the zero sheaf of modules): it is preadditive, hence has zero
morphisms, and it has a terminal object.

Nothing about this is localized along sheafification, so the universe `w` of the sections is
free. The additivity of `⊗_O`, which is pinned to `max u v` by Mathlib's monoidal structure on
presheaves of modules, is not here: it lives beside `⊗_O` itself in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/BifunctorReductionMachinery.lean`. -/
instance hasZeroObject : HasZeroObject (SheafOfModules.{w} (ringSheaf R)) :=
  hasZeroObject_of_hasTerminal_object

end Stacks.SheafOfModules.Tensor
end

end RingSheafSpelling

section StructureSheafSpelling
open CategoryTheory MonoidalCategory Localization

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Sheafification of presheaves of modules, with its source spelled over the ring presheaf
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf` rather than over
  `(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj`. The
two are definitionally equal, but Mathlib's monoidal structure on presheaves of modules is
indexed by a ring presheaf of the shape `𝒪 ⋙ forget₂ CommRingCat RingCat`, and instance search
does not unfold the structure sheaf to see that shape. -/
@[sga "4 IV 12.4" "A-module structure on aM"]
noncomputable abbrev sheafifyFunctor :
    PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) :=
  Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪

/-- Sheafification of presheaves of modules is the localization functor at the local
isomorphisms. -/
instance isLocalization_sheafify :
    (sheafifyFunctor 𝒪 h𝒪).IsLocalization (localIso (J := J) 𝒪) :=
  show ((PresheafOfModules.sheafification.{w}
    (R₀ := (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)
    (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)
    (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).IsLocalization
      (J.W.inverseImage
        (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
          h𝒪).obj))) from inferInstance

/-- The sheafification of a sheaf of modules is itself: the counit of the sheafification
adjunction is an isomorphism, because sheaves of modules form a reflective subcategory. -/
noncomputable def sheafifyValIso (F : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (sheafifyFunctor 𝒪 h𝒪).obj F.val ≅ F :=
  (asIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).counit).app F

/-- The sheafification of the presheaf tensor unit is the tensor unit `SheafOfModules.unit`.
The presheaf tensor unit is the structure sheaf viewed as a module over itself, which is already
a sheaf, so this is an instance of `sheafifyValIso`. -/
noncomputable def sheafifyUnitIso :
    (sheafifyFunctor 𝒪 h𝒪).obj
        (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
          𝒪))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) :=
  sheafifyValIso 𝒪 h𝒪 (SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))

/-- The monoidal structure on sheaves of `𝒪`-modules, obtained by
localizing the monoidal structure on presheaves of `𝒪`-modules along sheafification. Its tensor
product is the sheafification of the objectwise tensor product and its unit is
`SheafOfModules.unit`. -/
@[instance_reducible]
noncomputable def monoidalCategory :
    MonoidalCategory (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      𝒪 h𝒪)) :=
  Localization.monoidalCategory (sheafifyFunctor 𝒪 h𝒪) (localIso (J := J) 𝒪)
    (sheafifyUnitIso 𝒪 h𝒪)

attribute [local instance] monoidalCategory

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The tensor unit of `monoidalCategory` is `SheafOfModules.unit`, not merely isomorphic to
it: the unit object is a parameter of the localization construction and is chosen to be that
sheaf. -/
theorem tensorUnit_eq :
    𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) =
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) :=
  rfl

/-- Sheafification is compatible with the tensor products: the tensor product of two sheafified
presheaves of modules is the sheafification of their presheaf tensor product. -/
noncomputable def sheafifyTensorIso
    (P Q : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      𝒪)) :
    (sheafifyFunctor 𝒪 h𝒪).obj P ⊗ (sheafifyFunctor 𝒪 h𝒪).obj Q ≅
      (sheafifyFunctor 𝒪 h𝒪).obj (P ⊗ Q) :=
  Monoidal.μ (sheafifyFunctor 𝒪 h𝒪) (localIso (J := J) 𝒪) (sheafifyUnitIso 𝒪 h𝒪) P Q

/-- The tensor product of two sheaves of modules is the tensor product sheaf of Tag 01CA: the
sheafification of their objectwise tensor product. -/
noncomputable def tensorObjIso
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    F ⊗ G ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj G :=
  ((sheafifyValIso 𝒪 h𝒪 F).symm ⊗ᵢ (sheafifyValIso 𝒪 h𝒪 G).symm) ≪≫
    sheafifyTensorIso 𝒪 h𝒪 F.val G.val

/-- The braiding on sheaves of modules, transported from the braiding of presheaves of
modules. -/
@[instance_reducible]
noncomputable def braidedCategory :
    BraidedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) :=
  Localization.braidedCategory (sheafifyFunctor 𝒪 h𝒪) (localIso (J := J) 𝒪)
    (sheafifyUnitIso 𝒪 h𝒪)

/-- The tensor product of sheaves of modules is symmetric. -/
@[instance_reducible]
noncomputable def symmetricCategory :
    letI := braidedCategory 𝒪 h𝒪
    SymmetricCategory (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      𝒪 h𝒪)) :=
  Localization.symmetricCategory (sheafifyFunctor 𝒪 h𝒪) (localIso (J := J) 𝒪)
    (sheafifyUnitIso 𝒪 h𝒪)

end Stacks.SheafOfModules

end StructureSheafSpelling

end
