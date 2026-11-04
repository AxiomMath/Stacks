module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback.ModuleTransport
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# Inverse images of sheaves of modules

Let `f : Sh(C) → Sh(D)` be a morphism of topoi and let `O` be a sheaf of rings on `D`. The
inverse image `f⁻¹` is left exact, so it preserves finite products; transporting the ring and
module operations across the product comparison isomorphisms equips `f⁻¹O` with a sheaf of rings
structure and every `f⁻¹G` with a module structure over it, functorially in `G`.

## Main definitions

* `CategoryTheory.Functor.prodObjEquiv`, `prodObjMk`: for a functor `P` to types preserving
  finite products, the identification of `P (A ⨯ B)` with `P A × P B`, and the element of
  `P (A ⨯ B)` determined by a pair of elements of `P A` and `P B`. These are the element
  calculus on which everything else rests.
* `CategoryTheory.Sheaf.sectionsFunctor`: sections of a sheaf of types over a fixed object, as a
  finite-product-preserving functor.
* `CategoryTheory.Sheaf.binaryOpHom`, `unaryOpHom`, `constHom`: morphisms of sheaves of types
  given by natural pointwise operations on sections.
* `CategoryTheory.Sheaf.ringAddHom`, `ringMulHom`, `ringNegHom`, `ringZeroHom`, `ringOneHom`,
  `moduleAddHom`, `moduleNegHom`, `moduleZeroHom`, `moduleSMulHom`: the algebraic operations of a
  sheaf of rings and of a sheaf of modules, read off on underlying sheaves of sets.
* `CategoryTheory.Sheaf.ringObjRing`, `moduleObjAddCommGroup`, `moduleObjModule`: the ring,
  additive group and module structures transported along a finite-product-preserving functor to
  types.
* `Stacks.Sheaves.ToposPullback.pullbackRingSheaf`, `pullbackModuleObj`,
  `pullbackModuleFunctor`: the inverse-image sheaf of rings, the inverse image of a sheaf of
  modules, and the induced functor.
* `Stacks.Sheaves.ToposPullback.PullbackModuleData`: the inverse-image ring, the functor on
  modules, and their identifications with inverse images of underlying sheaves, compatible with
  all operations.

## Main results

* `Stacks.Sheaves.ToposPullback.pullbackModule`: inverse image along a morphism of topoi equips
  the inverse image of every sheaf of `O`-modules with a module structure over the inverse-image
  sheaf of rings, functorially in the module.
* `CategoryTheory.Presheaf.isSheaf_ringCat_of_isSheaf_forget`: a presheaf of rings whose
  underlying presheaf of types is a sheaf is a sheaf.

## Implementation notes

The source describes the scalar multiplication map and then observes functoriality. Both are
packaged as a functor to Mathlib's category `SheafOfModules`; `PullbackModuleData.action` exposes
the resulting map of underlying sheaves of sets. The fields `ringAdd_map`, `ringMul_map`,
`ringNeg_map`, `ringZero_map` and `ringOne_map` specify the inverse-image ring operations, the
fields `moduleAdd_map`, `moduleNeg_map` and `moduleZero_map` the inverse-image abelian group
structure, and `action_map` identifies scalar multiplication with the inverse image of the
original scalar multiplication. All these equations use the canonical product or terminal
comparison, so the identifications preserve the transported algebraic structures, not just their
underlying sets. The natural isomorphism `moduleIso` also specifies the inverse image of every
module morphism.

Mathlib has no notion of a module object over a ring object in a category with finite products,
no transport of `RingObj` along a product-preserving functor, and `SheafOfModules.pullback` only
for a continuous functor of sites between small sites whose rings live in the same universe. None
of that applies to an abstract morphism of topoi, so the construction here is carried out with a
bare-hands element calculus for finite-product-preserving functors to types: `prodObjMk` and its
computation rules reduce every operation and every axiom to a statement about sections, which is
then transported by applying the functor to a single identity between morphisms of sheaves.

`CategoryTheory.Presheaf.isSheaf_ringCat_of_isSheaf_forget` is proved from separatedness rather
than from Mathlib's `Presheaf.isSheaf_iff_isSheaf_forget`, which would require
`ReflectsLimitsOfSize (forget RingCat.{w})` and hence a size condition relating the universe of
the rings to the universes of the site. No such condition is assumed here, so no universe is
narrowed.

`CategoryTheory.Sheaf.sectionsFunctor` is deliberately a `def` rather than an `abbrev`: all the
computation rules are stated in terms of it and would not match syntactically if it unfolded.

The ring and module sections lie in the universe of their respective topos of sets; the section,
object and morphism universes of the two sites remain independent. This places the scalar
multiplication and both its factors in the domain of the same inverse-image functor, as in the
source's proof. No extension of a given morphism of topoi to a different universe is asserted.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public section

/-! ## The inverse image of a sheaf of rings along a left-exact functor -/

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory Limits Sheaf Functor Opposite

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'})

/-- The inverse-image presheaf of rings: its sections over `X` are the sections over `X` of the
inverse image of the underlying sheaf of sets of `O`, with the ring structure transported along
the (left exact, hence finite-product-preserving) inverse-image functor. -/
@[sga "3 I 2.2" "special case"]
noncomputable def pullbackRingPresheaf : Cᵒᵖ ⥤ RingCat.{ww} where
  obj X :=
    letI := ringObjRing O (Φ ⋙ sectionsFunctor J X)
    RingCat.of ((Φ ⋙ sectionsFunctor J X).obj (ringSheaf O))
  map {X Y} g :=
    letI := ringObjRing O (Φ ⋙ sectionsFunctor J X)
    letI := ringObjRing O (Φ ⋙ sectionsFunctor J Y)
    RingCat.ofHom (ringObjHom O (whiskerLeft Φ (sectionsRestrict g)))
  map_id X := by
    refine RingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    change (Φ.obj (ringSheaf O)).obj.map (𝟙 X) x = x
    exact (Φ.obj (ringSheaf O)).obj.map_id_apply X x
  map_comp {X Y Z} g h := by
    refine RingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    change (Φ.obj (ringSheaf O)).obj.map (g ≫ h) x =
      (Φ.obj (ringSheaf O)).obj.map h ((Φ.obj (ringSheaf O)).obj.map g x)
    exact (Φ.obj (ringSheaf O)).obj.map_comp_apply g h x

/-- The inverse image of a sheaf of rings along a finite-product-preserving functor between
categories of sheaves of sets. Its underlying sheaf of sets is the inverse image of the
underlying sheaf of sets of `O`. -/
noncomputable def pullbackRingSheaf : Sheaf J RingCat.{ww} :=
  ⟨pullbackRingPresheaf J Φ O,
    Presheaf.isSheaf_ringCat_of_isSheaf_forget _ (Φ.obj (ringSheaf O)).property⟩

/-- The underlying sheaf of sets of the inverse-image sheaf of rings is, on the nose, the
inverse image of the underlying sheaf of sets of `O`. -/
noncomputable def pullbackRingSheafIso :
    ringSheaf (pullbackRingSheaf J Φ O) ≅ Φ.obj (ringSheaf O) := Iso.refl _

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})] in
/-- Decoration by identity morphisms, as it appears in the compatibility equations. -/
lemma prodMap_id_comp {A B E : Sheaf J (Type ww)} (n : A ⨯ B ⟶ E) :
    Limits.prod.map (𝟙 A) (𝟙 B) ≫ n ≫ 𝟙 E = n := by
  rw [Limits.prod.map_id_id, Category.id_comp, Category.comp_id]

end Stacks.Sheaves.ToposPullback

/-! ## The inverse image of a sheaf of modules -/

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory Limits Sheaf Functor Opposite

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'})

/-- The inverse-image presheaf of abelian groups of a sheaf of modules. -/
noncomputable def pullbackModuleAb (G : SheafOfModules.{ww'} O) : Cᵒᵖ ⥤ AddCommGrpCat.{ww} :=
  letI : ∀ X : Cᵒᵖ, AddCommGroup ((Φ ⋙ sectionsFunctor J X).obj (moduleSheaf O G)) := fun X ↦
    moduleObjAddCommGroup O G (Φ ⋙ sectionsFunctor J X)
  { obj := fun X ↦ AddCommGrpCat.of ((Φ ⋙ sectionsFunctor J X).obj (moduleSheaf O G))
    map := fun {X Y} g ↦
      AddCommGrpCat.ofHom (moduleObjHom O G (whiskerLeft Φ (sectionsRestrict g)))
    map_id := fun X ↦ by
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ ?_)
      change (Φ.obj (moduleSheaf O G)).obj.map (𝟙 X) x = x
      exact (Φ.obj (moduleSheaf O G)).obj.map_id_apply X x
    map_comp := fun {X Y Z} g h ↦ by
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ ?_)
      change (Φ.obj (moduleSheaf O G)).obj.map (g ≫ h) x =
        (Φ.obj (moduleSheaf O G)).obj.map h ((Φ.obj (moduleSheaf O G)).obj.map g x)
      exact (Φ.obj (moduleSheaf O G)).obj.map_comp_apply g h x }

/-- The inverse image of a sheaf of modules, as a presheaf of modules over the inverse-image
presheaf of rings. -/
noncomputable def pullbackModuleVal (G : SheafOfModules.{ww'} O) :
    PresheafOfModules.{ww} (pullbackRingSheaf J Φ O).obj :=
  letI : ∀ X : Cᵒᵖ, Module ((pullbackRingSheaf J Φ O).obj.obj X)
      ((pullbackModuleAb J Φ O G).obj X) := fun X ↦
    moduleObjModule O G (Φ ⋙ sectionsFunctor J X)
  PresheafOfModules.ofPresheaf (pullbackModuleAb J Φ O G)
    (fun {X Y} g r m ↦ by
      exact moduleSMulObj_naturality O G (whiskerLeft Φ (sectionsRestrict g)) r m)

/-- The inverse image of a sheaf of `O`-modules, as a sheaf of modules over the inverse-image sheaf
of rings. -/
noncomputable def pullbackModuleObj (G : SheafOfModules.{ww'} O) :
    SheafOfModules.{ww} (pullbackRingSheaf J Φ O) where
  val := pullbackModuleVal J Φ O G
  isSheaf := Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{ww})
    (Φ.obj (moduleSheaf O G)).property

variable {G G' : SheafOfModules.{ww'} O}

/-- The inverse image of a morphism of sheaves of modules. -/
noncomputable def pullbackModuleMap (φ : G ⟶ G') :
    pullbackModuleObj J Φ O G ⟶ pullbackModuleObj J Φ O G' where
  val :=
    letI : ∀ X : Cᵒᵖ, AddCommGroup ((Φ ⋙ sectionsFunctor J X).obj (moduleSheaf O G)) := fun X ↦
      moduleObjAddCommGroup O G (Φ ⋙ sectionsFunctor J X)
    letI : ∀ X : Cᵒᵖ, AddCommGroup ((Φ ⋙ sectionsFunctor J X).obj (moduleSheaf O G')) := fun X ↦
      moduleObjAddCommGroup O G' (Φ ⋙ sectionsFunctor J X)
    PresheafOfModules.homMk
      { app := fun X ↦ AddCommGrpCat.ofHom
          { toFun := (Φ ⋙ sectionsFunctor J X).map ((moduleSheafFunctor O).map φ)
            map_zero' := map_moduleSheafFunctor_map_zeroObj O
              (P := Φ ⋙ sectionsFunctor J X) (φ := φ)
            map_add' := map_moduleSheafFunctor_map_addObj O
              (P := Φ ⋙ sectionsFunctor J X) (φ := φ) }
        naturality := fun X Y g ↦ by
          refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ ?_)
          exact (natTrans_app_map_apply (whiskerLeft Φ (sectionsRestrict g))
            ((moduleSheafFunctor O).map φ) x).symm }
      (fun X r m ↦ map_moduleSheafFunctor_map_smulObj O
        (P := Φ ⋙ sectionsFunctor J X) (φ := φ) r m)

omit [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- On sections over `X`, `pullbackModuleMap J Φ O φ` is the image under `Φ` of the morphism of
underlying sheaves of types of `φ`. -/
@[simp]
lemma pullbackModuleMap_val_app_apply (φ : G ⟶ G') (X : Cᵒᵖ)
    (x : (pullbackModuleObj J Φ O G).val.obj X) :
    ((pullbackModuleMap J Φ O φ).val.app X).hom x =
      (Φ ⋙ sectionsFunctor J X).map ((moduleSheafFunctor O).map φ) x := rfl

/-- Inverse image along a finite-product-preserving functor between categories of sheaves of sets,
as a functor from sheaves of `O`-modules to sheaves of modules over the inverse-image sheaf of
rings. -/
noncomputable def pullbackModuleFunctor :
    SheafOfModules.{ww'} O ⥤ SheafOfModules.{ww} (pullbackRingSheaf J Φ O) where
  obj G := pullbackModuleObj J Φ O G
  map φ := pullbackModuleMap J Φ O φ
  map_id G := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun X ↦ ?_))
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    refine (pullbackModuleMap_val_app_apply J Φ O (𝟙 G) X x).trans ?_
    rw [(moduleSheafFunctor O).map_id G]
    exact (Φ ⋙ sectionsFunctor J X).map_id_apply _ x
  map_comp {G₁ G₂ G₃} φ ψ := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun X ↦ ?_))
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    refine (pullbackModuleMap_val_app_apply J Φ O (φ ≫ ψ) X x).trans ?_
    rw [(moduleSheafFunctor O).map_comp φ ψ]
    exact (Φ ⋙ sectionsFunctor J X).map_comp_apply _ _ x

end Stacks.Sheaves.ToposPullback

/-! ## Compatibility of the inverse image with the algebraic operations -/

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory Limits Sheaf Functor Opposite

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'})

/-- A binary operation `f` and its transport `g` along `Φ` are related by the product comparison
as soon as `g` agrees with `f` on pairs of sections. -/
private theorem map_eq_prodComparison_comp {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww))
    [PreservesFiniteProducts Φ] {A B E : Sheaf K (Type ww')} (f : A ⨯ B ⟶ E)
    (g : Φ.obj A ⨯ Φ.obj B ⟶ Φ.obj E)
    (h : ∀ (X : Cᵒᵖ) (a : (sectionsFunctor J X).obj (Φ.obj A))
      (b : (sectionsFunctor J X).obj (Φ.obj B)),
      (sectionsFunctor J X).map g (prodObjMk (P := sectionsFunctor J X) (A := Φ.obj A)
          (B := Φ.obj B) a b) =
        (Φ ⋙ sectionsFunctor J X).map f
          (prodObjMk (P := Φ ⋙ sectionsFunctor J X) (A := A) (B := B) a b)) :
    Φ.map f = Limits.prodComparison Φ A B ≫ g := by
  refine hom_ext_sections (fun X p ↦ ?_)
  change (Φ ⋙ sectionsFunctor J X).map f p =
    (sectionsFunctor J X).map g ((sectionsFunctor J X).map (Limits.prodComparison Φ A B) p)
  rw [CategoryTheory.Functor.map_prodComparison_apply, h,
    CategoryTheory.Functor.prodObjMk_map_fst_map_snd]

/-- A nullary operation `f` and its transport `g` along `Φ` are related by the terminal
comparison as soon as `g` takes the value `f` at the unique section. -/
private theorem map_eq_terminalComparison_comp {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww))
    [PreservesFiniteProducts Φ] {E : Sheaf K (Type ww')} (f : ⊤_ _ ⟶ E)
    (g : ⊤_ (Sheaf J (Type ww)) ⟶ Φ.obj E)
    (h : ∀ (X : Cᵒᵖ) (p : (sectionsFunctor J X).obj (⊤_ (Sheaf J (Type ww)))),
      (sectionsFunctor J X).map g p = (Φ ⋙ sectionsFunctor J X).map f default) :
    Φ.map f = Limits.terminalComparison Φ ≫ g := by
  refine hom_ext_sections (fun X p ↦ ?_)
  change (Φ ⋙ sectionsFunctor J X).map f p =
    (sectionsFunctor J X).map g ((sectionsFunctor J X).map (Limits.terminalComparison Φ) p)
  rw [h]
  exact congrArg ((Φ ⋙ sectionsFunctor J X).map f)
    (Subsingleton.elim (α := (Φ ⋙ sectionsFunctor J X).obj (⊤_ (Sheaf K (Type ww')))) p default)

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- On sections over `X`, the addition of `pullbackRingSheaf J Φ O` is the image under `Φ` of
the addition of `O`. -/
lemma ringAddHom_pullback_apply (X : Cᵒᵖ)
    (a b : (sectionsFunctor J X).obj (Φ.obj (ringSheaf O))) :
    (sectionsFunctor J X).map (ringAddHom (pullbackRingSheaf J Φ O))
        (prodObjMk (P := sectionsFunctor J X) (A := Φ.obj (ringSheaf O))
          (B := Φ.obj (ringSheaf O)) a b) =
      (Φ ⋙ sectionsFunctor J X).map (ringAddHom O)
        (prodObjMk (P := Φ ⋙ sectionsFunctor J X) (A := ringSheaf O) (B := ringSheaf O) a b) :=
  sectionsFunctor_map_ringAddHom (pullbackRingSheaf J Φ O) X a b

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The image under `Φ` of the addition of `O` is the product comparison of `Φ` followed by the
addition of `pullbackRingSheaf J Φ O`. -/
lemma ringAdd_map_aux' :
    Φ.map (ringAddHom O) =
      Limits.prodComparison Φ (ringSheaf O) (ringSheaf O) ≫
        ringAddHom (pullbackRingSheaf J Φ O) :=
  map_eq_prodComparison_comp Φ _ _ (ringAddHom_pullback_apply J Φ O)

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The image under `Φ` of the addition of `O` is the product comparison of `Φ` followed by the
addition of `pullbackRingSheaf J Φ O`, with identity morphisms inserted on either side. -/
lemma ringAdd_map_aux :
    Φ.map (ringAddHom O) =
      Limits.prodComparison Φ (ringSheaf O) (ringSheaf O) ≫
        Limits.prod.map (𝟙 (ringSheaf (pullbackRingSheaf J Φ O)))
            (𝟙 (ringSheaf (pullbackRingSheaf J Φ O))) ≫
          ringAddHom (pullbackRingSheaf J Φ O) ≫ 𝟙 _ :=
  (ringAdd_map_aux' J Φ O).trans
    (congrArg (fun m ↦ Limits.prodComparison Φ (ringSheaf O) (ringSheaf O) ≫ m)
      (prodMap_id_comp J (ringAddHom (pullbackRingSheaf J Φ O))).symm)

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- On sections over `X`, the multiplication of `pullbackRingSheaf J Φ O` is the image under `Φ`
of the multiplication of `O`. -/
lemma ringMulHom_pullback_apply (X : Cᵒᵖ)
    (a b : (sectionsFunctor J X).obj (Φ.obj (ringSheaf O))) :
    (sectionsFunctor J X).map (ringMulHom (pullbackRingSheaf J Φ O))
        (prodObjMk (P := sectionsFunctor J X) (A := Φ.obj (ringSheaf O))
          (B := Φ.obj (ringSheaf O)) a b) =
      (Φ ⋙ sectionsFunctor J X).map (ringMulHom O)
        (prodObjMk (P := Φ ⋙ sectionsFunctor J X) (A := ringSheaf O) (B := ringSheaf O) a b) :=
  sectionsFunctor_map_ringMulHom (pullbackRingSheaf J Φ O) X a b

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The image under `Φ` of the multiplication of `O` is the product comparison of `Φ` followed by
the multiplication of `pullbackRingSheaf J Φ O`. -/
lemma ringMul_map_aux' :
    Φ.map (ringMulHom O) =
      Limits.prodComparison Φ (ringSheaf O) (ringSheaf O) ≫
        ringMulHom (pullbackRingSheaf J Φ O) :=
  map_eq_prodComparison_comp Φ _ _ (ringMulHom_pullback_apply J Φ O)

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The image under `Φ` of the multiplication of `O` is the product comparison of `Φ` followed by
the multiplication of `pullbackRingSheaf J Φ O`, with identity morphisms inserted on either
side. -/
lemma ringMul_map_aux :
    Φ.map (ringMulHom O) =
      Limits.prodComparison Φ (ringSheaf O) (ringSheaf O) ≫
        Limits.prod.map (𝟙 (ringSheaf (pullbackRingSheaf J Φ O)))
            (𝟙 (ringSheaf (pullbackRingSheaf J Φ O))) ≫
          ringMulHom (pullbackRingSheaf J Φ O) ≫ 𝟙 _ :=
  (ringMul_map_aux' J Φ O).trans
    (congrArg (fun m ↦ Limits.prodComparison Φ (ringSheaf O) (ringSheaf O) ≫ m)
      (prodMap_id_comp J (ringMulHom (pullbackRingSheaf J Φ O))).symm)

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The image under `Φ` of the negation of `O` is the negation of `pullbackRingSheaf J Φ O`, with
identity morphisms inserted on either side. -/
lemma ringNeg_map_aux :
    Φ.map (ringNegHom O) =
      𝟙 (Φ.obj (ringSheaf O)) ≫ ringNegHom (pullbackRingSheaf J Φ O) ≫ 𝟙 _ := by
  refine hom_ext_sections (fun X p ↦ ?_)
  show (Φ ⋙ sectionsFunctor J X).map (ringNegHom O) p =
    (sectionsFunctor J X).map (ringNegHom (pullbackRingSheaf J Φ O)) p
  exact (sectionsFunctor_map_ringNegHom (pullbackRingSheaf J Φ O) X p).symm

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The image under `Φ` of the zero section of `O` is the terminal comparison of `Φ` followed by
the zero section of `pullbackRingSheaf J Φ O`. -/
lemma ringZero_map_aux :
    Φ.map (ringZeroHom O) =
      Limits.terminalComparison Φ ≫ ringZeroHom (pullbackRingSheaf J Φ O) ≫ 𝟙 _ := by
  rw [Category.comp_id]
  exact map_eq_terminalComparison_comp Φ _ _ fun X p ↦ sectionsFunctor_map_ringZeroHom _ X p

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The image under `Φ` of the unit section of `O` is the terminal comparison of `Φ` followed by
the unit section of `pullbackRingSheaf J Φ O`. -/
lemma ringOne_map_aux :
    Φ.map (ringOneHom O) =
      Limits.terminalComparison Φ ≫ ringOneHom (pullbackRingSheaf J Φ O) ≫ 𝟙 _ := by
  rw [Category.comp_id]
  exact map_eq_terminalComparison_comp Φ _ _ fun X p ↦ sectionsFunctor_map_ringOneHom _ X p

variable (G : SheafOfModules.{ww'} O)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- On sections over `X`, the addition of `pullbackModuleObj J Φ O G` is the image under `Φ` of
the addition of `G`. -/
lemma moduleAddHom_pullback_apply (X : Cᵒᵖ)
    (a b : (sectionsFunctor J X).obj (Φ.obj (moduleSheaf O G))) :
    (sectionsFunctor J X).map
        (moduleAddHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))
        (prodObjMk (P := sectionsFunctor J X) (A := Φ.obj (moduleSheaf O G))
          (B := Φ.obj (moduleSheaf O G)) a b) =
      (Φ ⋙ sectionsFunctor J X).map (moduleAddHom O G)
        (prodObjMk (P := Φ ⋙ sectionsFunctor J X) (A := moduleSheaf O G)
          (B := moduleSheaf O G) a b) :=
  sectionsFunctor_map_moduleAddHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) X a b

/-- On sections over `X`, the scalar multiplication of `pullbackModuleObj J Φ O G` is the image
under `Φ` of the scalar multiplication of `G`. -/
lemma moduleSMulHom_pullback_apply (X : Cᵒᵖ)
    (r : (sectionsFunctor J X).obj (Φ.obj (ringSheaf O)))
    (m : (sectionsFunctor J X).obj (Φ.obj (moduleSheaf O G))) :
    (sectionsFunctor J X).map
        (moduleSMulHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))
        (prodObjMk (P := sectionsFunctor J X) (A := Φ.obj (ringSheaf O))
          (B := Φ.obj (moduleSheaf O G)) r m) =
      (Φ ⋙ sectionsFunctor J X).map (moduleSMulHom O G)
        (prodObjMk (P := Φ ⋙ sectionsFunctor J X) (A := ringSheaf O)
          (B := moduleSheaf O G) r m) :=
  sectionsFunctor_map_moduleSMulHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) X r m

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The image under `Φ` of the addition of `G` is the product comparison of `Φ` followed by the
addition of `pullbackModuleObj J Φ O G`. -/
lemma moduleAdd_map_aux' :
    Φ.map (moduleAddHom O G) =
      Limits.prodComparison Φ (moduleSheaf O G) (moduleSheaf O G) ≫
        moduleAddHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) :=
  map_eq_prodComparison_comp Φ _ _ (moduleAddHom_pullback_apply J Φ O G)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The image under `Φ` of the negation of `G` is the negation of `pullbackModuleObj J Φ O G`. -/
lemma moduleNeg_map_aux :
    Φ.map (moduleNegHom O G) =
      moduleNegHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) := by
  refine hom_ext_sections (fun X p ↦ ?_)
  show (Φ ⋙ sectionsFunctor J X).map (moduleNegHom O G) p =
    (sectionsFunctor J X).map
      (moduleNegHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G)) p
  exact (sectionsFunctor_map_moduleNegHom (pullbackRingSheaf J Φ O)
    (pullbackModuleObj J Φ O G) X p).symm

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The image under `Φ` of the zero section of `G` is the terminal comparison of `Φ` followed by
the zero section of `pullbackModuleObj J Φ O G`. -/
lemma moduleZero_map_aux :
    Φ.map (moduleZeroHom O G) =
      Limits.terminalComparison Φ ≫
        moduleZeroHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) :=
  map_eq_terminalComparison_comp Φ _ _ fun X p ↦ sectionsFunctor_map_moduleZeroHom _ _ X p

/-- The image under `Φ` of the scalar multiplication of `G` is the product comparison of `Φ`
followed by the scalar multiplication of `pullbackModuleObj J Φ O G`. -/
lemma moduleSMul_map_aux' :
    Φ.map (moduleSMulHom O G) =
      Limits.prodComparison Φ (ringSheaf O) (moduleSheaf O G) ≫
        moduleSMulHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) :=
  map_eq_prodComparison_comp Φ _ _ (moduleSMulHom_pullback_apply J Φ O G)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The image under `Φ` of the addition of `G` is the product comparison of `Φ` followed by the
addition of `pullbackModuleObj J Φ O G`, with identity morphisms inserted on either side. -/
lemma moduleAdd_map_aux :
    Φ.map (moduleAddHom O G) =
      Limits.prodComparison Φ (moduleSheaf O G) (moduleSheaf O G) ≫
        Limits.prod.map (𝟙 (moduleSheaf (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G)))
            (𝟙 (moduleSheaf (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))) ≫
          moduleAddHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) ≫ 𝟙 _ :=
  (moduleAdd_map_aux' J Φ O G).trans
    (congrArg (fun m ↦ Limits.prodComparison Φ (moduleSheaf O G) (moduleSheaf O G) ≫ m)
      (prodMap_id_comp J
        (moduleAddHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))).symm)

/-- The image under `Φ` of the scalar multiplication of `G` is the product comparison of `Φ`
followed by the scalar multiplication of `pullbackModuleObj J Φ O G`, with identity morphisms
inserted on either side. -/
lemma moduleSMul_map_aux :
    Φ.map (moduleSMulHom O G) =
      Limits.prodComparison Φ (ringSheaf O) (moduleSheaf O G) ≫
        Limits.prod.map (𝟙 (ringSheaf (pullbackRingSheaf J Φ O)))
            (𝟙 (moduleSheaf (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))) ≫
          moduleSMulHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) ≫ 𝟙 _ :=
  (moduleSMul_map_aux' J Φ O G).trans
    (congrArg (fun m ↦ Limits.prodComparison Φ (ringSheaf O) (moduleSheaf O G) ≫ m)
      (prodMap_id_comp J
        (moduleSMulHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))).symm)

end Stacks.Sheaves.ToposPullback

/-! ## Inverse images of sheaves of modules along a morphism of topoi -/

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory Limits Sheaf Functor Opposite

universe ww ww' vv uu vv' uu'

/-- The data asserting that inverse image along a morphism of topoi carries modules over `O`
to modules over the inverse-image ring. The natural isomorphisms identify the underlying ring
and module sheaves with their ordinary inverse images, and the operation equations identify
their algebraic structures with the transported original structures. The displayed `action`
is the scalar multiplication of the resulting sheaf of modules. -/
structure PullbackModuleData
    {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [J.HasSheafCompose (forget RingCat.{ww})]
    [K.HasSheafCompose (forget RingCat.{ww'})]
    [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
    [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
    (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
    (O : Sheaf K RingCat.{ww'}) where
  /-- The inverse-image sheaf of rings. -/
  ring : Sheaf J RingCat.{ww}
  /-- Pullback of modules, functorial in the module. -/
  moduleFunctor : CategoryTheory.Functor (SheafOfModules.{ww'} O) (SheafOfModules.{ww} ring)
  /-- The underlying sheaf of the inverse-image ring is the inverse image of the underlying
  sheaf of the original ring. -/
  ringIso : ringSheaf ring ≅ f.inverseImage.obj (ringSheaf O)
  /-- The underlying sheaf of a pulled-back module is naturally its inverse-image sheaf. -/
  moduleIso : moduleFunctor ⋙ moduleSheafFunctor ring ≅ moduleSheafFunctor O ⋙ f.inverseImage
  /-- The scalar multiplication map on each inverse-image module. -/
  action (G : SheafOfModules.{ww'} O) :
    ringSheaf ring ⨯ moduleSheaf ring (moduleFunctor.obj G) ⟶
      moduleSheaf ring (moduleFunctor.obj G)
  /-- The preceding map is the scalar multiplication belonging to the pulled-back module. -/
  action_apply (G : SheafOfModules.{ww'} O) (X : Cᵒᵖ)
      (p : (ringSheaf ring ⨯ moduleSheaf ring (moduleFunctor.obj G)).obj.obj X) :
      (action G).hom.app X p =
        let r : ring.obj.obj X :=
          (Limits.prod.fst : ringSheaf ring ⨯ moduleSheaf ring (moduleFunctor.obj G) ⟶
            ringSheaf ring).hom.app X p
        let m : (moduleFunctor.obj G).val.obj X :=
          (Limits.prod.snd : ringSheaf ring ⨯ moduleSheaf ring (moduleFunctor.obj G) ⟶
            moduleSheaf ring (moduleFunctor.obj G)).hom.app X p
        r • m
  /-- Ring addition is the inverse image of the original addition. -/
  ringAdd_map :
    f.inverseImage.map (ringAddHom O) =
      Limits.prodComparison f.inverseImage (ringSheaf O) (ringSheaf O) ≫
        Limits.prod.map ringIso.inv ringIso.inv ≫ ringAddHom ring ≫ ringIso.hom
  /-- Ring multiplication is the inverse image of the original multiplication. -/
  ringMul_map :
    f.inverseImage.map (ringMulHom O) =
      Limits.prodComparison f.inverseImage (ringSheaf O) (ringSheaf O) ≫
        Limits.prod.map ringIso.inv ringIso.inv ≫ ringMulHom ring ≫ ringIso.hom
  /-- Ring negation is the inverse image of the original negation. -/
  ringNeg_map :
    f.inverseImage.map (ringNegHom O) = ringIso.inv ≫ ringNegHom ring ≫ ringIso.hom
  /-- Ring zero is the inverse image of the original zero. -/
  ringZero_map :
    f.inverseImage.map (ringZeroHom O) =
      Limits.terminalComparison f.inverseImage ≫ ringZeroHom ring ≫ ringIso.hom
  /-- Ring one is the inverse image of the original one. -/
  ringOne_map :
    f.inverseImage.map (ringOneHom O) =
      Limits.terminalComparison f.inverseImage ≫ ringOneHom ring ≫ ringIso.hom
  /-- Module addition is the inverse image of the original addition. -/
  moduleAdd_map (G : SheafOfModules.{ww'} O) :
    f.inverseImage.map (moduleAddHom O G) =
      Limits.prodComparison f.inverseImage (moduleSheaf O G) (moduleSheaf O G) ≫
        Limits.prod.map (moduleIso.app G).inv (moduleIso.app G).inv ≫
          moduleAddHom ring (moduleFunctor.obj G) ≫ (moduleIso.app G).hom
  /-- Module negation is the inverse image of the original negation. -/
  moduleNeg_map (G : SheafOfModules.{ww'} O) :
    f.inverseImage.map (moduleNegHom O G) =
      (moduleIso.app G).inv ≫ moduleNegHom ring (moduleFunctor.obj G) ≫ (moduleIso.app G).hom
  /-- Module zero is the inverse image of the original zero. -/
  moduleZero_map (G : SheafOfModules.{ww'} O) :
    f.inverseImage.map (moduleZeroHom O G) =
      Limits.terminalComparison f.inverseImage ≫
        moduleZeroHom ring (moduleFunctor.obj G) ≫ (moduleIso.app G).hom
  /-- The action is the inverse image of the original scalar multiplication, using the
  canonical binary-product comparison. -/
  action_map (G : SheafOfModules.{ww'} O) :
    f.inverseImage.map (moduleSMulHom O G) =
      Limits.prodComparison f.inverseImage (ringSheaf O) (moduleSheaf O G) ≫
        Limits.prod.map ringIso.inv (moduleIso.app G).inv ≫ action G ≫ (moduleIso.app G).hom

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]

/-- The inverse image of a sheaf of `O`-modules under a morphism of topoi is naturally a sheaf of
modules over the inverse-image ring, and this construction is functorial in the module. -/
@[stacks 03D2]
noncomputable def pullbackModule
    (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
    (O : Sheaf K RingCat.{ww'}) : PullbackModuleData J K f O :=
  haveI := f.preservesFiniteLimits
  { ring := pullbackRingSheaf J f.inverseImage O
    moduleFunctor := pullbackModuleFunctor J f.inverseImage O
    ringIso := Iso.refl _
    moduleIso := Iso.refl _
    action := fun _ ↦ moduleSMulHom _ _
    action_apply := fun _ _ _ ↦ rfl
    ringAdd_map := ringAdd_map_aux J f.inverseImage O
    ringMul_map := ringMul_map_aux J f.inverseImage O
    ringNeg_map := ringNeg_map_aux J f.inverseImage O
    ringZero_map := ringZero_map_aux J f.inverseImage O
    ringOne_map := ringOne_map_aux J f.inverseImage O
    moduleAdd_map := fun G ↦ moduleAdd_map_aux J f.inverseImage O G
    moduleNeg_map := fun G ↦ moduleNeg_map_aux J f.inverseImage O G
    moduleZero_map := fun G ↦ moduleZero_map_aux J f.inverseImage O G
    action_map := fun G ↦ moduleSMul_map_aux J f.inverseImage O G }

end Stacks.Sheaves.ToposPullback
