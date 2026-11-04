module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import StacksFrontier.RingTheory.Cech.CechColimitDatum
public import StacksFrontier.RingTheory.Cech.RingBaseChangeDerived

/-!
# Stacks 099D, step 2: the colimit read over the objects under a fixed one

Step 2 of the proof of [Stacks, Tag 099D] takes the filtered colimit, over the index category
`Stacks.PairSite.PairOver A I`, of the values of a complex of pair-modules. This file re-reads
that colimit over the objects of the index category **under a fixed object `X`**, and does the
same for the base change of a fixed complex of `X.pair.ring`-modules. Both colimits then live in
one category — the modules over the ring of `X.pair` — which is what lets a natural
transformation between the two diagrams, quasi-isomorphic in each degree, be pushed through the
exactness of filtered colimits.

The index category is filtered (`Stacks.PairSite.PairOver.isFiltered`), so the forgetful functor
of the under-category is final and the colimit may be computed over `Under X`
(`CategoryTheory.Under.final_forget`). Every object `Y` under `X` carries a ring map
`X.pair.ring ⟶ Y.right.pair.ring`, so the value of a pair-module at `Y` and the base change of a
fixed `X.pair.ring`-module along that ring map are both `X.pair.ring`-modules.

## Main definitions

* `Stacks.PairSite.PairOver.underHom` — the ring map from the ring of `X.pair` to the ring of the
  pair of an object under `X`.
* `Stacks.PairSite.PairOver.underSections` — the diagram, over `Under X`, of the values of a
  pair-module, read over the ring of `X.pair`; `Stacks.PairSite.PairOver.underSectionsComplex` is
  the same for a complex of pair-modules.
* `Stacks.PairSite.PairOver.underRing` — the diagram of the rings of the pairs, i.e.
  `underSections` of the structure pair-module.
* `Stacks.PairSite.PairOver.underGermCocone`, `Stacks.PairSite.PairOver.underRingCocone` and
  `Stacks.PairSite.PairOver.underSectionsComplexCocone` — the cocones of germ maps, of structure
  maps and of germ maps on complexes.
* `Stacks.PairSite.PairOver.tensorComplexFunctor` — the degreewise tensor product of a varying
  module with a fixed cochain complex, and
  `Stacks.PairSite.PairOver.underTensorComplex`/`underTensorCocone` the resulting diagram and
  cocone of base changes of a fixed complex.
* `Stacks.PairSite.PairOver.baseMod` and `Stacks.PairSite.PairOver.tmulBase` — a ring, read as a
  module along a ring map, and the pure tensors of the base change it computes.

## Main results

* `Stacks.PairSite.PairOver.isColimit_underGermCocone` — **the colimit of step 2 is the colimit
  over the objects under a fixed one**, in the modules over the ring of `X.pair`.
* `Stacks.PairSite.PairOver.isColimit_underRingCocone` — **`A` is the colimit of the rings of the
  pairs of the objects under `X`**, read in the modules over the ring of `X.pair`.
* `Stacks.PairSite.PairOver.isColimit_underSectionsComplexCocone` and
  `Stacks.PairSite.PairOver.isColimit_underTensorCocone` — the two colimits on complexes. The
  second one is the colimit of the first diagram tensored with a fixed complex, and tensoring
  preserves colimits because it is a left adjoint.
* `Stacks.PairSite.PairOver.whiskerLeft_baseMod` and
  `Stacks.PairSite.PairOver.tensorComplexBaseIso` — tensoring with the base ring *is* degreewise
  extension of scalars, in a single degree and on complexes.
* `Stacks.PairSite.PairOver.adjointHom_tmulBase` and
  `Stacks.PairSite.PairOver.complexAdj_homEquiv_symm_f` — the adjoint of a semilinear map on a
  pure tensor, and the degreewise description of the complex-level adjoint.

## Implementation notes

The objects of the two diagrams are *definitionally* equal to the base changes they stand for:
`(ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj V)` is the tensor product of
`V` with `(ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)` on the nose, which is why
`Stacks.PairSite.PairOver.tensorComplexBaseIso` has identity components and only the
differentials need an argument. The *morphisms* differ: `Mathlib`'s degreewise extension of
scalars uses `LinearMap.baseChange`, and the monoidal whiskering uses `LinearMap.lTensor`, so
`whiskerLeft_baseMod` is proved on pure tensors rather than by `rfl`.

`Stacks.PairSite.PairOver.complexAdj_homEquiv_symm_f` is stated with
`Functor.mapHomologicalComplex` and not with `CochainComplex.restrictScalars`: the two are
definitionally equal, but `rw` works only in the first spelling, and typeclass search for
`QuasiIso` only matches the first.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u

namespace Stacks.PairSite.PairOver

variable {A : Type u} [CommRing A] {I : Ideal A}

/-! ### The structure map of an object under a fixed one -/

/-- The ring map from the ring of `X.pair` to the ring of the pair of an object under `X`. -/
def underHom {X : PairOver A I} (Y : Under X) : X.pair.ring →+* Y.right.pair.ring :=
  (Hom.toHom Y.hom).toRingHom

/-- The structure map of an object `Y` under `X`, composed with `underHom Y`, is the structure map
of `X`. -/
theorem hom_comp_underHom {X : PairOver A I} (Y : Under X) :
    Y.right.hom.comp (underHom Y) = X.hom := Hom.w Y.hom

/-- The structure map of an object `Y` under `X` sends `underHom Y r` to the image of `r` under
the structure map of `X`. -/
theorem hom_underHom_apply {X : PairOver A I} (Y : Under X) (r : X.pair.ring) :
    Y.right.hom (underHom Y r) = X.hom r :=
  congrArg (fun φ : X.pair.ring →+* A => φ r) (hom_comp_underHom Y)

/-- For a morphism `f : Y ⟶ Z` under `X`, the ring map of `f` composed with `underHom Y` is
`underHom Z`. -/
theorem underHom_map {X : PairOver A I} {Y Z : Under X} (f : Y ⟶ Z) :
    ((Hom.toHom f.right).toRingHom).comp (underHom Y) = underHom Z := by
  have h := Under.w f
  unfold underHom
  rw [← h]
  rfl

/-- For a morphism `f : Y ⟶ Z` under `X`, the ring map of `f` sends `underHom Y r` to
`underHom Z r`. -/
theorem underHom_map_apply {X : PairOver A I} {Y Z : Under X} (f : Y ⟶ Z) (r : X.pair.ring) :
    (Hom.toHom f.right).toRingHom (underHom Y r) = underHom Z r :=
  congrArg (fun φ : X.pair.ring →+* Z.right.pair.ring => φ r) (underHom_map f)

/-! ### The diagram of the values of a pair-module over the objects under a fixed one -/

/-- The diagram, over the objects of the index category under a fixed object `X`, of the values
of a pair-module, each read as a module over the ring of `X.pair`. -/
def underSections (M : PairModule.{u}) {X : PairOver A I} :
    Under X ⥤ ModuleCat.{u} X.pair.ring where
  obj Y := (ModuleCat.restrictScalars (underHom Y)).obj (M.value Y.right.pair)
  map {Y Z} f := ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars (underHom Y)).obj (M.value Y.right.pair))
      (Y := (ModuleCat.restrictScalars (underHom Z)).obj (M.value Z.right.pair))
    { toFun := fun m => M.restriction (Hom.toHom f.right) m
      map_add' := fun a b => map_add (M.restriction (Hom.toHom f.right)).hom a b
      map_smul' := fun r m =>
        ((M.restriction (Hom.toHom f.right)).hom.map_smul (underHom Y r) m).trans
          (congrArg (fun s : Z.right.pair.ring =>
              s • ((M.restriction (Hom.toHom f.right)).hom m))
            (underHom_map_apply f r)) }
  map_id Y := ModuleCat.hom_ext (LinearMap.ext fun m =>
    PairModule.restriction_id_apply M Y.right.pair m)
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun m =>
    PairModule.restriction_comp_apply M (Hom.toHom f.right) (Hom.toHom g.right) m)

/-- The objects of the index category under a fixed one, read as indices of the site of the
index category. -/
def projUU (X : PairOver A I) : Under X ⥤ (PairOver A I)ᵒᵖᵒᵖ :=
  Under.forget X ⋙ opOp (PairOver A I)

/-- The functor `Stacks.PairSite.PairOver.projUU X` is final. -/
instance projUU_final (X : PairOver A I) : (projUU X).Final :=
  inferInstanceAs ((Under.forget X ⋙ opOp (PairOver A I)).Final)

/-- `Stacks.PairSite.PairOver.underSections`, read on underlying abelian groups, is the
restriction of the underlying presheaf of abelian groups of the pair-module. -/
def underSectionsIso (M : PairModule.{u}) {X : PairOver A I} :
    underSections M (X := X) ⋙ forget₂ (ModuleCat.{u} X.pair.ring) AddCommGrpCat.{u} ≅
      projUU X ⋙ (indexModule A I M).presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    refine Eq.trans (Category.comp_id _) (Eq.trans ?_ (Category.id_comp _).symm)
    rfl)

/-- The cocone of germ maps over the objects of the index category under a fixed object. -/
def underGermCocone (hI : I.FG) (M : PairModule.{u}) (X : PairOver A I) :
    Cocone (underSections M (X := X)) where
  pt := (ModuleCat.restrictScalars X.hom).obj ((colimitFunctor hI).obj M)
  ι :=
    { app := fun Y => ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars (underHom Y)).obj (M.value Y.right.pair))
        (Y := (ModuleCat.restrictScalars X.hom).obj ((colimitFunctor hI).obj M))
        { toFun := fun m => germ hI M Y.right m
          map_add' := fun a b => map_add (germ hI M Y.right).hom a b
          map_smul' := fun r m =>
            ((germ hI M Y.right).hom.map_smul (underHom Y r) m).trans
              (congrArg (fun a : A => a • ((germ hI M Y.right).hom m))
                (hom_underHom_apply Y r)) }
      naturality := fun _ _ f => ModuleCat.hom_ext (LinearMap.ext fun m =>
        germ_restriction hI M f.right m) }

/-- **The colimit of step 2 may be computed over the objects under a fixed one.** The germ maps
at the objects of the index category under a fixed object `X` exhibit the colimit module as the
colimit of that restricted diagram, in the category of modules over the ring of `X.pair`. -/
def isColimit_underGermCocone (hI : I.FG) (M : PairModule.{u}) (X : PairOver A I) :
    IsColimit (underGermCocone hI M X) := by
  refine isColimitOfReflects (forget₂ (ModuleCat.{u} X.pair.ring) AddCommGrpCat.{u}) ?_
  refine (IsColimit.equivOfNatIsoOfIso (underSectionsIso M (X := X)) _
    ((colimit.cocone ((indexModule A I M).presheaf)).whisker (projUU X)) ?_).symm
    ((Functor.Final.isColimitWhiskerEquiv (projUU X) _).symm
      (colimit.isColimit ((indexModule A I M).presheaf)))
  exact Cocone.ext (Iso.refl _) (fun _ => by
    refine Eq.trans (Category.comp_id _) ?_
    exact Eq.trans (Category.id_comp _) rfl)


/-! ### The diagram of the rings -/

/-- The diagram, over the objects of the index category under a fixed object `X`, of the rings
of the pairs, each read as a module over the ring of `X.pair`. -/
abbrev underRing (X : PairOver A I) : Under X ⥤ ModuleCat.{u} X.pair.ring :=
  underSections structureModule.{u} (X := X)

/-- `A`, read as a module over the ring of `X.pair` along the structure map of `X`. -/
abbrev underBase (X : PairOver A I) : ModuleCat.{u} X.pair.ring :=
  (ModuleCat.restrictScalars X.hom).obj (ModuleCat.of A A)

/-- The cocone of structure maps `A₀ ⟶ A` over the objects of the index category under a fixed
object. -/
def underRingCocone (hI : I.FG) (X : PairOver A I) : Cocone (underRing X) :=
  (underGermCocone hI structureModule.{u} X).extend
    ((ModuleCat.restrictScalars X.hom).map (colimitStructureHom hI))

/-- The leg of `underRingCocone` at an object `Y` under `X` is the structure map of `Y`. -/
@[simp]
theorem underRingCocone_ι_app_apply (hI : I.FG) (X : PairOver A I) (Y : Under X)
    (r : Y.right.pair.ring) :
    (underRingCocone hI X).ι.app Y r = Y.right.hom r :=
  colimitStructureHom_germAt hI Y.right r

/-- **`A` is the colimit of the rings of the pairs of the objects under a fixed one.** -/
def isColimit_underRingCocone (hI : I.FG) (X : PairOver A I) :
    IsColimit (underRingCocone hI X) :=
  (isColimit_underGermCocone hI structureModule.{u} X).ofIsoColimit
    (Cocone.ext
      ((ModuleCat.restrictScalars X.hom).mapIso (colimitStructureIso hI)) (fun _ => rfl))

/-! ### Tensoring a fixed complex with a varying module -/

section Tensor

variable {R : Type u} [CommRing R]

/-- Degreewise tensor product of a varying module with a fixed cochain complex. -/
def tensorComplexFunctor (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj W := ((tensorLeft W).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  map h :=
    { f := fun n => h ▷ P.X n
      comm' := fun i j _ => (whisker_exchange h (P.d i j)).symm }
  map_id _ := HomologicalComplex.hom_ext _ _ fun _ => id_whiskerRight _ _
  map_comp _ _ := HomologicalComplex.hom_ext _ _ fun _ => comp_whiskerRight _ _ _

end Tensor

/-! ### Base change read as a tensor product -/

section BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- `S`, read as an `R`-module along `φ`. -/
abbrev baseMod : ModuleCat.{u} R := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)

/-- The element `s ⊗ v` of the base change `S ⊗_R V`. -/
def tmulBase (V : ModuleCat.{u} R) (s : S) (v : V) : ((baseMod φ) ⊗ V : ModuleCat.{u} R) :=
  TensorProduct.tmul (R := R) (show (baseMod φ) from s) v

/-- Two linear maps out of `S ⊗_R V` agreeing on the elements `tmulBase φ V s v` are equal. -/
theorem hom_ext_tmulBase {V Z : ModuleCat.{u} R}
    {a b : ((baseMod φ) ⊗ V : ModuleCat.{u} R) ⟶ Z}
    (h : ∀ (s : S) (v : V), a.hom (tmulBase φ V s v) = b.hom (tmulBase φ V s v)) : a = b :=
  ModuleCat.hom_ext (TensorProduct.ext' fun s v => h s v)

/-- Tensoring with `S` is the degreewise extension of scalars. -/
theorem whiskerLeft_baseMod {V V' : ModuleCat.{u} R} (h : V ⟶ V') :
    (baseMod φ) ◁ h =
      (ModuleCat.restrictScalars φ).map ((ModuleCat.extendScalars φ).map h) :=
  ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl)

/-- The whiskering `h ▷ V` sends `s ⊗ v` to `h s ⊗ v`. -/
theorem whiskerRight_tmulBase {V : ModuleCat.{u} R} {S' : Type u} [CommRing S']
    (ψ : R →+* S') (h : baseMod φ ⟶ baseMod ψ) (s : S) (v : V) :
    (h ▷ V).hom (tmulBase φ V s v) = tmulBase ψ V (h.hom (show baseMod φ from s)) v := rfl

/-- In the extension of scalars of `V`, the element `s ⊗ v` is `s • (1 ⊗ v)`. -/
theorem tmulBase_eq_smul (V : ModuleCat.{u} R) (s : S) (v : V) :
    (show (ModuleCat.extendScalars φ).obj V from tmulBase φ V s v) =
      s • (show (ModuleCat.extendScalars φ).obj V from tmulBase φ V 1 v) :=
  congrArg (fun t : S => (show (ModuleCat.extendScalars φ).obj V from tmulBase φ V t v))
    (mul_one s).symm

open Stacks.CechRingBaseChange in
/-- The adjoint of a semilinear map, on a pure tensor. -/
theorem adjointHom_tmulBase {V : ModuleCat.{u} R} {W : ModuleCat.{u} S}
    (g : V ⟶ (ModuleCat.restrictScalars φ).obj W) (s : S) (v : V) :
    (adjointHom φ g).hom (tmulBase φ V s v) = s • (show W from g.hom v) :=
  (congrArg (adjointHom φ g).hom (tmulBase_eq_smul φ V s v)).trans
    (((adjointHom φ g).hom.map_smul s _).trans
      (congrArg (fun z : W => s • z) (adjointHom_tensorOne φ g v)))

open Stacks.CechRingBaseChange in
/-- The complex-level adjoint of a map of complexes is, in each degree, the adjoint of its
component. -/
theorem complexAdj_homEquiv_symm_f {K : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : CochainComplex (ModuleCat.{u} S) ℤ}
    (u : K ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    (i : ℤ) :
    (((complexAdj φ).homEquiv K L).symm u).f i = adjointHom φ (u.f i) := by
  show (((complexAdj φ).homEquiv _ _).symm u).f i =
    ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm (u.f i)
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  rfl

/-- **Degreewise base change of a complex is tensoring with `S`.** -/
def tensorComplexBaseIso (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorComplexFunctor P).obj (baseMod φ) ≅
      (CochainComplex.restrictScalars φ).obj ((CochainComplex.extendScalars φ).obj P) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j _ => by
    refine Eq.trans (Category.id_comp _) (Eq.trans ?_ (Category.comp_id _).symm)
    exact (whiskerLeft_baseMod φ (P.d i j)).symm)

/-- Every component of `tensorComplexBaseIso` is the identity. -/
@[simp]
theorem tensorComplexBaseIso_hom_f (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (tensorComplexBaseIso φ P).hom.f n = 𝟙 _ := rfl

end BaseChange

/-! ### The two diagrams of complexes -/

/-- The diagram, over the objects under `X`, of the complexes of sections of a complex of
pair-modules, each read over the ring of `X.pair`. -/
def underSectionsComplex (K : CochainComplex PairModule.{u} ℤ) (X : PairOver A I) :
    Under X ⥤ CochainComplex (ModuleCat.{u} X.pair.ring) ℤ where
  obj Y := (CochainComplex.restrictScalars (underHom Y)).obj (sectionsComplex K Y.right.pair)
  map f :=
    { f := fun n => (underSections (K.X n)).map f
      comm' := fun i j _ => ModuleCat.hom_ext (LinearMap.ext fun m =>
        PairModule.naturality_apply (K.d i j) (Hom.toHom f.right) m) }
  map_id Y := HomologicalComplex.hom_ext _ _ fun n => (underSections (K.X n)).map_id Y
  map_comp f g := HomologicalComplex.hom_ext _ _ fun n => (underSections (K.X n)).map_comp f g

/-- The cocone of germ maps on complexes over the objects under `X`. -/
def underSectionsComplexCocone (hI : I.FG) (K : CochainComplex PairModule.{u} ℤ)
    (X : PairOver A I) : Cocone (underSectionsComplex K X) where
  pt := (CochainComplex.restrictScalars X.hom).obj ((colimitComplexFunctor hI).obj K)
  ι :=
    { app := fun Y =>
        { f := fun n => (underGermCocone hI (K.X n) X).ι.app Y
          comm' := fun i j _ => ModuleCat.hom_ext (LinearMap.ext fun m =>
            germAt_naturality hI (K.d i j) Y.right m) }
      naturality := fun _ _ f => HomologicalComplex.hom_ext _ _ fun n =>
        (underGermCocone hI (K.X n) X).ι.naturality f }

/-- **The colimit complex of step 2 may be computed over the objects under a fixed one.** -/
def isColimit_underSectionsComplexCocone (hI : I.FG) (K : CochainComplex PairModule.{u} ℤ)
    (X : PairOver A I) : IsColimit (underSectionsComplexCocone hI K X) :=
  HomologicalComplex.isColimitOfEval _ _ fun n => isColimit_underGermCocone hI (K.X n) X

/-- The diagram, over the objects under `X`, of the base changes of a fixed complex of modules
over the ring of `X.pair`. -/
def underTensorComplex (X : PairOver A I)
    (P : CochainComplex (ModuleCat.{u} X.pair.ring) ℤ) :
    Under X ⥤ CochainComplex (ModuleCat.{u} X.pair.ring) ℤ :=
  underRing X ⋙ tensorComplexFunctor P

/-- The cocone of the base changes of a fixed complex to `A`. -/
def underTensorCocone (hI : I.FG) (X : PairOver A I)
    (P : CochainComplex (ModuleCat.{u} X.pair.ring) ℤ) :
    Cocone (underTensorComplex X P) :=
  (tensorComplexFunctor P).mapCocone (underRingCocone hI X)

/-- **`A ⊗ P` is the colimit of the `A₀ ⊗ P` over the objects under `X`.** -/
def isColimit_underTensorCocone (hI : I.FG) (X : PairOver A I)
    (P : CochainComplex (ModuleCat.{u} X.pair.ring) ℤ) :
    IsColimit (underTensorCocone hI X P) := by
  refine HomologicalComplex.isColimitOfEval _ _ fun n => ?_
  haveI := (ihom.adjunction (P.X n)).leftAdjoint_preservesColimits
  exact isColimitOfPreserves (tensorRight (P.X n)) (isColimit_underRingCocone hI X)

end Stacks.PairSite.PairOver

end
