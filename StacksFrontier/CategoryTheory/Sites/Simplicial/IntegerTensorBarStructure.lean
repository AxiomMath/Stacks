module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorBarTerm
import StacksFrontier.CategoryTheory.CommutingSquares

/-!
# The projection formula of Stacks 0D9E is compatible with the structure maps

Let `S` be a simplicial-site situation. The projection formula
`CategoryTheory.SimplicialSiteSituation.barTermIsoIntegerTensor` identifies, naturally in the
abelian sheaf `F` on the total site, the degree-`n` term `bar_n(F)` of the simplex-coefficient
resolution of Stacks 0D78 with the tensor product `g_{n!}ℤ ⊗_ℤ F`. That is a *degreewise*
identification. This file equips the tensor side with the two structure maps of the
simplex-coefficient resolution — the simplicial structure maps and the augmentation — and proves
that the identification carries one to the other, so that the whole resolution, and not only its
terms, is read through the projection formula (Stacks 0D9K).

Both structure maps come from the integral resolution of Stacks 09WI. Its degree-`n` term is the
sheafification of the free abelian presheaf on the presheaf of `n`-simplices, identified with
`g_{n!}ℤ` by `CategoryTheory.SimplicialSiteSituation.resolutionDegreeIso'`; its simplicial
structure maps reindex the simplices by precomposition, and its augmentation sends every simplex
to `1`. Tensoring those maps with `F` gives the two maps on the tensor side.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.integerFace`: the simplicial structure map
  `g_{m!}ℤ ⟶ g_{n!}ℤ` of a simplex map `θ : ⦋n⦌ ⟶ ⦋m⦌`, read through `resolutionDegreeIso'`.
* `CategoryTheory.SimplicialSiteSituation.integerTensorFace`: that map tensored with `F`, i.e.
  `g_{m!}ℤ ⊗_ℤ F ⟶ g_{n!}ℤ ⊗_ℤ F`.
* `CategoryTheory.SimplicialSiteSituation.integerAugmentation`: the augmentation `g_{0!}ℤ ⟶ ℤ`
  of the integral resolution, read through `resolutionDegreeIso'`.
* `CategoryTheory.SimplicialSiteSituation.unitTensorIso`: **the unit identification**
  `ℤ ⊗_ℤ - ≅ 𝟭`, obtained by writing `ℤ` as the sheafification of the free presheaf of modules
  on the one-point presheaf of types, whose copower is the identity.
* `CategoryTheory.SimplicialSiteSituation.integerTensorAugmentation`: the augmentation tensored
  with `F` followed by the unit identification, i.e. `g_{0!}ℤ ⊗_ℤ F ⟶ F`.
* `CategoryTheory.copowerReindex`: the copower of an abelian presheaf is functorial in the
  presheaf of labels.

## Main results

* `CategoryTheory.SimplicialSiteSituation.barTermIsoIntegerTensor_face`: **the projection formula
  is compatible with the simplicial structure maps.**
* `CategoryTheory.SimplicialSiteSituation.barTermIsoIntegerTensor_augmentation`: **the projection
  formula is compatible with the augmentation.**
* `CategoryTheory.freeTensorCopowerIso_reindex` and
  `CategoryTheory.SimplicialSiteSituation.copowerStdSimplexIso_simplexMap`: the two
  presheaf-level identifications the projection formula is built from are natural in the presheaf
  of labels; under the second, a simplex map becomes the reindexing of the summands of the
  simplex-coefficient presheaf by precomposition.
* `PresheafOfModules.sheafifyFreeObjIso_naturality`: the presentation of a sheafified free
  presheaf of modules as a sheafified free abelian presheaf is natural in the presheaf of labels;
  through `resolutionDegreeIso'` it identifies the structure maps of Stacks 09WI with the
  reindexing of a free presheaf.
* `PresheafOfModules.tensorSheafifySecondIso_hom_naturality_left`: the mixed tensor comparison of
  Stacks 0GMW is natural in its presheaf factor, as
  `PresheafOfModules.tensorSheafifySecondIso_hom_naturality` is in its sheaf factor.

## Implementation notes

Unqualified names in this section are in the namespace `CategoryTheory.SimplicialSiteSituation`.

`resolutionDegreeIso'` is opaque. Both structure maps are defined by conjugating with it, and
`componentIntegerModuleIso_face` and `pointIntegerModuleIso_augmentation` show that it cancels
against the copies inside `componentIntegerSheafIsoSheafifyFreeModule`.

`integerAugmentation` is `resolutionAugmentation'` conjugated by `resolutionDegreeIso'`, so it is
the augmentation of `simplicialIntegerResolution` read in degree zero.

The two spellings `SheafOfModules (Sheaf.toRingCat _ _)` and
`Stacks.DerivedTensor.RingedSite.Modules _` of the sheaves of modules over the constant sheaf of
rings `ℤ` are definitionally but not reducibly equal, so composites of maps of sheaves of modules
are rewritten with explicit `Eq.trans`/`congrArg` chains rather than `rw`.

The unit identification `ℤ ⊗_ℤ - ≅ 𝟭` is built from the presentation of `ℤ` as the
sheafification of the free presheaf of modules on the one-point presheaf of types, under which the
copower by a point is the identity (`copowerPointIso`); the left unitor of the monoidal structure
on sheaves of modules does not compute on sections. It is stated objectwise, with naturality as
the separate equation `unitTensorIsoAux_naturality`.

## References

* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

universe v₀ u₀ u

namespace CategoryTheory

/-! ### Reindexing a copower along a map of presheaves of types -/

section Reindex

variable {C : Type u₀} [Category.{v₀} C] {E E' : Cᵒᵖ ⥤ Type u₀} (ε : E ⟶ E')
  (G : Cᵒᵖ ⥤ AddCommGrpCat.{u₀})

/-- Over one object, the map of copowers which reindexes the summands along `ε`. -/
def copowerReindexApp (X : Cᵒᵖ) :
    (copowerPresheafObj E G).obj X ⟶ (copowerPresheafObj E' G).obj X :=
  AddCommGrpCat.ofHom (Finsupp.mapDomain.addMonoidHom (ConcreteCategory.hom (ε.app X)))

/-- The reindexing carries the summand labelled by `e` to the summand labelled by `ε e`. -/
@[simp] theorem copowerReindexApp_single (X : Cᵒᵖ) (e : E.obj X) (m : (G.obj X : Type u₀)) :
    AddCommGrpCat.Hom.hom (copowerReindexApp ε G X) (Finsupp.single e m) =
      Finsupp.single (ConcreteCategory.hom (ε.app X) e) m := by
  change Finsupp.mapDomain (ConcreteCategory.hom (ε.app X)) (Finsupp.single e m) = _
  rw [Finsupp.mapDomain_single]

/-- The copower of a presheaf of abelian groups is functorial in the presheaf of labels: a map
`ε : E ⟶ E'` of presheaves of types reindexes the summands. -/
def copowerReindex : copowerPresheafObj E G ⟶ copowerPresheafObj E' G where
  app := copowerReindexApp ε G
  naturality X Y f := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro e m
    change AddCommGrpCat.Hom.hom (copowerReindexApp ε G Y)
        (AddCommGrpCat.Hom.hom (copowerRestriction E G f) (Finsupp.single e m)) =
      AddCommGrpCat.Hom.hom (copowerRestriction E' G f)
        (AddCommGrpCat.Hom.hom (copowerReindexApp ε G X) (Finsupp.single e m))
    rw [copowerRestriction_single, copowerReindexApp_single, copowerReindexApp_single,
      copowerRestriction_single]
    have hn : ConcreteCategory.hom (ε.app Y) (ConcreteCategory.hom (E.map f) e) =
        ConcreteCategory.hom (E'.map f) (ConcreteCategory.hom (ε.app X) e) :=
      NatTrans.naturality_apply ε f e
    exact congrArg (fun y => Finsupp.single y (AddCommGrpCat.Hom.hom (G.map f) m)) hn

/-- The value of the reindexing on the summand labelled by `e`. -/
@[simp] theorem copowerReindex_app_single (X : Cᵒᵖ) (e : E.obj X) (m : (G.obj X : Type u₀)) :
    AddCommGrpCat.Hom.hom ((copowerReindex ε G).app X) (Finsupp.single e m) =
      Finsupp.single (ConcreteCategory.hom (ε.app X) e) m :=
  copowerReindexApp_single ε G X e m

/-- Reindexing the summands and acting on the coefficients commute. -/
theorem copowerReindex_copowerPresheafMap {H : Cᵒᵖ ⥤ AddCommGrpCat.{u₀}} (α : G ⟶ H) :
    copowerReindex ε G ≫ copowerPresheafMap E' α =
      copowerPresheafMap E α ≫ copowerReindex ε H := by
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply Finsupp.addHom_ext
  intro e m
  change AddCommGrpCat.Hom.hom ((copowerPresheafMap E' α).app X)
      (AddCommGrpCat.Hom.hom ((copowerReindex ε G).app X) (Finsupp.single e m)) =
    AddCommGrpCat.Hom.hom ((copowerReindex ε H).app X)
      (AddCommGrpCat.Hom.hom ((copowerPresheafMap E α).app X) (Finsupp.single e m))
  rw [copowerReindex_app_single, copowerPresheafMap_app_single, copowerPresheafMap_app_single,
    copowerReindex_app_single]

end Reindex

/-! ### The free-tensor identification is natural in the presheaf of labels -/

section FreeTensorReindex

variable {C : Type u₀} [Category.{v₀} C] {E E' : Cᵒᵖ ⥤ Type u₀} (ε : E ⟶ E')
  (R : Cᵒᵖ ⥤ CommRingCat.{u₀})
  (N : PresheafOfModules.{u₀} (R ⋙ forget₂ CommRingCat.{u₀} RingCat.{u₀}))

open PresheafOfModules

/-- The identification of `R[E] ⊗_R N` with the copower of `N` by `E` is natural in `E`. -/
theorem freeTensorCopowerIso_reindex :
    (toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map
          (tensorHom ((free (R ⋙ forget₂ CommRingCat RingCat)).map ε) (𝟙 N)) ≫
        (freeTensorCopowerIso E' R N).hom =
      (freeTensorCopowerIso E R N).hom ≫
        copowerReindex ε ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj N) := by
  refine square_of_inv _ _ _ _ ?_
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply Finsupp.addHom_ext
  intro e m
  have h1 : AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N X).inv
      (Finsupp.single e m) = _ :=
    freeTensorCopowerIsoApp_inv_single E R N X e m
  have h2 : Hom.app (tensorHom ((free (R ⋙ forget₂ CommRingCat RingCat)).map ε) (𝟙 N)) X
      (ModuleCat.freeMk (R := (R.obj X : Type u₀)) e ⊗ₜ[(R.obj X : Type u₀)] m) = _ :=
    tensorHom_tmul ((free (R ⋙ forget₂ CommRingCat RingCat)).map ε) (𝟙 N) X _ m
  have h3 : AddCommGrpCat.Hom.hom ((copowerReindex ε
      ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj N)).app X) (Finsupp.single e m) = _ :=
    copowerReindex_app_single ε _ X e m
  have h4 : AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E' R N X).inv
      (Finsupp.single (ConcreteCategory.hom (ε.app X) e) m) = _ :=
    freeTensorCopowerIsoApp_inv_single E' R N X _ m
  change AddCommGrpCat.Hom.hom
      (((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map
        (tensorHom ((free (R ⋙ forget₂ CommRingCat RingCat)).map ε) (𝟙 N))).app X)
      (AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N X).inv (Finsupp.single e m)) =
    AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E' R N X).inv
      (AddCommGrpCat.Hom.hom ((copowerReindex ε
        ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj N)).app X) (Finsupp.single e m))
  refine Eq.trans (congrArg (AddCommGrpCat.Hom.hom
    (((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map
      (tensorHom ((free (R ⋙ forget₂ CommRingCat RingCat)).map ε) (𝟙 N))).app X)) h1) ?_
  refine Eq.trans h2 ?_
  refine Eq.trans ?_ (congrArg (AddCommGrpCat.Hom.hom
    (freeTensorCopowerIsoApp E' R N X).inv) h3).symm
  refine Eq.trans ?_ h4.symm
  have hfree : Hom.app ((free (R ⋙ forget₂ CommRingCat RingCat)).map ε) X
        (ModuleCat.freeMk (R := (R.obj X : Type u₀)) e) =
      ModuleCat.freeMk (R := (R.obj X : Type u₀)) (ConcreteCategory.hom (ε.app X) e) :=
    ModuleCat.free_map_apply _ e
  congr 1

end FreeTensorReindex

end CategoryTheory

/-! ### The free presheaf of modules over the integers is natural in the presheaf of labels -/

namespace PresheafOfModules

open CategoryTheory

section FreeAb

variable {C : Type u₀} [Category.{v₀} C] {E E' : Cᵒᵖ ⥤ Type u₀} (ε : E ⟶ E')

/-- The underlying presheaf of abelian groups of the free presheaf of modules on `E` over the
constant presheaf of rings `ℤ` is natural in `E`. -/
theorem freeObjToPresheafIso_naturality :
    (toPresheaf (intRingPresheaf C)).map ((free (intRingPresheaf C)).map ε) ≫
        (freeObjToPresheafIso E').hom =
      (freeObjToPresheafIso E).hom ≫
        Functor.whiskerRight ε AddCommGrpCat.freeIntModule.{u₀} := by
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply Finsupp.addHom_ext
  intro x c
  change AddCommGrpCat.Hom.hom
      (((toPresheaf (intRingPresheaf C)).map ((free (intRingPresheaf C)).map ε)).app X)
      (Finsupp.single x c) =
    AddCommGrpCat.Hom.hom ((Functor.whiskerRight ε AddCommGrpCat.freeIntModule.{u₀}).app X)
      (Finsupp.single x c)
  have hl : AddCommGrpCat.Hom.hom
      (((toPresheaf (intRingPresheaf C)).map ((free (intRingPresheaf C)).map ε)).app X)
      (Finsupp.single x c) = Finsupp.single (ConcreteCategory.hom (ε.app X) x) c := by
    change Finsupp.mapDomain (ConcreteCategory.hom (ε.app X)) (Finsupp.single x c) = _
    rw [Finsupp.mapDomain_single]
  have hr : AddCommGrpCat.Hom.hom
      ((Functor.whiskerRight ε AddCommGrpCat.freeIntModule.{u₀}).app X) (Finsupp.single x c) =
      Finsupp.single (ConcreteCategory.hom (ε.app X) x) c :=
    AddCommGrpCat.freeIntModule_map_single _ x c
  exact hl.trans hr.symm

/-- The identification of the free presheaf of modules on `E` with the free abelian presheaf on
`E` is natural in `E`. -/
theorem freeObjToFreeAbIso_naturality :
    (toPresheaf (intRingPresheaf C)).map ((free (intRingPresheaf C)).map ε) ≫
        (freeObjToFreeAbIso E').hom =
      (freeObjToFreeAbIso E).hom ≫ Functor.whiskerRight ε AddCommGrpCat.free.{u₀} :=
  square_comp (freeObjToPresheafIso_naturality ε) <| NatTrans.ext <| funext fun X ↦
    AddCommGrpCat.freeIsoFreeIntModule.{u₀}.inv.naturality (ε.app X)

variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u₀}}
  (α : intRingPresheaf C ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u₀}] [HasWeakSheafify J AddCommGrpCat.{u₀}]

/-- **The sheafification of the free presheaf of modules is natural in the presheaf of
labels.** -/
theorem sheafifyFreeObjIso_naturality :
    (SheafOfModules.toSheaf R).map
          ((sheafification α).map ((free (intRingPresheaf C)).map ε)) ≫
        (sheafifyFreeObjIso α E').hom =
      (sheafifyFreeObjIso α E).hom ≫
        (presheafToSheaf J AddCommGrpCat.{u₀}).map
          (Functor.whiskerRight ε AddCommGrpCat.free.{u₀}) :=
  square_comp ((sheafificationCompToSheaf α).hom.naturality
      ((free (intRingPresheaf C)).map ε))
    (square_map (presheafToSheaf J AddCommGrpCat.{u₀}) _ _ _ _
      (freeObjToFreeAbIso_naturality ε))

end FreeAb

/-! ### The mixed tensor comparison is natural in the presheaf factor -/

section MixedLeft

open CategoryTheory.Sheaf

variable {C : Type u₀} [Category.{v₀} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u₀} RingCat.{u₀})]
  {O : Cᵒᵖ ⥤ CommRingCat.{u₀}} {Osharp : Sheaf J CommRingCat.{u₀}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (Sheaf.toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (Sheaf.toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u₀}] [HasWeakSheafify J AddCommGrpCat.{u₀}]
  {F F' : PresheafOfModules.{u₀} (O ⋙ forget₂ CommRingCat RingCat)} (h : F ⟶ F')
  (G : SheafOfModules.{u₀} (Sheaf.toRingCat J Osharp))

/-- The inverse of the mixed tensor comparison `tensorSheafifySecondIso` is natural in the
presheaf factor. -/
theorem tensorSheafifySecondIso_inv_naturality_left :
    (moduleSheafification.{v₀, u₀, u₀, u₀} J a).map
          (tensorHom h (𝟙 ((restrictSheafFunctor.{v₀, u₀, u₀, u₀} J a).obj G))) ≫
        (CategoryTheory.SimplicialSiteSituation.tensorSheafifySecondIso.{v₀, u₀, u₀, u₀, u₀}
          J a F' G).inv =
      (CategoryTheory.SimplicialSiteSituation.tensorSheafifySecondIso.{v₀, u₀, u₀, u₀, u₀}
            J a F G).inv ≫
        (Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, u₀, u₀, u₀} Osharp)).map
          (CategoryTheory.Prod.mkHom
            ((moduleSheafification.{v₀, u₀, u₀, u₀} J a).map h) (𝟙 G)) := by
  have hp : CategoryTheory.Prod.mkHom
        ((moduleSheafification.{v₀, u₀, u₀, u₀} J a).map h)
        ((moduleSheafification.{v₀, u₀, u₀, u₀} J a).map
          (𝟙 ((restrictSheafFunctor.{v₀, u₀, u₀, u₀} J a).obj G))) ≫
      CategoryTheory.Prod.mkHom
        (𝟙 ((moduleSheafification.{v₀, u₀, u₀, u₀} J a).obj F'))
        (sheafifyRestrictSheafIso.{v₀, u₀, u₀, u₀} J a G).hom =
    CategoryTheory.Prod.mkHom
        (𝟙 ((moduleSheafification.{v₀, u₀, u₀, u₀} J a).obj F))
        (sheafifyRestrictSheafIso.{v₀, u₀, u₀, u₀} J a G).hom ≫
      CategoryTheory.Prod.mkHom ((moduleSheafification.{v₀, u₀, u₀, u₀} J a).map h) (𝟙 G) :=
    CategoryTheory.Prod.hom_ext (by simp) (by simp)
  have hn := tensorSheafifyComparison_naturality J a F
      ((restrictSheafFunctor.{v₀, u₀, u₀, u₀} J a).obj G) h
      (𝟙 ((restrictSheafFunctor.{v₀, u₀, u₀, u₀} J a).obj G))
  rw [CategoryTheory.SimplicialSiteSituation.tensorSheafifySecondIso_inv,
    CategoryTheory.SimplicialSiteSituation.tensorSheafifySecondIso_inv]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
        ((congrArg (CategoryTheory.Functor.map _) hp).trans
          (CategoryTheory.Functor.map_comp _ _ _)))).trans
        (Category.assoc _ _ _).symm)))

/-- The mixed tensor comparison `tensorSheafifySecondIso` is natural in the presheaf factor. -/
theorem tensorSheafifySecondIso_hom_naturality_left :
    (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, u₀, u₀, u₀} Osharp)).map
          (CategoryTheory.Prod.mkHom
            ((moduleSheafification.{v₀, u₀, u₀, u₀} J a).map h) (𝟙 G)) ≫
        (CategoryTheory.SimplicialSiteSituation.tensorSheafifySecondIso.{v₀, u₀, u₀, u₀, u₀}
          J a F' G).hom =
      (CategoryTheory.SimplicialSiteSituation.tensorSheafifySecondIso.{v₀, u₀, u₀, u₀, u₀}
            J a F G).hom ≫
        (moduleSheafification.{v₀, u₀, u₀, u₀} J a).map
          (tensorHom h (𝟙 ((restrictSheafFunctor.{v₀, u₀, u₀, u₀} J a).obj G))) := by
  have h2 : (CategoryTheory.SimplicialSiteSituation.tensorSheafifySecondIso.{v₀,
          u₀, u₀, u₀, u₀} J a F G).hom ≫
      (moduleSheafification.{v₀, u₀, u₀, u₀} J a).map
          (tensorHom h (𝟙 ((restrictSheafFunctor.{v₀, u₀, u₀, u₀} J a).obj G))) ≫
        (CategoryTheory.SimplicialSiteSituation.tensorSheafifySecondIso.{v₀,
          u₀, u₀, u₀, u₀} J a F' G).inv =
      (Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, u₀, u₀, u₀} Osharp)).map
        (CategoryTheory.Prod.mkHom
          ((moduleSheafification.{v₀, u₀, u₀, u₀} J a).map h) (𝟙 G)) :=
    (congrArg (_ ≫ ·) (tensorSheafifySecondIso_inv_naturality_left J a h G)).trans
      (Iso.hom_inv_id_assoc _ _)
  exact (congrArg (· ≫ _) h2.symm).trans ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans (Category.comp_id _)))))

end MixedLeft

end PresheafOfModules

namespace CategoryTheory.SimplicialSiteSituation

open Stacks.DerivedTensor.AbelianSheaves Stacks.SheafOfModules.Tensor PresheafOfModules

/-! ### The simplex-coefficient identification is natural in the degree -/

section SimplexReindex

variable (S : SimplicialSiteSituation.{u})

/-- Reindexing the presheaf of simplices along a simplex map is precomposition. -/
theorem stdSimplexPresheafObjEquiv_simplexMap {n m : SimplexCategory} (θ : n ⟶ m)
    (U : S.totalCategoryᵒᵖ) (x : (stdSimplexPresheaf' S m).obj U) :
    stdSimplexPresheafObjEquiv S n U
        (ConcreteCategory.hom ((stdSimplexPresheafMap' S θ).app U) x) =
      θ ≫ stdSimplexPresheafObjEquiv S m U x :=
  rfl

/-- **The copower identification is natural in the simplicial degree.** Reindexing the labels
along a simplex map is the simplicial structure map of the simplex-coefficient presheaf. -/
theorem copowerStdSimplexIso_simplexMap {n m : SimplexCategory} (θ : n ⟶ m)
    (G : S.totalCategoryᵒᵖ ⥤ AddCommGrpCat.{u}) :
    copowerReindex (stdSimplexPresheafMap' S θ) G ≫ (copowerStdSimplexIso S n G).hom =
      (copowerStdSimplexIso S m G).hom ≫
        ((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj G).map θ.op := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply Finsupp.addHom_ext
  intro x c
  have h1 : AddCommGrpCat.Hom.hom ((copowerReindex (stdSimplexPresheafMap' S θ) G).app U)
      (Finsupp.single x c) = _ :=
    copowerReindex_app_single (stdSimplexPresheafMap' S θ) G U x c
  have h2 := copowerStdSimplexIso_hom_app_single S n G U
    (ConcreteCategory.hom ((stdSimplexPresheafMap' S θ).app U) x) c
  have h3 := copowerStdSimplexIso_hom_app_single S m G U x c
  have h4 := ι_copowerMap (C := AddCommGrpCat.{u})
    (fun φ : m ⟶ (totalSimplexDegree S).leftOp.obj U => θ ≫ φ)
    (𝟙 (G.obj U)) (stdSimplexPresheafObjEquiv S m U x)
  change AddCommGrpCat.Hom.hom ((copowerStdSimplexIso S n G).hom.app U)
      (AddCommGrpCat.Hom.hom ((copowerReindex (stdSimplexPresheafMap' S θ) G).app U)
        (Finsupp.single x c)) =
    AddCommGrpCat.Hom.hom
      (copowerMap (fun φ : m ⟶ (totalSimplexDegree S).leftOp.obj U => θ ≫ φ) (𝟙 (G.obj U)))
      (AddCommGrpCat.Hom.hom ((copowerStdSimplexIso S m G).hom.app U) (Finsupp.single x c))
  refine Eq.trans (congrArg (AddCommGrpCat.Hom.hom
    ((copowerStdSimplexIso S n G).hom.app U)) h1) ?_
  refine Eq.trans h2 ?_
  refine Eq.trans ?_ (congrArg (AddCommGrpCat.Hom.hom
    (copowerMap (fun φ : m ⟶ (totalSimplexDegree S).leftOp.obj U => θ ≫ φ)
      (𝟙 (G.obj U)))) h3).symm
  refine Eq.trans ?_ (congrArg (fun k => AddCommGrpCat.Hom.hom k c) h4).symm
  rw [stdSimplexPresheafObjEquiv_simplexMap]
  exact congrArg (fun k => AddCommGrpCat.Hom.hom k c) (Category.id_comp _).symm

end SimplexReindex

/-! ### The structure maps on the tensor side -/

section Structure

variable (S : SimplicialSiteSituation.{u})

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-- The structure map of the simplicial abelian sheaf of simplices of Stacks 09WI, read through
the identification of its degree-`n` term with `g_{n!}ℤ`. -/
def integerFace {n m : SimplexCategory} (θ : n ⟶ m) :
    componentIntegerSheaf S m ⟶ componentIntegerSheaf S n :=
  (resolutionDegreeIso' S m).inv ≫ (resolutionSimplicial' S).map θ.op ≫
    (resolutionDegreeIso' S n).hom

/-- The structure map of the simplicial abelian sheaf of simplices is the sheafification of the
reindexing of the free abelian presheaf on the simplices. -/
theorem resolutionSimplicial_map_whiskerRight {n m : SimplexCategory} (θ : n ⟶ m) :
    (resolutionSimplicial' S).map θ.op =
      (presheafToSheaf S.totalTopology Ab.{u}).map
        (Functor.whiskerRight (stdSimplexPresheafMap' S θ) AddCommGrpCat.free.{u}) :=
  rfl

/-- The presentation of `g_{n!}ℤ` as a sheafified free presheaf of modules is compatible with
the simplicial structure maps. -/
theorem componentIntegerSheafIsoSheafifyFreeModule_face {n m : SimplexCategory} (θ : n ⟶ m) :
    (moduleEquivalence S.totalTopology).functor.map
          ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).map
            ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map
              (stdSimplexPresheafMap' S θ))) ≫
        (componentIntegerSheafIsoSheafifyFreeModule S n).hom =
      (componentIntegerSheafIsoSheafifyFreeModule S m).hom ≫ integerFace S θ := by
  refine square_comp (sheafifyFreeObjIso_naturality (stdSimplexPresheafMap' S θ)
    (intRingSheafScalars S.totalTopology)) ?_
  rw [integerFace]
  exact (Iso.hom_inv_id_assoc (resolutionDegreeIso' S m) _).symm

/-- The value of the comparison of `g_{n!}ℤ` with a sheafified free presheaf of modules. -/
theorem componentIntegerModuleIso_hom (n : SimplexCategory) :
    (componentIntegerModuleIso S n).hom =
      (moduleEquivalence S.totalTopology).inverse.map
          (componentIntegerSheafIsoSheafifyFreeModule S n).inv ≫
        ((moduleEquivalence S.totalTopology).unitIso.app
          ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
            (barFree S n))).inv :=
  rfl

/-- An equivalence carries a square of isomorphisms presented through `e.functor` to the
corresponding square of the `e.inverse`-images, conjugated by the unit. -/
private theorem inverse_map_comp_unitIso_inv {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) {A B : D} {X Y : C} (f : A ⟶ B) (g : X ⟶ Y) (φ : e.functor.obj X ≅ A)
    (ψ : e.functor.obj Y ≅ B) (h : e.functor.map g ≫ ψ.hom = φ.hom ≫ f) :
    e.inverse.map f ≫ e.inverse.map ψ.inv ≫ (e.unitIso.app Y).inv =
      (e.inverse.map φ.inv ≫ (e.unitIso.app X).inv) ≫ g := by
  have hB : f ≫ ψ.inv = φ.inv ≫ e.functor.map g := by
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  exact square_comp (by rw [← e.inverse.map_comp, hB, e.inverse.map_comp]; rfl)
    (e.unitIso.inv.naturality g)

/-- **The presentation of `g_{n!}ℤ` as a sheafified free presheaf of modules is compatible with
the simplicial structure maps**, in sheaves of modules over the constant sheaf of rings `ℤ`. -/
theorem componentIntegerModuleIso_face {n m : SimplexCategory} (θ : n ⟶ m) :
    (moduleEquivalence S.totalTopology).inverse.map (integerFace S θ) ≫
        (componentIntegerModuleIso S n).hom =
      (componentIntegerModuleIso S m).hom ≫
        (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).map
          ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map
            (stdSimplexPresheafMap' S θ)) := by
  rw [componentIntegerModuleIso_hom, componentIntegerModuleIso_hom]
  exact inverse_map_comp_unitIso_inv _ _ _ _ _ (componentIntegerSheafIsoSheafifyFreeModule_face S θ)

/-- **The map `g_{m!}ℤ ⊗_ℤ F ⟶ g_{n!}ℤ ⊗_ℤ F` induced by a simplex map `θ : ⦋n⦌ ⟶ ⦋m⦌`**: the
structure map of the simplicial abelian sheaf of simplices, tensored with `F`. -/
def integerTensorFace {n m : SimplexCategory} (θ : n ⟶ m) :
    integerTensorAb S m ⟶ integerTensorAb S n :=
  Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse
    (Functor.whiskerRight
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
        ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ)))
      (moduleEquivalence S.totalTopology).functor)

/-- `integerTensorFace`, at an abelian sheaf, as the tensor bifunctor of Stacks 0GMW with its
right factor fixed. -/
theorem integerTensorFace_app {n m : SimplexCategory} (θ : n ⟶ m)
    (F : Sheaf S.totalTopology Ab.{u}) :
    (integerTensorFace S θ).app F =
      (moduleEquivalence S.totalTopology).functor.map
        ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map
          (CategoryTheory.Prod.mkHom
            ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ))
            (𝟙 (barModule S F)))) :=
  congrArg (moduleEquivalence S.totalTopology).functor.map
    ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)).symm

/-- A square between two presentations of a module as a sheafified free presheaf of modules gives
a square after tensoring with `barModule S F` and reading through the mixed tensor comparison. -/
private theorem tensor_map_comp_secondIso {E E' : S.totalCategoryᵒᵖ ⥤ Type u} (ε : E ⟶ E')
    {A A' : SheafOfModules.{u} S.barRings}
    (p : A ≅ (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj (freeObj E))
    (p' : A' ≅ (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj (freeObj E'))
    (α : A ⟶ A') (F : Sheaf S.totalTopology Ab.{u})
    (h : α ≫ p'.hom =
      p.hom ≫ (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).map
        ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map ε)) :
    (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map
          (CategoryTheory.Prod.mkHom α (𝟙 (barModule S F))) ≫
        ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map
          (CategoryTheory.Prod.mkHom p'.hom (𝟙 (barModule S F))) ≫
        (tensorSheafifySecondIso.{u, u, u, u, u} S.totalTopology (intUnit S) (freeObj E')
          (barModule S F)).hom) =
      ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map
          (CategoryTheory.Prod.mkHom p.hom (𝟙 (barModule S F))) ≫
        (tensorSheafifySecondIso.{u, u, u, u, u} S.totalTopology (intUnit S) (freeObj E)
          (barModule S F)).hom) ≫
        (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).map
          (tensorHom ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map ε)
            (𝟙 (barRestrict S F))) := by
  refine square_comp ?_
    (tensorSheafifySecondIso_hom_naturality_left S.totalTopology (intUnit S)
      ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map ε) (barModule S F))
  have hprod : CategoryTheory.Prod.mkHom α (𝟙 (barModule S F)) ≫
        CategoryTheory.Prod.mkHom p'.hom (𝟙 (barModule S F)) =
      CategoryTheory.Prod.mkHom p.hom (𝟙 (barModule S F)) ≫
        CategoryTheory.Prod.mkHom
          ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).map
            ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map ε)) (𝟙 (barModule S F)) :=
    CategoryTheory.Prod.hom_ext h (by simp)
  exact (((Functor.uncurry.obj
      (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map_comp _ _).symm.trans
    ((congrArg (Functor.uncurry.obj
        (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map hprod).trans
      ((Functor.uncurry.obj
        (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map_comp _ _)))

/-- **The projection formula is compatible with the simplicial structure maps, before
sheafifying the copower.** -/
theorem barTensorIso_face {n m : SimplexCategory} (θ : n ⟶ m)
    (F : Sheaf S.totalTopology Ab.{u}) :
    (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map
          (CategoryTheory.Prod.mkHom
            ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ))
            (𝟙 (barModule S F))) ≫
        (barTensorIso S n F).hom =
      (barTensorIso S m F).hom ≫
        (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).map
          (tensorHom
            ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map
              (stdSimplexPresheafMap' S θ)) (𝟙 (barRestrict S F))) := by
  rw [barTensorIso_hom, barTensorIso_hom]
  exact tensor_map_comp_secondIso S _ _ _ _ F (componentIntegerModuleIso_face S θ)

/-- **`barTermIsoIntegerTensor` is compatible with the simplicial structure maps.** -/
theorem barTermIsoIntegerTensor_face {n m : SimplexCategory} (θ : n ⟶ m)
    (F : Sheaf S.totalTopology Ab.{u}) :
    ((barSimplicial' S).obj F).map θ.op ≫ (barTermIsoIntegerTensor S n).hom.app F =
      (barTermIsoIntegerTensor S m).hom.app F ≫ (integerTensorFace S θ).app F := by
  have haux : (integerTensorFace S θ).app F ≫ (barTermIsoAux S n F).hom =
      (barTermIsoAux S m F).hom ≫ ((barSimplicial' S).obj F).map θ.op := by
    rw [barTermIsoAux_hom, barTermIsoAux_hom, integerTensorFace_app]
    exact square_comp
      (square_map (moduleEquivalence S.totalTopology).functor _ _ _ _
        (barTensorIso_face S θ F))
      (square_comp
        ((sheafificationCompToSheaf
          (Sheaf.toRingCatMap S.totalTopology (intUnit S))).hom.naturality
            (tensorHom
              ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map
                (stdSimplexPresheafMap' S θ)) (𝟙 (barRestrict S F))))
        (square_comp
          (square_map (presheafToSheaf S.totalTopology Ab.{u}) _ _ _ _
            (freeTensorCopowerIso_reindex (stdSimplexPresheafMap' S θ) (intPresheaf S)
              (barRestrict S F)))
          (square_comp
            (square_map (presheafToSheaf S.totalTopology Ab.{u})
              ((copowerPresheaf (stdSimplexPresheaf' S m)).mapIso (barCounitIso S F))
              ((copowerPresheaf (stdSimplexPresheaf' S n)).mapIso (barCounitIso S F))
              (copowerReindex (stdSimplexPresheafMap' S θ)
                ((toPresheaf (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).obj
                  (barRestrict S F)))
              (copowerReindex (stdSimplexPresheafMap' S θ) F.obj)
              (copowerReindex_copowerPresheafMap (stdSimplexPresheafMap' S θ)
                ((toPresheaf (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).obj
                  (barRestrict S F))
                (barCounitIso S F).hom))
            (square_map (presheafToSheaf S.totalTopology Ab.{u})
              (copowerStdSimplexIso S m F.obj) (copowerStdSimplexIso S n F.obj)
              (copowerReindex (stdSimplexPresheafMap' S θ) F.obj)
              (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).map θ.op)
              (copowerStdSimplexIso_simplexMap S θ F.obj)))))
  change ((barSimplicial' S).obj F).map θ.op ≫ (barTermIsoAux S n F).inv =
    (barTermIsoAux S m F).inv ≫ (integerTensorFace S θ).app F
  exact (Iso.comp_inv_eq (barTermIsoAux S n F)).2
    (((Category.assoc _ _ _).trans
      ((congrArg (fun t => (barTermIsoAux S m F).inv ≫ t) haux).trans
        (Iso.inv_hom_id_assoc _ _))).symm)

end Structure

/-! ### The augmentation on the tensor side -/

section Augmentation

variable (S : SimplicialSiteSituation.{u})

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-- The constant presheaf of types with value a point on the total category. -/
abbrev pointPresheaf : S.totalCategoryᵒᵖ ⥤ Type u :=
  (Functor.const S.totalCategoryᵒᵖ).obj PUnit.{u + 1}

/-- The free abelian presheaf on the one-point presheaf is the constant integer presheaf. -/
def pointFreeAbIso :
    pointPresheaf S ⋙ AddCommGrpCat.free.{u} ≅
      (Functor.const S.totalCategoryᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  freeAbPresheafConstIso' S.totalCategory ≪≫
    (Functor.const S.totalCategoryᵒᵖ).mapIso freeUnitIntegerIso'.{u}

/-- **The augmentation `g_{0!}ℤ ⟶ ℤ` of the integral resolution of Stacks 09WI**, read through
the identification of its degree-zero term with `g_{0!}ℤ`. -/
def integerAugmentation : componentIntegerSheaf S ⦋0⦌ ⟶ totalIntegerSheaf S :=
  (resolutionDegreeIso' S ⦋0⦌).inv ≫ resolutionAugmentation' S

/-- The copower of a presheaf of abelian groups by the one-point presheaf is that presheaf. -/
def copowerPointIsoApp (G : S.totalCategoryᵒᵖ ⥤ AddCommGrpCat.{u}) (X : S.totalCategoryᵒᵖ) :
    (copowerPresheafObj (pointPresheaf S) G).obj X ≅ G.obj X where
  hom := AddCommGrpCat.ofHom
    (Finsupp.liftAddHom (fun _ : PUnit.{u + 1} => AddMonoidHom.id (G.obj X : Type u)))
  inv := AddCommGrpCat.ofHom (Finsupp.singleAddHom (PUnit.unit : PUnit.{u + 1}))
  hom_inv_id := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro e m
    change Finsupp.single (PUnit.unit : PUnit.{u + 1})
        (Finsupp.liftAddHom (fun _ : PUnit.{u + 1} => AddMonoidHom.id (G.obj X : Type u))
          (Finsupp.single e m)) = Finsupp.single e m
    rw [Finsupp.liftAddHom_apply_single]
    rfl
  inv_hom_id := by
    apply AddCommGrpCat.hom_ext
    ext m
    change Finsupp.liftAddHom (fun _ : PUnit.{u + 1} => AddMonoidHom.id (G.obj X : Type u))
        (Finsupp.single (PUnit.unit : PUnit.{u + 1}) m) = m
    rw [Finsupp.liftAddHom_apply_single]
    rfl

/-- The copower of a presheaf of abelian groups by the one-point presheaf is that presheaf. -/
def copowerPointIso (G : S.totalCategoryᵒᵖ ⥤ AddCommGrpCat.{u}) :
    copowerPresheafObj (pointPresheaf S) G ≅ G :=
  NatIso.ofComponents (copowerPointIsoApp S G) (by
    intro X Y f
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro e m
    change AddCommGrpCat.Hom.hom (copowerPointIsoApp S G Y).hom
        (AddCommGrpCat.Hom.hom (copowerRestriction (pointPresheaf S) G f)
          (Finsupp.single e m)) =
      AddCommGrpCat.Hom.hom (G.map f)
        (AddCommGrpCat.Hom.hom (copowerPointIsoApp S G X).hom (Finsupp.single e m))
    rw [copowerRestriction_single]
    change Finsupp.liftAddHom (fun _ : PUnit.{u + 1} => AddMonoidHom.id (G.obj Y : Type u))
        (Finsupp.single _ (AddCommGrpCat.Hom.hom (G.map f) m)) =
      AddCommGrpCat.Hom.hom (G.map f)
        (Finsupp.liftAddHom (fun _ : PUnit.{u + 1} => AddMonoidHom.id (G.obj X : Type u))
          (Finsupp.single e m))
    rw [Finsupp.liftAddHom_apply_single, Finsupp.liftAddHom_apply_single]
    rfl)

/-- The value of the identification on the summand labelled by a point. -/
theorem copowerPointIso_hom_app_single (G : S.totalCategoryᵒᵖ ⥤ AddCommGrpCat.{u})
    (X : S.totalCategoryᵒᵖ) (e : PUnit.{u + 1}) (m : (G.obj X : Type u)) :
    AddCommGrpCat.Hom.hom ((copowerPointIso S G).hom.app X) (Finsupp.single e m) = m := by
  change Finsupp.liftAddHom (fun _ : PUnit.{u + 1} => AddMonoidHom.id (G.obj X : Type u))
      (Finsupp.single e m) = m
  rw [Finsupp.liftAddHom_apply_single]
  rfl

/-- The identification of the copower by a point with the presheaf itself is natural. -/
theorem copowerPointIso_naturality {G H : S.totalCategoryᵒᵖ ⥤ AddCommGrpCat.{u}} (β : G ⟶ H) :
    copowerPresheafMap (pointPresheaf S) β ≫ (copowerPointIso S H).hom =
      (copowerPointIso S G).hom ≫ β := by
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply Finsupp.addHom_ext
  intro e m
  change AddCommGrpCat.Hom.hom ((copowerPointIso S H).hom.app X)
      (AddCommGrpCat.Hom.hom ((copowerPresheafMap (pointPresheaf S) β).app X)
        (Finsupp.single e m)) =
    AddCommGrpCat.Hom.hom (β.app X)
      (AddCommGrpCat.Hom.hom ((copowerPointIso S G).hom.app X) (Finsupp.single e m))
  rw [copowerPresheafMap_app_single, copowerPointIso_hom_app_single,
    copowerPointIso_hom_app_single]

/-- The constant integer sheaf on the total site, presented as the sheafification of the free
presheaf of modules on the one-point presheaf. -/
def pointIntegerIso :
    (moduleEquivalence S.totalTopology).functor.obj
        ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
          (freeObj (pointPresheaf S))) ≅ totalIntegerSheaf S :=
  sheafifyFreeObjIso (intRingSheafScalars S.totalTopology) (pointPresheaf S) ≪≫
    (presheafToSheaf S.totalTopology Ab.{u}).mapIso (pointFreeAbIso S)

/-- The constant integer sheaf on the total site, read in sheaves of modules over the constant
sheaf of rings `ℤ`: it is the sheafification of the free presheaf of modules on a point. -/
def pointIntegerModuleIso :
    (moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S) ≅
      (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
        (freeObj (pointPresheaf S)) :=
  (moduleEquivalence S.totalTopology).inverse.mapIso (pointIntegerIso S).symm ≪≫
    ((moduleEquivalence S.totalTopology).unitIso.app
      ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
        (freeObj (pointPresheaf S)))).symm

/-- The value of the comparison of `ℤ` with the sheafified free presheaf of modules on a
point. -/
theorem pointIntegerModuleIso_hom :
    (pointIntegerModuleIso S).hom =
      (moduleEquivalence S.totalTopology).inverse.map (pointIntegerIso S).inv ≫
        ((moduleEquivalence S.totalTopology).unitIso.app
          ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
            (freeObj (pointPresheaf S)))).inv :=
  rfl

/-- The presentations of `g_{0!}ℤ` and of `ℤ` as sheafified free presheaves of modules are
compatible with the augmentation of the integral resolution. -/
theorem pointIntegerIso_augmentation :
    (moduleEquivalence S.totalTopology).functor.map
          ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).map
            ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map
              (stdSimplexPresheafToPoint' S ⦋0⦌))) ≫
        (pointIntegerIso S).hom =
      (componentIntegerSheafIsoSheafifyFreeModule S ⦋0⦌).hom ≫ integerAugmentation S := by
  refine square_comp (sheafifyFreeObjIso_naturality (stdSimplexPresheafToPoint' S ⦋0⦌)
    (intRingSheafScalars S.totalTopology)) ?_
  refine Eq.trans ((presheafToSheaf S.totalTopology Ab.{u}).map_comp _ _).symm ?_
  exact (Iso.hom_inv_id_assoc (resolutionDegreeIso' S ⦋0⦌) _).symm

/-- **The presentations of `g_{0!}ℤ` and of `ℤ` as sheafified free presheaves of modules are
compatible with the augmentation of the integral resolution**, in sheaves of modules over the
constant sheaf of rings `ℤ`. -/
theorem pointIntegerModuleIso_augmentation :
    (moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S) ≫
        (pointIntegerModuleIso S).hom =
      (componentIntegerModuleIso S ⦋0⦌).hom ≫
        (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).map
          ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map
            (stdSimplexPresheafToPoint' S ⦋0⦌)) := by
  rw [componentIntegerModuleIso_hom, pointIntegerModuleIso_hom]
  exact inverse_map_comp_unitIso_inv _ _ _ _ _ (pointIntegerIso_augmentation S)

/-- Tensoring with `ℤ` in sheaves of modules, as the sheafification of the objectwise tensor
product of the free presheaf of modules on a point with the sheaf being resolved. -/
def pointTensorIso (F : Sheaf S.totalTopology Ab.{u}) :
    (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).obj
        ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S),
          barModule S F) ≅
      (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
        (tensorObj (freeObj (pointPresheaf S)) (barRestrict S F)) :=
  (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).mapIso
      (Iso.prod (pointIntegerModuleIso S) (Iso.refl (barModule S F))) ≪≫
    tensorSheafifySecondIso.{u, u, u, u, u} S.totalTopology (intUnit S)
      (freeObj (pointPresheaf S)) (barModule S F)

/-- `pointTensorIso`, written out. -/
theorem pointTensorIso_hom (F : Sheaf S.totalTopology Ab.{u}) :
    (pointTensorIso S F).hom =
      (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map
          (CategoryTheory.Prod.mkHom (pointIntegerModuleIso S).hom (𝟙 (barModule S F))) ≫
        (tensorSheafifySecondIso.{u, u, u, u, u} S.totalTopology (intUnit S)
          (freeObj (pointPresheaf S)) (barModule S F)).hom :=
  rfl

/-- `pointTensorIso` is natural in the abelian sheaf being resolved. -/
theorem pointTensorIso_naturality {F G : Sheaf S.totalTopology Ab.{u}} (α : F ⟶ G) :
    (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map
          (CategoryTheory.Prod.mkHom
            (𝟙 ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
            (barModuleMap S α)) ≫
        (pointTensorIso S G).hom =
      (pointTensorIso S F).hom ≫
        (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).map
          (tensorHom (𝟙 (freeObj (pointPresheaf S)))
            ((restrictSheafFunctor.{u, u, u, u} S.totalTopology (intUnit S)).map
              (barModuleMap S α))) := by
  have hp : CategoryTheory.Prod.mkHom
        (𝟙 ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
        (barModuleMap S α) ≫
      CategoryTheory.Prod.mkHom (pointIntegerModuleIso S).hom (𝟙 (barModule S G)) =
    CategoryTheory.Prod.mkHom (pointIntegerModuleIso S).hom (𝟙 (barModule S F)) ≫
      CategoryTheory.Prod.mkHom
        (𝟙 ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
          (freeObj (pointPresheaf S)))) (barModuleMap S α) :=
    CategoryTheory.Prod.hom_ext
      ((Category.id_comp (pointIntegerModuleIso S).hom).trans
        (Category.comp_id (pointIntegerModuleIso S).hom).symm) (by simp)
  rw [pointTensorIso_hom, pointTensorIso_hom]
  refine square_comp ?_
    (tensorSheafifySecondIso_hom_naturality.{u, u, u, u, u} S.totalTopology (intUnit S)
      (freeObj (pointPresheaf S)) (barModuleMap S α))
  exact (((Functor.uncurry.obj
      (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map_comp _ _).symm.trans
    ((congrArg (Functor.uncurry.obj
        (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map hp).trans
      ((Functor.uncurry.obj
        (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map_comp _ _)))

/-- **The unit identification `ℤ ⊗_ℤ F ≅ F`** at a single abelian sheaf. -/
def unitTensorIsoAux (F : Sheaf S.totalTopology Ab.{u}) :
    (moduleEquivalence S.totalTopology).functor.obj
        ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).obj
          ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S),
            barModule S F)) ≅ F :=
  (moduleEquivalence S.totalTopology).functor.mapIso (pointTensorIso S F) ≪≫
    (sheafificationCompToSheaf (Sheaf.toRingCatMap S.totalTopology (intUnit S))).app
        (tensorObj (freeObj (pointPresheaf S)) (barRestrict S F)) ≪≫
      (presheafToSheaf S.totalTopology Ab.{u}).mapIso
          (freeTensorCopowerIso (pointPresheaf S) (intPresheaf S) (barRestrict S F)) ≪≫
        (presheafToSheaf S.totalTopology Ab.{u}).mapIso
            ((copowerPresheaf (pointPresheaf S)).mapIso (barCounitIso S F)) ≪≫
          (presheafToSheaf S.totalTopology Ab.{u}).mapIso (copowerPointIso S F.obj) ≪≫
            (@asIso _ _ _ _ _
              (isIso_sheafificationAdjunction_counit (J := S.totalTopology) (D := Ab.{u}) F))

/-- `unitTensorIsoAux`, written out. -/
theorem unitTensorIsoAux_hom (F : Sheaf S.totalTopology Ab.{u}) :
    (unitTensorIsoAux S F).hom =
      ((moduleEquivalence S.totalTopology).functor.mapIso (pointTensorIso S F)).hom ≫
        ((sheafificationCompToSheaf (Sheaf.toRingCatMap S.totalTopology (intUnit S))).app
            (tensorObj (freeObj (pointPresheaf S)) (barRestrict S F))).hom ≫
          ((presheafToSheaf S.totalTopology Ab.{u}).mapIso
              (freeTensorCopowerIso (pointPresheaf S) (intPresheaf S)
                (barRestrict S F))).hom ≫
            ((presheafToSheaf S.totalTopology Ab.{u}).mapIso
                ((copowerPresheaf (pointPresheaf S)).mapIso (barCounitIso S F))).hom ≫
              ((presheafToSheaf S.totalTopology Ab.{u}).mapIso
                  (copowerPointIso S F.obj)).hom ≫
                (sheafificationAdjunction S.totalTopology Ab.{u}).counit.app F :=
  rfl

/-- Tensoring with `ℤ` as an endofunctor of abelian sheaves on the total site. -/
abbrev unitIntegerTensorAb :
    Sheaf S.totalTopology Ab.{u} ⥤ Sheaf S.totalTopology Ab.{u} :=
  (moduleEquivalence S.totalTopology).inverse ⋙
    (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
      ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)) ⋙
    (moduleEquivalence S.totalTopology).functor

/-- Tensoring with `ℤ` as the tensor bifunctor of Stacks 0GMW with its left factor fixed. -/
theorem unitIntegerTensorAb_map_eq {F G : Sheaf S.totalTopology Ab.{u}} (α : F ⟶ G) :
    (unitIntegerTensorAb S).map α =
      (moduleEquivalence S.totalTopology).functor.map
        ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map
          (CategoryTheory.Prod.mkHom
            (𝟙 ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
            (barModuleMap S α))) :=
  congrArg (moduleEquivalence S.totalTopology).functor.map
    ((congrArg (· ≫ _) (congrArg (fun t => NatTrans.app t _)
      (CategoryTheory.Functor.map_id _ _))).trans (Category.id_comp _)).symm

/-- The unit identification is natural in the abelian sheaf. -/
theorem unitTensorIsoAux_naturality {F G : Sheaf S.totalTopology Ab.{u}} (α : F ⟶ G) :
    (unitIntegerTensorAb S).map α ≫ (unitTensorIsoAux S G).hom =
      (unitTensorIsoAux S F).hom ≫ α := by
  rw [unitTensorIsoAux_hom, unitTensorIsoAux_hom, unitIntegerTensorAb_map_eq]
  exact square_comp
    (square_map (moduleEquivalence S.totalTopology).functor _ _ _ _
      (pointTensorIso_naturality S α))
    (square_comp
      ((sheafificationCompToSheaf
        (Sheaf.toRingCatMap S.totalTopology (intUnit S))).hom.naturality
          (tensorHom (𝟙 (freeObj (pointPresheaf S)))
            ((restrictSheafFunctor.{u, u, u, u} S.totalTopology (intUnit S)).map
              (barModuleMap S α))))
      (square_comp
        (square_map (presheafToSheaf S.totalTopology Ab.{u}) _ _ _ _
          (freeTensorCopowerIso_naturality (pointPresheaf S) (intPresheaf S)
            ((restrictSheafFunctor.{u, u, u, u} S.totalTopology (intUnit S)).map
              (barModuleMap S α))))
        (square_comp
          (square_map (presheafToSheaf S.totalTopology Ab.{u}) _ _ _ _
            (square_map (copowerPresheaf (pointPresheaf S)) _ _ _ _
              (barCounitIso_naturality S α)))
          (square_comp
            (square_map (presheafToSheaf S.totalTopology Ab.{u}) _ _ _ _
              (copowerPointIso_naturality S
                ((sheafToPresheaf S.totalTopology Ab.{u}).map α)))
            ((sheafificationAdjunction S.totalTopology Ab.{u}).counit.naturality α)))))

/-- **The unit identification `ℤ ⊗_ℤ - ≅ 𝟭`**, as an isomorphism of endofunctors. -/
def unitTensorIso : unitIntegerTensorAb S ≅ 𝟭 (Sheaf S.totalTopology Ab.{u}) :=
  NatIso.ofComponents (unitTensorIsoAux S) (unitTensorIsoAux_naturality S)

/-- **The map `g_{0!}ℤ ⊗_ℤ F ⟶ F` induced by the augmentation of the integral resolution.** -/
def integerTensorAugmentation :
    integerTensorAb S ⦋0⦌ ⟶ 𝟭 (Sheaf S.totalTopology Ab.{u}) :=
  Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse
      (Functor.whiskerRight
        ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
          ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S)))
        (moduleEquivalence S.totalTopology).functor) ≫
    (unitTensorIso S).hom

/-- `integerTensorAugmentation`, at an abelian sheaf. -/
theorem integerTensorAugmentation_app (F : Sheaf S.totalTopology Ab.{u}) :
    (integerTensorAugmentation S).app F =
      (moduleEquivalence S.totalTopology).functor.map
          ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map
            (CategoryTheory.Prod.mkHom
              ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S))
              (𝟙 (barModule S F)))) ≫
        (unitTensorIsoAux S F).hom :=
  congrArg (· ≫ (unitTensorIsoAux S F).hom)
    (congrArg (moduleEquivalence S.totalTopology).functor.map
      ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)).symm)

/-- The augmentation of the simplex-coefficient presheaf sums the summands, and so does the
augmentation of the integral resolution read through the copower identifications. -/
theorem copowerPointIso_simplexCoefficientAugmentation (F : Sheaf S.totalTopology Ab.{u}) :
    copowerReindex (stdSimplexPresheafToPoint' S ⦋0⦌) F.obj ≫ (copowerPointIso S F.obj).hom =
      (copowerStdSimplexIso S ⦋0⦌ F.obj).hom ≫
        (simplexCoefficientAugmentation' (totalSimplexDegree S).leftOp F.obj).app
          (Opposite.op ⦋0⦌) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply Finsupp.addHom_ext
  intro x c
  have h1 := copowerReindex_app_single (stdSimplexPresheafToPoint' S ⦋0⦌) F.obj U x c
  have h2 := copowerPointIso_hom_app_single S F.obj U
    (ConcreteCategory.hom ((stdSimplexPresheafToPoint' S ⦋0⦌).app U) x) c
  have h3 := copowerStdSimplexIso_hom_app_single S ⦋0⦌ F.obj U x c
  have h4 : Limits.Sigma.ι
        (fun _ : ⦋0⦌ ⟶ (totalSimplexDegree S).leftOp.obj U => F.obj.obj U)
          (stdSimplexPresheafObjEquiv S ⦋0⦌ U x) ≫
      Limits.Sigma.desc (fun _ : ⦋0⦌ ⟶ (totalSimplexDegree S).leftOp.obj U =>
        𝟙 (F.obj.obj U)) = 𝟙 (F.obj.obj U) :=
    Limits.Sigma.ι_comp_desc _ _
  change AddCommGrpCat.Hom.hom ((copowerPointIso S F.obj).hom.app U)
      (AddCommGrpCat.Hom.hom ((copowerReindex (stdSimplexPresheafToPoint' S ⦋0⦌) F.obj).app U)
        (Finsupp.single x c)) =
    AddCommGrpCat.Hom.hom
      (Limits.Sigma.desc (fun _ : ⦋0⦌ ⟶ (totalSimplexDegree S).leftOp.obj U =>
        𝟙 (F.obj.obj U)))
      (AddCommGrpCat.Hom.hom ((copowerStdSimplexIso S ⦋0⦌ F.obj).hom.app U)
        (Finsupp.single x c))
  refine Eq.trans (congrArg (AddCommGrpCat.Hom.hom
    ((copowerPointIso S F.obj).hom.app U)) h1) ?_
  refine Eq.trans h2 ?_
  refine Eq.trans ?_ (congrArg (AddCommGrpCat.Hom.hom
    (Limits.Sigma.desc (fun _ : ⦋0⦌ ⟶ (totalSimplexDegree S).leftOp.obj U =>
      𝟙 (F.obj.obj U)))) h3).symm
  exact (congrArg (fun k => AddCommGrpCat.Hom.hom k c) h4).symm

/-- The sheafified presheaf-level augmentation, followed by the counit of the sheafification
adjunction, is the augmentation of the simplex-coefficient resolution. -/
theorem presheafAugmentation_comp_counit (F : Sheaf S.totalTopology Ab.{u}) :
    (presheafToSheaf S.totalTopology Ab.{u}).map
          ((simplexCoefficientAugmentation' (totalSimplexDegree S).leftOp F.obj).app
            (Opposite.op ⦋0⦌)) ≫
        (sheafificationAdjunction S.totalTopology Ab.{u}).counit.app F =
      barAugmentation' S F :=
  congrArg (fun t => t ≫ (sheafificationAdjunction S.totalTopology Ab.{u}).counit.app F)
    (Category.comp_id _).symm

/-- **`barTermIsoIntegerTensor` is compatible with the augmentation.** -/
theorem barTermIsoIntegerTensor_augmentation (F : Sheaf S.totalTopology Ab.{u}) :
    barAugmentation' S F =
      (barTermIsoIntegerTensor S ⦋0⦌).hom.app F ≫ (integerTensorAugmentation S).app F := by
  have hstep1 : (Functor.uncurry.obj
              (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology))).map
            (CategoryTheory.Prod.mkHom
              ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S))
              (𝟙 (barModule S F))) ≫
          (pointTensorIso S F).hom =
        (barTensorIso S ⦋0⦌ F).hom ≫
          (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).map
            (tensorHom
              ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map
                (stdSimplexPresheafToPoint' S ⦋0⦌)) (𝟙 (barRestrict S F))) := by
    rw [pointTensorIso_hom, barTensorIso_hom]
    exact tensor_map_comp_secondIso S _ _ _ _ F (pointIntegerModuleIso_augmentation S)
  have hlast : (presheafToSheaf S.totalTopology Ab.{u}).map
            (copowerReindex (stdSimplexPresheafToPoint' S ⦋0⦌) F.obj) ≫
          (((presheafToSheaf S.totalTopology Ab.{u}).mapIso
              (copowerPointIso S F.obj)).hom ≫
            (sheafificationAdjunction S.totalTopology Ab.{u}).counit.app F) =
        ((presheafToSheaf S.totalTopology Ab.{u}).mapIso
            (copowerStdSimplexIso S ⦋0⦌ F.obj)).hom ≫ barAugmentation' S F := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg
      (fun t => t ≫ (sheafificationAdjunction S.totalTopology Ab.{u}).counit.app F)
      (((presheafToSheaf S.totalTopology Ab.{u}).map_comp _ _).symm.trans
        ((congrArg (presheafToSheaf S.totalTopology Ab.{u}).map
          (copowerPointIso_simplexCoefficientAugmentation S F)).trans
          ((presheafToSheaf S.totalTopology Ab.{u}).map_comp _ _)))) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg
      (fun t => ((presheafToSheaf S.totalTopology Ab.{u}).mapIso
        (copowerStdSimplexIso S ⦋0⦌ F.obj)).hom ≫ t)
      (presheafAugmentation_comp_counit S F)
  have haux : (integerTensorAugmentation S).app F =
      (barTermIsoAux S ⦋0⦌ F).hom ≫ barAugmentation' S F := by
    rw [integerTensorAugmentation_app, unitTensorIsoAux_hom, barTermIsoAux_hom]
    exact square_comp
      (square_map (moduleEquivalence S.totalTopology).functor _ _ _ _ hstep1)
      (square_comp
        ((sheafificationCompToSheaf
          (Sheaf.toRingCatMap S.totalTopology (intUnit S))).hom.naturality
            (tensorHom
              ((free (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map
                (stdSimplexPresheafToPoint' S ⦋0⦌)) (𝟙 (barRestrict S F))))
        (square_comp
          (square_map (presheafToSheaf S.totalTopology Ab.{u}) _ _ _ _
            (freeTensorCopowerIso_reindex (stdSimplexPresheafToPoint' S ⦋0⦌) (intPresheaf S)
              (barRestrict S F)))
          (square_comp
            (square_map (presheafToSheaf S.totalTopology Ab.{u})
              ((copowerPresheaf (stdSimplexPresheaf' S ⦋0⦌)).mapIso (barCounitIso S F))
              ((copowerPresheaf (pointPresheaf S)).mapIso (barCounitIso S F))
              (copowerReindex (stdSimplexPresheafToPoint' S ⦋0⦌)
                ((toPresheaf (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).obj
                  (barRestrict S F)))
              (copowerReindex (stdSimplexPresheafToPoint' S ⦋0⦌) F.obj)
              (copowerReindex_copowerPresheafMap (stdSimplexPresheafToPoint' S ⦋0⦌)
                ((toPresheaf (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).obj
                  (barRestrict S F))
                (barCounitIso S F).hom))
            hlast)))
  rw [haux]
  change barAugmentation' S F =
    (barTermIsoAux S ⦋0⦌ F).inv ≫ (barTermIsoAux S ⦋0⦌ F).hom ≫ barAugmentation' S F
  rw [Iso.inv_hom_id_assoc]

end Augmentation

end CategoryTheory.SimplicialSiteSituation

end
