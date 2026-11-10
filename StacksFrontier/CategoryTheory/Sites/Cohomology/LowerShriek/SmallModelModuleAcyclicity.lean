module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.EssentiallySmallModuleDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ModuleDerivedLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.Algebra.Homology.MapHomologicalComplexExactness

/-!
# The acyclicity input of Stacks 07AC for modules over essentially small sites

Let `f : C ⥤ D` be a continuous and cocontinuous functor of sites satisfying the covering-pullback
condition of Stacks 00WV, let `O_D` be a sheaf of commutative rings on `D` and set
`O_C = g^{-1} O_D`. The existence of the derived lower shriek `Lg_!` of Stacks 07AC reduces, by the
criterion of Stacks 0794, to one statement: `g_! : Mod(O_C) ⥤ Mod(O_D)` carries bounded above
acyclic complexes of direct sums of the `j_{U!} O_U` to acyclic complexes. For small sites in the
universe of the module sections this is
`Stacks.Cohomology.DerivedLowerShriek.lowerShriekModules_acyclic`, which rests on Stacks 0D6X.

The sites of algebraic stacks are only *essentially* small. This file proves the statement for
essentially small sites by transport to small models: the two sites are replaced by small models
with the induced topologies (`Stacks.SheafOfModules.SmallModelSite`), `f` by the induced functor of
models, which again satisfies the three hypotheses, and the two categories of modules by the
equivalent categories of modules on the models. The transport is exact, carries the `j_{U!} O_U`
to the corresponding objects on the model and intertwines the two lower-shriek functors, so the
small case applies.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.SmallModel.modelFunctor`: the functor induced on small
  models.
* `Stacks.Cohomology.DerivedLowerShriek.SmallModel.targetModulesEquivalence` and
  `Stacks.Cohomology.DerivedLowerShriek.SmallModel.sourceModulesEquivalence`: the equivalences of
  `Mod(O_D)` and `Mod(O_C)` with the categories of modules on the models.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.SmallModel.preservesCoveringPullbacks_modelFunctor`: the
  covering-pullback condition passes to the models.
* `Stacks.Cohomology.DerivedLowerShriek.SmallModel.restrictionModulesCompIso` and
  `Stacks.Cohomology.DerivedLowerShriek.SmallModel.lowerShriekModulesCompIso`: restriction and
  lower shriek commute with the transport.
* `Stacks.Cohomology.DerivedLowerShriek.SmallModel.sourceModulesEquivalenceExtensionByZeroUnitIso`:
  the transport carries `j_{U!} O_U` to `j_{U'!} O_{U'}`.
* `Stacks.Cohomology.DerivedLowerShriek.SmallModel.lowerShriekModules_acyclic_of_essentiallySmall`:
  the acyclicity statement over essentially small sites.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek.SmallModel

open Stacks.SheafOfModules.SmallModelSite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)

/-- The functor of sites `f` read on small models of its source and target. -/
abbrev modelFunctor : SmallModel.{w} C ⥤ SmallModel.{w} D :=
  (equivalence.{w} (C := C)).functor ⋙ f ⋙ (equivalence.{w} (C := D)).inverse

/-- The functor induced on small models is continuous for the induced topologies when `f` is
continuous. -/
instance modelFunctor_isContinuous [f.IsContinuous J K] :
    (modelFunctor f).IsContinuous (topology.{w} J) (topology.{w} K) :=
  have := Functor.isContinuous_comp f (equivalence.{w} (C := D)).inverse J K (topology.{w} K)
  Functor.isContinuous_comp (equivalence.{w} (C := C)).functor
    (f ⋙ (equivalence.{w} (C := D)).inverse) (topology.{w} J) J (topology.{w} K)

/-- The functor induced on small models is cocontinuous for the induced topologies when `f` is
cocontinuous. -/
instance modelFunctor_isCocontinuous [f.IsCocontinuous J K] :
    (modelFunctor f).IsCocontinuous (topology.{w} J) (topology.{w} K) :=
  have := isCocontinuous_comp f (equivalence.{w} (C := D)).inverse J K (L := topology.{w} K)
  isCocontinuous_comp (equivalence.{w} (C := C)).functor
    (f ⋙ (equivalence.{w} (C := D)).inverse) (topology.{w} J) J (L := topology.{w} K)

/-- **The covering-pullback clause of continuity passes to the small models.** If `f` satisfies
the covering-pullback condition of Stacks 00WV for `J`, so does the functor it induces between
small models of the two sites, for the induced topologies. -/
instance preservesCoveringPullbacks_modelFunctor [Stacks.Sites.PreservesCoveringPullbacks J f] :
    Stacks.Sites.PreservesCoveringPullbacks (topology.{w} J) (modelFunctor f) := by
  let e := equivalence.{w} (C := C)
  constructor
  intro U' S hS
  have hS' : S.functorPushforward e.functor ∈ J (e.functor.obj U') :=
    (Functor.functorPushforward_mem_iff (G := e.functor) (J := topology.{w} J) (K := J)).2 hS
  obtain ⟨R, hR, hRS, hpb⟩ := Stacks.Sites.PreservesCoveringPullbacks.exists_cover (u := f) _ _ hS'
  let R' : Presieve U' := fun V' h' => ∃ (V : C) (r : V ⟶ e.functor.obj U') (_ : R r)
    (a : e.functor.obj V' ≅ V), e.functor.map h' = a.hom ≫ r
  refine ⟨R', ?_, ?_, ?_⟩
  · refine (Functor.functorPushforward_mem_iff (G := e.functor) (J := topology.{w} J)
      (K := J)).1 (J.superset_covering ?_ hR)
    rintro Y g ⟨V, k, r, hr, rfl⟩
    let a : e.functor.obj (e.inverse.obj V) ≅ V := e.counitIso.app V
    let h' : e.inverse.obj V ⟶ U' := e.functor.preimage (a.hom ≫ r)
    refine ⟨e.inverse.obj V, h', k ≫ a.inv,
      Sieve.le_generate R' _ _ (show R' h' from ⟨V, r, hr, a, by simp [h']⟩), ?_⟩
    simp [h']
  · rintro V' h' ⟨V, r, hr, a, hh⟩
    obtain ⟨Z', s, k, hs, hk⟩ := hRS _ _ hr
    rw [show h' = e.functor.preimage (a.hom ≫ k) ≫ s from
      e.functor.map_injective (by simp [hh, hk])]
    exact S.downward_closed hs _
  · rintro V' h' ⟨V, r, hr, a, hh⟩ W' g'
    obtain ⟨hP, hpres⟩ := hpb r hr (e.functor.map g')
    let i : cospan (e.functor.map h') (e.functor.map g') ≅ cospan r (e.functor.map g') :=
      cospanExt a (Iso.refl _) (Iso.refl _) (by simp [hh]) (by simp)
    have : HasLimit (cospan h' g' ⋙ e.functor) :=
      hasLimit_of_iso (cospanCompIso e.functor h' g' ≪≫ i).symm
    refine ⟨Adjunction.hasLimit_of_comp_equivalence _ e.functor, ?_⟩
    have : PreservesLimit (cospan (e.functor.map h') (e.functor.map g')) f :=
      preservesLimit_of_iso_diagram f i.symm
    have : PreservesLimit (cospan h' g' ⋙ e.functor) f :=
      preservesLimit_of_iso_diagram f (cospanCompIso e.functor h' g').symm
    have : PreservesLimit (cospan h' g' ⋙ e.functor) (f ⋙ (equivalence.{w} (C := D)).inverse) :=
      inferInstance
    exact inferInstance

section Modules

variable [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K CommRingCat.{w})
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The structure sheaf of `D`, read as a sheaf of rings. -/
abbrev targetRing : Sheaf K RingCat.{w} := Stacks.SheafOfModules.Tensor.ringSheaf O

/-- The structure sheaf of the small model of `D`. -/
abbrev modelRing : Sheaf (topology.{w} K) CommRingCat.{w} := (ringedSite.{w} K O).O

/-- The comparison of the two functors from the small model of `C` to `D`: `f` after the model
equivalence of `C`, and the induced functor of models after the model equivalence of `D`. -/
def modelFunctorIso :
    (equivalence.{w} (C := C)).functor ⋙ f ≅ modelFunctor f ⋙ (equivalence.{w} (C := D)).functor :=
  NatIso.ofComponents
    (fun V => ((equivalence.{w} (C := D)).counitIso.app (f.obj
      ((equivalence.{w} (C := C)).functor.obj V))).symm)
    (fun g => by simp)

/-- The composite of the model equivalence of `C` with `f` is continuous. -/
instance : ((equivalence.{w} (C := C)).functor ⋙ f).IsContinuous (topology.{w} J) K :=
  Functor.isContinuous_comp _ _ _ J _

/-- The composite of the induced functor of models with the model equivalence of `D` is
continuous. -/
instance : (modelFunctor f ⋙ (equivalence.{w} (C := D)).functor).IsContinuous (topology.{w} J) K :=
  Functor.isContinuous_comp _ _ _ (topology.{w} K) _

/-- The two sheaves of rings on the small model of `C`: the transport of `O_C = f^{-1} O_D`
along the model equivalence, and the inverse image of the transported structure sheaf of `D`
along the induced functor of models. They are isomorphic through `modelFunctorIso`. -/
def modelRingIso :
    Stacks.SheafOfModules.reindexRing (topology.{w} J) (equivalence.{w} (C := C))
        (inverseImageRing J K f (targetRing K O)) ≅
      inverseImageRing (topology.{w} J) (topology.{w} K) (modelFunctor f)
        (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O)) :=
  (Functor.sheafPushforwardContinuousIso (modelFunctorIso f) RingCat.{w} (topology.{w} J) K).app
    (targetRing K O)

/-- **Sheaves of modules on `D` are sheaves of modules on its small model.** -/
def targetModulesEquivalence :
    SheafOfModules.{w} (targetRing K O) ≌
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O)) :=
  Stacks.SheafOfModules.reindexEquivalence (J' := topology.{w} K) (equivalence.{w} (C := D))
    (targetRing K O)

/-- The functor of the identity equivalence of the small model of `C` is continuous. -/
instance : (CategoryTheory.Equivalence.refl (C := SmallModel.{w} C)).functor.IsContinuous
    (topology.{w} J) (topology.{w} J) :=
  inferInstanceAs ((𝟭 (SmallModel.{w} C)).IsContinuous _ _)

/-- The inverse of the identity equivalence of the small model of `C` is continuous. -/
instance : (CategoryTheory.Equivalence.refl (C := SmallModel.{w} C)).inverse.IsContinuous
    (topology.{w} J) (topology.{w} J) :=
  inferInstanceAs ((𝟭 (SmallModel.{w} C)).IsContinuous _ _)

/-- **Sheaves of `O_C`-modules on `C` are sheaves of modules on the small model of `C` over the
inverse image of the transported structure sheaf of `D`**: transport along the model equivalence
of `C`, followed by restriction of scalars along `modelRingIso`. -/
def sourceModulesEquivalence :
    SheafOfModules.{w} (inverseImageRing J K f (targetRing K O)) ≌
      SheafOfModules.{w} (inverseImageRing (topology.{w} J) (topology.{w} K) (modelFunctor f)
        (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O))) :=
  (Stacks.SheafOfModules.reindexEquivalence (J' := topology.{w} J) (equivalence.{w} (C := C))
    (inverseImageRing J K f (targetRing K O))).trans
    (SheafOfModules.pushforwardPushforwardEquivalence
      (CategoryTheory.Equivalence.refl (C := SmallModel.{w} C))
      (modelRingIso J K f O).inv (modelRingIso J K f O).hom
      (by
        ext X : 2
        change (Stacks.SheafOfModules.reindexRing (topology.{w} J) (equivalence.{w} (C := C))
            (inverseImageRing J K f (targetRing K O))).obj.map (𝟙 X) =
          (targetRing K O).obj.map ((modelFunctorIso f).inv.app X.unop).op ≫
            (targetRing K O).obj.map ((modelFunctorIso f).hom.app X.unop).op
        rw [← CategoryTheory.Functor.map_comp, ← op_comp, Iso.hom_inv_id_app, op_id,
          CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
        rfl)
      (by
        ext X : 2
        change (targetRing K O).obj.map ((modelFunctorIso f).hom.app X.unop).op ≫
            (targetRing K O).obj.map ((modelFunctorIso f).inv.app X.unop).op ≫
            (inverseImageRing (topology.{w} J) (topology.{w} K) (modelFunctor f)
              (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O))).obj.map (𝟙 X) = 𝟙 _
        have h : (targetRing K O).obj.map ((modelFunctorIso f).hom.app X.unop).op ≫
            (targetRing K O).obj.map ((modelFunctorIso f).inv.app X.unop).op = 𝟙 _ := by
          rw [← CategoryTheory.Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id,
            CategoryTheory.Functor.map_id]
        rw [CategoryTheory.Functor.map_id]
        exact (Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans h)))

/-- **Restriction commutes with the transport to the small models.** Restricting a sheaf of
modules on `D` to `C` and transporting the result to the small model of `C` is isomorphic to
transporting it to the small model of `D` first and restricting along the induced functor of
models; the comparison is the action of `modelFunctorIso` on sections. -/
def restrictionModulesCompIso :
    restrictionModules J K f (targetRing K O) ⋙ (sourceModulesEquivalence J K f O).functor ≅
      (targetModulesEquivalence K O).functor ⋙
        restrictionModules (topology.{w} J) (topology.{w} K) (modelFunctor f)
          (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O)) :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
    (SheafOfModules.pushforwardComp.{w} (F := (equivalence.{w} (C := C)).functor) (G := f)
          (𝟙 (Stacks.SheafOfModules.reindexRing (topology.{w} J) (equivalence.{w} (C := C))
              (inverseImageRing J K f (targetRing K O))))
          (𝟙 (inverseImageRing J K f (targetRing K O)))) _ ≪≫
    (SheafOfModules.pushforwardComp.{w} (F := 𝟭 _) (G := (equivalence.{w} (C := C)).functor ⋙ f)
        (J := topology.{w} J) (K := topology.{w} J) (K' := K)
        (R := Stacks.SheafOfModules.reindexRing (topology.{w} J) (equivalence.{w} (C := C))
              (inverseImageRing J K f (targetRing K O)))
        (R' := targetRing K O) (modelRingIso J K f O).inv
        (𝟙 (Stacks.SheafOfModules.reindexRing (topology.{w} J) (equivalence.{w} (C := C))
              (inverseImageRing J K f (targetRing K O))) ≫
          ((equivalence.{w} (C := C)).functor.sheafPushforwardContinuous RingCat.{w}
            (topology.{w} J) J).map (𝟙 (inverseImageRing J K f (targetRing K O))))) ≪≫
    (SheafOfModules.pushforwardCongr₂.{w}
        (F := modelFunctor f ⋙ (equivalence.{w} (C := D)).functor)
        (G := 𝟭 _ ⋙ (equivalence.{w} (C := C)).functor ⋙ f) (S := targetRing K O)
        (φ := (modelRingIso J K f O).inv ≫
          ((𝟭 (SmallModel.{w} C)).sheafPushforwardContinuous RingCat.{w} (topology.{w} J)
              (topology.{w} J)).map
            (𝟙 (Stacks.SheafOfModules.reindexRing (topology.{w} J) (equivalence.{w} (C := C))
              (inverseImageRing J K f (targetRing K O))) ≫
              ((equivalence.{w} (C := C)).functor.sheafPushforwardContinuous RingCat.{w}
                (topology.{w} J) J).map (𝟙 (inverseImageRing J K f (targetRing K O)))))
        (ψ := 𝟙 (inverseImageRing (topology.{w} J) (topology.{w} K) (modelFunctor f)
              (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O))) ≫
            ((modelFunctor f).sheafPushforwardContinuous RingCat.{w} (topology.{w} J)
              (topology.{w} K)).map
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O))))
        (modelFunctorIso f).symm (by
          simp only [CategoryTheory.Functor.map_id, Category.comp_id]
          exact (modelRingIso J K f O).inv_hom_id)) ≪≫
    (SheafOfModules.pushforwardComp.{w} (F := modelFunctor f)
          (G := (equivalence.{w} (C := D)).functor)
          (𝟙 (inverseImageRing (topology.{w} J) (topology.{w} K) (modelFunctor f)
            (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O)))) (R' := targetRing K O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O)))).symm

section Transport

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.essentiallySmall_over

/-- The abelian structure on the sheaves of `O_C`-modules. -/
local instance abelianSourceModules :
    Abelian (SheafOfModules.{w} (inverseImageRing J K f (targetRing K O))) :=
  SheafOfModules.instAbelian _

/-- The abelian structure on the sheaves of `O_D`-modules. -/
local instance abelianTargetModules : Abelian (SheafOfModules.{w} (targetRing K O)) :=
  SheafOfModules.instAbelian _

/-- **Lower shriek commutes with the transport to the small models**: the left adjoints of the two
sides of `restrictionModulesCompIso` are isomorphic. -/
def lowerShriekModulesCompIso :
    lowerShriekModules J K f (targetRing K O) ⋙ (targetModulesEquivalence K O).functor ≅
      (sourceModulesEquivalence J K f O).functor ⋙
        lowerShriekModules (topology.{w} J) (topology.{w} K) (modelFunctor f)
          (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O)) := by
  set ΦC := sourceModulesEquivalence J K f O
  set ΦD := targetModulesEquivalence K O
  let adj₁ := (ΦC.symm.toAdjunction.comp (adjunctionModules J K f (targetRing K O))).comp
    ΦD.toAdjunction
  let e : ΦD.inverse ⋙ restrictionModules J K f (targetRing K O) ⋙ ΦC.functor ≅
      restrictionModules (topology.{w} J) (topology.{w} K) (modelFunctor f)
        (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O)) :=
    Functor.isoWhiskerLeft ΦD.inverse (restrictionModulesCompIso J K f O) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ΦD.counitIso _ ≪≫
      Functor.leftUnitor _
  let u := (adj₁.ofNatIsoRight e).leftAdjointUniq
    (adjunctionModules (topology.{w} J) (topology.{w} K) (modelFunctor f)
      (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O)))
  exact (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight ΦC.unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft ΦC.functor u

/-- **The transport to the small model of `C` carries `j_{U!} O_U` to `j_{U'!} O_{U'}`**, where
`U'` is the object of the small model corresponding to `U`. -/
def sourceModulesEquivalenceExtensionByZeroUnitIso (U : C) :
    (sourceModulesEquivalence J K f O).functor.obj
        (extensionByZeroUnit (inverseImageRing J K f (targetRing K O)) U) ≅
      extensionByZeroUnit (inverseImageRing (topology.{w} J) (topology.{w} K) (modelFunctor f)
        (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O)))
        ((equivalence.{w} (C := C)).inverse.obj U) :=
  let ΦC := sourceModulesEquivalence J K f O
  let R' := inverseImageRing (topology.{w} J) (topology.{w} K) (modelFunctor f)
    (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O))
  let U' := (equivalence.{w} (C := C)).inverse.obj U
  let X := extensionByZeroUnit (inverseImageRing J K f (targetRing K O)) U
  let eN : ∀ N : SheafOfModules.{w} R', (ΦC.functor.obj X ⟶ N) ≃ (N.val.obj (op U') : Type w) :=
    fun N => (ΦC.toAdjunction.homEquiv X N).trans
      (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv.{w} J _ U (ΦC.inverse.obj N))
  let c : coyoneda.obj (op (ΦC.functor.obj X)) ≅
      SheafOfModules.toSheaf R' ⋙ (sheafSections (topology.{w} J) AddCommGrpCat.{w}).obj (op U') ⋙
        forget AddCommGrpCat.{w} :=
    NatIso.ofComponents (fun N => Equiv.toIso (eN N))
      (fun {N N'} g => by
        ext φ
        change Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv.{w} J _ U _
            (ΦC.toAdjunction.homEquiv X N' (φ ≫ g)) =
          g.val.app (op U') (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv.{w} J _ U _
            (ΦC.toAdjunction.homEquiv X N φ))
        rw [Adjunction.homEquiv_naturality_right,
          Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality]
        rfl)
  (Coyoneda.fullyFaithful.preimageIso
    (c ≪≫ (extensionByZeroUnitCorepresentation (topology.{w} J) R' U').symm)).unop.symm

omit [f.IsCocontinuous J K] [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}] in
/-- The transport to the small model of `C` carries a direct sum of the `j_{U!} O_U` to a direct
sum of the `j_{U'!} O_{U'}`. -/
theorem isSumOfExtensionByZeroUnits_sourceModulesEquivalence_obj
    {M : SheafOfModules.{w} (inverseImageRing J K f (targetRing K O))}
    (hM : IsSumOfExtensionByZeroUnits (inverseImageRing J K f (targetRing K O)) M) :
    IsSumOfExtensionByZeroUnits (inverseImageRing (topology.{w} J) (topology.{w} K)
        (modelFunctor f) (Stacks.SheafOfModules.Tensor.ringSheaf (modelRing K O)))
      ((sourceModulesEquivalence J K f O).functor.obj M) := by
  obtain ⟨ι, U, ⟨e⟩⟩ := hM
  refine ⟨ι, fun i => (equivalence.{w} (C := C)).inverse.obj (U i), ⟨?_⟩⟩
  have : HasColimitsOfShape (Discrete ι)
      (PresheafOfModules.{w} (inverseImageRing J K f (targetRing K O)).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  have : HasColimitsOfShape (Discrete ι)
      (SheafOfModules.{w} (inverseImageRing J K f (targetRing K O))) := inferInstance
  exact (Sigma.mapIso fun i =>
      (sourceModulesEquivalenceExtensionByZeroUnitIso J K f O (U i)).symm) ≪≫
    (PreservesCoproduct.iso (sourceModulesEquivalence J K f O).functor _).symm ≪≫
    (sourceModulesEquivalence J K f O).functor.mapIso e

/-- A functor between preadditive categories with binary biproducts which preserves binary
coproducts is additive. -/
private theorem additive_of_preservesBinaryCoproducts {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] [HasBinaryBiproducts A] (F : A ⥤ B)
    [F.PreservesZeroMorphisms] [PreservesColimitsOfShape (Discrete WalkingPair) F] :
    F.Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact Functor.additive_of_preservesBinaryBiproducts _

omit [f.IsCocontinuous J K] [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The acyclicity statement of Stacks 07AC for modules, over essentially small sites.** For a
continuous and cocontinuous functor `f : C ⥤ D` of essentially small sites satisfying the
covering-pullback condition of Stacks 00WV, the lower-shriek functor
`g_! : Mod(O_C) ⥤ Mod(O_D)` carries every bounded above acyclic complex whose terms are direct
sums of the `j_{U!} O_U` to an acyclic complex. -/
theorem lowerShriekModules_acyclic_of_essentiallySmall
    [Stacks.Sites.PreservesCoveringPullbacks J f] (a : ℤ)
    (L : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f (targetRing K O))) ℤ)
    (hLE : L.IsStrictlyLE a)
    (hLP : ∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f (targetRing K O)) (L.X n))
    (hLac : L.Acyclic) :
    (((lowerShriekModules J K f (targetRing K O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).Acyclic := by
  let ΦC := sourceModulesEquivalence J K f O
  let ΦD := targetModulesEquivalence K O
  have := additive_of_preservesBinaryCoproducts ΦC.functor
  have := additive_of_preservesBinaryCoproducts ΦD.functor
  let L' := (ΦC.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have hLE' : CochainComplex.IsStrictlyLE L' a := by
    have := hLE
    infer_instance
  have hLac' : L'.Acyclic :=
    (HomologicalComplex.acyclic_map_iff_of_preservesHomology L ΦC.functor).2 hLac
  have h := lowerShriekModules_acyclic (topology.{w} J) (topology.{w} K) (modelFunctor f)
    (modelRing K O) a L' hLE'
    (fun n => isSumOfExtensionByZeroUnits_sourceModulesEquivalence_obj J K f O (hLP n)) hLac'
  have h' : ((ΦD.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((lowerShriekModules J K f (targetRing K O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)).Acyclic :=
    fun i => (h i).of_iso
      ((NatIso.mapHomologicalComplex (lowerShriekModulesCompIso J K f O) _).app L).symm
  exact (HomologicalComplex.acyclic_map_iff_of_preservesHomology _ ΦD.functor).1 h'

end Transport

end Modules

end Stacks.Cohomology.DerivedLowerShriek.SmallModel

end
