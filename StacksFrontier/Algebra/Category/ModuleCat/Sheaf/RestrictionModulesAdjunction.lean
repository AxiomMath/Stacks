module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction

/-!
# Restriction of sheaves of modules along a continuous functor, as a left adjoint

Let `G : C ⥤ D` be a continuous functor of sites whose restriction functor on sheaves of sets
`G^s = G.sheafPushforwardContinuous` has a right adjoint `P`, so that `(P, G^s)` is a morphism of
topoi `m : Sh(C) → Sh(D)` (for instance `G` continuous and cocontinuous, `P` the right Kan
extension). For a sheaf of rings `O` on `D`, restriction of sheaves of `O`-modules along `G` is
left adjoint to the direct image `m_*`, read over `O`, and the adjunction is the adjunction
`G^s ⊣ P` on underlying sheaves of sets: its unit and counit are the unit and counit of `G^s ⊣ P`.

The adjunction is the inverse-image adjunction of Stacks 03D3,
`Stacks.Sheaves.RingedToposModules.inverseImageAdjDirectImageModules`, transported along the
identification of the inverse image of a module with its restriction,
`Stacks.Sheaves.ToposPullback.restrictionModuleIso`. Both are the identity on underlying sheaves
of sets, which is what makes the unit and counit computable.

## Implementation notes

The direct image is computed over the inverse-image ring `inverseImageRingSheaf m O`, whose
underlying sheaf of sets is that of the restricted ring but whose ring structure is transported;
the two rings are isomorphic, not equal. Every statement below is therefore spelled with
underlying sheaves of sets over one ring at a time (the module over the restricted ring is read
through `SheafOfModules.restrictScalars` along `restrictionRingIso` whenever it meets the
direct image): unifying `moduleSheaf` over the two rings makes Lean compare the rings themselves,
which does not terminate in the heartbeat budget.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.restrictionMorphism`: the morphism of topoi `(P, G^s)`.
* `Stacks.Sheaves.RingedToposModules.restrictionModulesAdjunction`: restriction of sheaves of
  modules along `G` is left adjoint to the direct image along `restrictionMorphism`.

## Main results

* `Stacks.Sheaves.RingedToposModules.moduleAddObj_restrictionModules` and
  `.moduleSMulObj_restrictionModules`: the module operations of a restriction, transported along
  a further finite-product-preserving functor `P`, are those of the module transported along
  `G^s ⋙ P`.
* `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_restrictionModulesAdjunction_unit_app`
  and `..._counit_app`: the unit and counit are those of `G^s ⊣ P` on underlying sheaves of sets.

## References

* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.RingedToposModules

universe w v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w})]
  (G : C ⥤ D) [G.IsContinuous J K]
  {P : Sheaf J (Type w) ⥤ Sheaf K (Type w)} (adj : G.sheafPushforwardContinuous (Type w) J K ⊣ P)
  (O : Sheaf K RingCat.{w})

/-- The morphism of topoi whose inverse image is restriction along a continuous functor `G` and
whose direct image is a chosen right adjoint `P` of it. -/
noncomputable abbrev restrictionMorphism : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K
    (Type w)) where
  pushforward := P
  inverseImage := G.sheafPushforwardContinuous (Type w) J K
  adj := adj
  preservesFiniteLimits := inferInstance

section Operations

variable (M : SheafOfModules.{w} O)

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})] in
/-- Restriction along `G` carries the addition of a module to the addition of its restriction,
the two products being compared by the product comparison of `G^s`. -/
theorem sheafPushforwardContinuous_map_moduleAddHom :
    (G.sheafPushforwardContinuous (Type w) J K).map (Sheaf.moduleAddHom O M) =
      prodComparison (G.sheafPushforwardContinuous (Type w) J K) (Sheaf.moduleSheaf O M)
          (Sheaf.moduleSheaf O M) ≫
        Sheaf.moduleAddHom ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
          ((restrictionModules J K G O).obj M) := by
  refine Sheaf.hom_ext_sections fun X p => ?_
  have hL : (Sheaf.sectionsFunctor J X).map
        ((G.sheafPushforwardContinuous (Type w) J K).map (Sheaf.moduleAddHom O M)) p =
      (Sheaf.sectionsFunctor K (G.op.obj X)).map prod.fst p +
        (Sheaf.sectionsFunctor K (G.op.obj X)).map prod.snd p :=
    Eq.trans (congrArg ((Sheaf.sectionsFunctor K (G.op.obj X)).map (Sheaf.moduleAddHom O M))
      (Functor.prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor K (G.op.obj X)) p).symm)
      (Sheaf.sectionsFunctor_map_moduleAddHom O M _ _ _)
  have hR : (Sheaf.sectionsFunctor J X).map
        (prodComparison (G.sheafPushforwardContinuous (Type w) J K) (Sheaf.moduleSheaf O M)
            (Sheaf.moduleSheaf O M) ≫
          Sheaf.moduleAddHom ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
            ((restrictionModules J K G O).obj M)) p =
      (Sheaf.sectionsFunctor K (G.op.obj X)).map prod.fst p +
        (Sheaf.sectionsFunctor K (G.op.obj X)).map prod.snd p :=
    Eq.trans (congrArg ((Sheaf.sectionsFunctor J X).map
        (Sheaf.moduleAddHom ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
          ((restrictionModules J K G O).obj M)))
      (Functor.map_prodComparison_apply (P := Sheaf.sectionsFunctor J X)
        (G.sheafPushforwardContinuous (Type w) J K) _ _ p))
      (Sheaf.sectionsFunctor_map_moduleAddHom
        ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
        ((restrictionModules J K G O).obj M) X _ _)
  exact hL.trans hR.symm

/-- Restriction along `G` carries the scalar action of a module to the action of its
restriction over the restricted sheaf of rings. -/
theorem sheafPushforwardContinuous_map_moduleSMulHom :
    (G.sheafPushforwardContinuous (Type w) J K).map (Sheaf.moduleSMulHom O M) =
      prodComparison (G.sheafPushforwardContinuous (Type w) J K) (Sheaf.ringSheaf O)
          (Sheaf.moduleSheaf O M) ≫
        Sheaf.moduleSMulHom ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
          ((restrictionModules J K G O).obj M) := by
  refine Sheaf.hom_ext_sections fun X p => ?_
  have hL : (Sheaf.sectionsFunctor J X).map
        ((G.sheafPushforwardContinuous (Type w) J K).map (Sheaf.moduleSMulHom O M)) p =
      (Sheaf.sectionsFunctor K (G.op.obj X)).map prod.fst p •
        (Sheaf.sectionsFunctor K (G.op.obj X)).map prod.snd p :=
    Eq.trans (congrArg ((Sheaf.sectionsFunctor K (G.op.obj X)).map (Sheaf.moduleSMulHom O M))
      (Functor.prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor K (G.op.obj X)) p).symm)
      (Sheaf.sectionsFunctor_map_moduleSMulHom O M _ _ _)
  have hR : (Sheaf.sectionsFunctor J X).map
        (prodComparison (G.sheafPushforwardContinuous (Type w) J K) (Sheaf.ringSheaf O)
            (Sheaf.moduleSheaf O M) ≫
          Sheaf.moduleSMulHom ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
            ((restrictionModules J K G O).obj M)) p =
      (Sheaf.sectionsFunctor K (G.op.obj X)).map prod.fst p •
        (Sheaf.sectionsFunctor K (G.op.obj X)).map prod.snd p :=
    Eq.trans (congrArg ((Sheaf.sectionsFunctor J X).map
        (Sheaf.moduleSMulHom ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
          ((restrictionModules J K G O).obj M)))
      (Functor.map_prodComparison_apply (P := Sheaf.sectionsFunctor J X)
        (G.sheafPushforwardContinuous (Type w) J K) _ _ p))
      (Sheaf.sectionsFunctor_map_moduleSMulHom
        ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
        ((restrictionModules J K G O).obj M) X _ _)
  exact hL.trans hR.symm

universe t

variable (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})] in
/-- The addition of a module transported along `G^s ⋙ P` is the addition of its restriction
transported along `P`. -/
theorem moduleAddObj_restrictionModules
    (a b : P.obj (Sheaf.moduleSheaf ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
      ((restrictionModules J K G O).obj M))) :
    Sheaf.moduleAddObj O M (G.sheafPushforwardContinuous (Type w) J K ⋙ P) a b =
      Sheaf.moduleAddObj ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
        ((restrictionModules J K G O).obj M) P a b := by
  refine Eq.trans (congrArg
    (fun m => P.map m (Functor.prodObjMk (P := G.sheafPushforwardContinuous (Type w) J K ⋙ P)
      (A := Sheaf.moduleSheaf O M) (B := Sheaf.moduleSheaf O M) a b))
    (sheafPushforwardContinuous_map_moduleAddHom J K G O M)) ?_
  refine Eq.trans (P.map_comp_apply _ _ _) ?_
  refine congrArg
    (P.map (Sheaf.moduleAddHom ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
      ((restrictionModules J K G O).obj M))) ?_
  refine Eq.trans (Functor.map_prodComparison_apply (P := P)
    (G.sheafPushforwardContinuous (Type w) J K) _ _ _) ?_
  exact congrArg₂ Functor.prodObjMk
    (Functor.map_fst_prodObjMk (P := G.sheafPushforwardContinuous (Type w) J K ⋙ P)
      (A := Sheaf.moduleSheaf O M) (B := Sheaf.moduleSheaf O M) a b)
    (Functor.map_snd_prodObjMk (P := G.sheafPushforwardContinuous (Type w) J K ⋙ P)
      (A := Sheaf.moduleSheaf O M) (B := Sheaf.moduleSheaf O M) a b)

/-- The scalar action of a module transported along `G^s ⋙ P` is the action of its restriction
transported along `P`. -/
theorem moduleSMulObj_restrictionModules
    (r : P.obj (Sheaf.ringSheaf ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)))
    (a : P.obj (Sheaf.moduleSheaf ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
      ((restrictionModules J K G O).obj M))) :
    Sheaf.moduleSMulObj O M (G.sheafPushforwardContinuous (Type w) J K ⋙ P) r a =
      Sheaf.moduleSMulObj ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
        ((restrictionModules J K G O).obj M) P r a := by
  refine Eq.trans (congrArg
    (fun m => P.map m (Functor.prodObjMk (P := G.sheafPushforwardContinuous (Type w) J K ⋙ P)
      (A := Sheaf.ringSheaf O) (B := Sheaf.moduleSheaf O M) r a))
    (sheafPushforwardContinuous_map_moduleSMulHom J K G O M)) ?_
  refine Eq.trans (P.map_comp_apply _ _ _) ?_
  refine congrArg
    (P.map (Sheaf.moduleSMulHom ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)
      ((restrictionModules J K G O).obj M))) ?_
  refine Eq.trans (Functor.map_prodComparison_apply (P := P)
    (G.sheafPushforwardContinuous (Type w) J K) _ _ _) ?_
  exact congrArg₂ Functor.prodObjMk
    (Functor.map_fst_prodObjMk (P := G.sheafPushforwardContinuous (Type w) J K ⋙ P)
      (A := Sheaf.ringSheaf O) (B := Sheaf.moduleSheaf O M) r a)
    (Functor.map_snd_prodObjMk (P := G.sheafPushforwardContinuous (Type w) J K ⋙ P)
      (A := Sheaf.ringSheaf O) (B := Sheaf.moduleSheaf O M) r a)

end Operations

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The identification of the inverse image of a module with its restriction is the identity on
underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_restrictionModuleIso_hom_app (M : SheafOfModules.{w} O) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf (restrictionMorphism J K G adj) O)).map
        ((restrictionModuleIso J K G O).hom.app M) = 𝟙 _ :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- **Restriction of modules is left adjoint to the direct image**, as an equivalence of
morphism types: a morphism of `O|_C`-modules `M|_C ⟶ N` corresponds to a morphism of
`O`-modules `M ⟶ m_*N`, by the adjunction `G^s ⊣ P` on underlying sheaves of sets. -/
noncomputable def restrictionModulesHomEquiv (M : SheafOfModules.{w} O)
    (N : SheafOfModules.{w} ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)) :
    ((restrictionModules J K G O).obj M ⟶ N) ≃
      (M ⟶ (directImageModules (restrictionMorphism J K G adj) O).obj
        ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).obj N)) :=
  ((RingedPoint.restrictScalarsEquivalenceOfIso
        (restrictionRingIso J K G O)).fullyFaithfulInverse.homEquiv.trans
      ((Iso.homCongr ((restrictionModuleIso J K G O).app M) (Iso.refl _)).symm)).trans
    (toposModulesHomEquiv (restrictionMorphism J K G adj) O M
      ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).obj N))

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Restriction of scalars along the comparison of rings is injective on morphisms. -/
theorem restrictScalars_restrictionRingIso_map_injective
    {N N' : SheafOfModules.{w} ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)}
    {k k' : N ⟶ N'}
    (h : (SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).map k =
        (SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).map k') : k = k' :=
  (RingedPoint.restrictScalarsEquivalenceOfIso
    (restrictionRingIso J K G O)).fullyFaithfulInverse.map_injective h

/-- On underlying sheaves of sets, `restrictionModulesHomEquiv` is the adjunction `G^s ⊣ P`. -/
theorem moduleSheafFunctor_map_restrictionModulesHomEquiv (M : SheafOfModules.{w} O)
    (N : SheafOfModules.{w} ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O))
    (a : (restrictionModules J K G O).obj M ⟶ N) :
    (Sheaf.moduleSheafFunctor O).map (restrictionModulesHomEquiv J K G adj O M N a) =
      adj.homEquiv ((Sheaf.moduleSheafFunctor O).obj M)
        ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf (restrictionMorphism J K G adj) O)).obj
            ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).obj N))
        ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf (restrictionMorphism J K G adj) O)).map
            ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).map a)) := by
  refine (moduleSheafFunctor_map_toposModulesHomEquiv _ _ _).trans ?_
  exact congrArg (adj.homEquiv _ _) (Sheaf.hom_ext_sections fun _ _ ↦ rfl)

/-- On underlying sheaves of sets, the inverse of `restrictionModulesHomEquiv` is the inverse of
the adjunction `G^s ⊣ P`. -/
theorem moduleSheafFunctor_map_restrictionModulesHomEquiv_symm (M : SheafOfModules.{w} O)
    (N : SheafOfModules.{w} ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O))
    (b : M ⟶ (directImageModules (restrictionMorphism J K G adj) O).obj
        ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).obj N)) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf (restrictionMorphism J K G adj) O)).map
        ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).map
            ((restrictionModulesHomEquiv J K G adj O M N).symm b)) =
      (adj.homEquiv ((Sheaf.moduleSheafFunctor O).obj M)
        ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf (restrictionMorphism J K G adj) O)).obj
            ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).obj N))).symm
        ((Sheaf.moduleSheafFunctor O).map b) := by
  have h := moduleSheafFunctor_map_restrictionModulesHomEquiv J K G adj O M N
    ((restrictionModulesHomEquiv J K G adj O M N).symm b)
  rw [Equiv.apply_symm_apply] at h
  exact (Equiv.eq_symm_apply _).mpr h.symm

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- On underlying sheaves of sets, restriction of a morphism of modules along `G` is its
restriction as a morphism of sheaves of sets. -/
theorem moduleSheafFunctor_map_restrictionModules_map {M M' : SheafOfModules.{w} O}
    (g : M ⟶ M') :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf (restrictionMorphism J K G adj) O)).map
        ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).map
            ((restrictionModules J K G O).map g)) =
      (G.sheafPushforwardContinuous (Type w) J K).map ((Sheaf.moduleSheafFunctor O).map g) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- On underlying sheaves of sets, the direct image of a morphism of modules is `P` of it. -/
theorem moduleSheafFunctor_map_restrictionModulesRightAdjoint_map
    {N N' : SheafOfModules.{w} ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)}
    (k : N ⟶ N') :
    (Sheaf.moduleSheafFunctor O).map
        ((directImageModules (restrictionMorphism J K G adj) O).map
            ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).map k)) =
      P.map ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf
          (restrictionMorphism J K G adj) O)).map ((SheafOfModules.restrictScalars
              (restrictionRingIso J K G O).hom).map k)) :=
  moduleSheafFunctor_map_directImageModules_map (restrictionMorphism J K G adj) O _

/-- `restrictionModulesHomEquiv` is natural in the module being restricted. -/
theorem restrictionModulesHomEquiv_naturality_left_symm {M' M : SheafOfModules.{w} O}
    {N : SheafOfModules.{w} ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)}
    (g : M' ⟶ M)
    (β : M ⟶ (directImageModules (restrictionMorphism J K G adj) O).obj
        ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).obj N)) :
    (restrictionModulesHomEquiv J K G adj O M' N).symm (g ≫ β) =
      (restrictionModules J K G O).map g ≫ (restrictionModulesHomEquiv J K G adj O M N).symm β := by
  refine restrictScalars_restrictionRingIso_map_injective J K G O
    (hom_ext_moduleSheafFunctor ?_)
  rw [moduleSheafFunctor_map_restrictionModulesHomEquiv_symm, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleSheafFunctor_map_restrictionModulesHomEquiv_symm,
    moduleSheafFunctor_map_restrictionModules_map J K G adj O]
  exact adj.homEquiv_naturality_left_symm _ _

/-- `restrictionModulesHomEquiv` is natural in the module over the restricted ring. -/
theorem restrictionModulesHomEquiv_naturality_right {M : SheafOfModules.{w} O}
    {N N' : SheafOfModules.{w} ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)}
    (α : (restrictionModules J K G O).obj M ⟶ N) (k : N ⟶ N') :
    restrictionModulesHomEquiv J K G adj O M N' (α ≫ k) =
      restrictionModulesHomEquiv J K G adj O M N α ≫
        (directImageModules (restrictionMorphism J K G adj) O).map ((SheafOfModules.restrictScalars
            (restrictionRingIso J K G O).hom).map k) := by
  refine hom_ext_moduleSheafFunctor ?_
  rw [moduleSheafFunctor_map_restrictionModulesHomEquiv,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_restrictionModulesHomEquiv,
    moduleSheafFunctor_map_restrictionModulesRightAdjoint_map J K G adj O]
  exact adj.homEquiv_naturality_right _ _

/-- **Restriction of sheaves of modules along `G` is left adjoint to the direct image** along
the morphism of topoi `(P, G^s)`, read over `O`. Its unit and counit are those of `G^s ⊣ P` on
underlying sheaves of sets. -/
noncomputable def restrictionModulesAdjunction :
    restrictionModules J K G O ⊣ SheafOfModules.restrictScalars
        (restrictionRingIso J K G O).hom ⋙ directImageModules (restrictionMorphism J K G adj) O :=
  Adjunction.mkOfHomEquiv
    { homEquiv := restrictionModulesHomEquiv J K G adj O
      homEquiv_naturality_left_symm := restrictionModulesHomEquiv_naturality_left_symm J K G adj O
      homEquiv_naturality_right := restrictionModulesHomEquiv_naturality_right J K G adj O }

/-- The unit of `restrictionModulesAdjunction` is the unit of `G^s ⊣ P` on underlying sheaves of
sets. -/
theorem moduleSheafFunctor_map_restrictionModulesAdjunction_unit_app (M : SheafOfModules.{w} O) :
    (Sheaf.moduleSheafFunctor O).map ((restrictionModulesAdjunction J K G adj O).unit.app M) =
      adj.unit.app ((Sheaf.moduleSheafFunctor O).obj M) :=
  (moduleSheafFunctor_map_restrictionModulesHomEquiv J K G adj O M _ (𝟙 _)).trans
    (adj.homEquiv_id _)

/-- The counit of `restrictionModulesAdjunction` is the counit of `G^s ⊣ P` on underlying
sheaves of sets. -/
theorem moduleSheafFunctor_map_restrictionModulesAdjunction_counit_app
    (N : SheafOfModules.{w} ((G.sheafPushforwardContinuous RingCat.{w} J K).obj O)) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf (restrictionMorphism J K G adj) O)).map
        ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).map
            ((restrictionModulesAdjunction J K G adj O).counit.app N)) =
      adj.counit.app ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf
          (restrictionMorphism J K G adj) O)).obj ((SheafOfModules.restrictScalars
              (restrictionRingIso J K G O).hom).obj N)) :=
  (moduleSheafFunctor_map_restrictionModulesHomEquiv_symm J K G adj O _ N (𝟙 _)).trans
    (adj.homEquiv_symm_id _)

end Stacks.Sheaves.RingedToposModules

end
