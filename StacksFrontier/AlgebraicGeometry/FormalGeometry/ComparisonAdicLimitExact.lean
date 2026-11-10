module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicArtinRees
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Exactness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHoms
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalComplement
public import StacksFrontier.CategoryTheory.Abelian.ShortExactReflectFaithful

/-!
# The limit of a tower of ideal-power quotients is exact in the middle

Let `X` be a Noetherian scheme, `J` a quasi-coherent ideal sheaf and `0 → F' → F → F'' → 0` a
short exact sequence of coherent modules. The towers `n ↦ F / Jⁿ F` have limits in the category
of modules, and a morphism from a coherent module into the limit of the middle tower which dies
in the limit of the third tower comes from the limit of the first.

This is not left exactness of a limit: the maps of the towers are not injective, and the
sequence of towers is exact only in the middle and on the right. The statement holds because
maps out of a coherent module into the limit of an adic tower are maps out of its completion,
and completion along `J` is an exact functor on coherent modules.

## Main results

* `Stacks.Algebraization.towerIso_hom_naturality_module` and
  `Stacks.Algebraization.adicLimitToCompletionLimit_naturality` — the identification of the
  tower of ideal-power quotients with the completion tower, and of their limits, is natural in
  the module.
* `Stacks.Algebraization.exists_limMap_adicQuotientSystemMap_eq` — **the limit of the towers is
  exact in the middle** on morphisms out of a coherent module.

## References

* [Stacks Project, Tag 0881](https://stacks.math.columbia.edu/tag/0881)
* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)

/-! ### The two towers are identified naturally in the module -/

/-- The identification of the `n`-th term of the completion with the `(n+1)`-st ideal-power
quotient is natural in the module. -/
theorem towerIso_hom_naturality_module
    {H K : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (φ : H ⟶ K)
    (n : ℕ) :
    ((completionFunctor X J).map φ).hom.app (op n) ≫ (NeighbourhoodHoms.towerIso J K n).hom =
      (NeighbourhoodHoms.towerIso J H n).hom ≫
        idealPowerQuotientMap J J (n + 1) (n + 1) le_rfl φ.hom := by
  have hepi : Epi (completionProjection X J H n) := epi_completionProjection X J H n
  refine (cancel_epi (completionProjection X J H n)).1 ?_
  have hL : completionProjection X J H n ≫
      (((completionFunctor X J).map φ).hom.app (op n) ≫
        (NeighbourhoodHoms.towerIso J K n).hom) =
      φ.hom ≫ cokernel.π (C := X.Modules) (idealPowerMultiple J (n + 1) K.obj).ι :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (NeighbourhoodHoms.towerIso J K n).hom)
          (completionFunctor_map_quotient X J φ n)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k => φ.hom ≫ k)
            (NeighbourhoodHoms.completionProjection_comp_towerIso J K n))))
  have hR : completionProjection X J H n ≫
      ((NeighbourhoodHoms.towerIso J H n).hom ≫
        idealPowerQuotientMap J J (n + 1) (n + 1) le_rfl φ.hom) =
      φ.hom ≫ cokernel.π (C := X.Modules) (idealPowerMultiple J (n + 1) K.obj).ι :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ idealPowerQuotientMap J J (n + 1) (n + 1) le_rfl φ.hom)
          (NeighbourhoodHoms.completionProjection_comp_towerIso J H n)).trans
        (idealPowerQuotientMap_π J J (n + 1) (n + 1) le_rfl φ.hom))
  exact hL.trans hR.symm

/-- The inverse form of `Stacks.Algebraization.towerIso_hom_naturality_module`. -/
theorem towerIso_inv_naturality_module
    {H K : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (φ : H ⟶ K)
    (n : ℕ) :
    (NeighbourhoodHoms.towerIso J H n).inv ≫
        ((completionFunctor X J).map φ).hom.app (op n) =
      idealPowerQuotientMap J J (n + 1) (n + 1) le_rfl φ.hom ≫
        (NeighbourhoodHoms.towerIso J K n).inv := by
  refine (cancel_mono (NeighbourhoodHoms.towerIso J K n).hom).1 ?_
  have hL : ((NeighbourhoodHoms.towerIso J H n).inv ≫
        ((completionFunctor X J).map φ).hom.app (op n)) ≫
        (NeighbourhoodHoms.towerIso J K n).hom =
      idealPowerQuotientMap J J (n + 1) (n + 1) le_rfl φ.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => (NeighbourhoodHoms.towerIso J H n).inv ≫ k)
          (towerIso_hom_naturality_module J φ n)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ idealPowerQuotientMap J J (n + 1) (n + 1) le_rfl φ.hom)
              (NeighbourhoodHoms.towerIso J H n).inv_hom_id).trans (Category.id_comp _))))
  have hR : (idealPowerQuotientMap J J (n + 1) (n + 1) le_rfl φ.hom ≫
        (NeighbourhoodHoms.towerIso J K n).inv) ≫
        (NeighbourhoodHoms.towerIso J K n).hom =
      idealPowerQuotientMap J J (n + 1) (n + 1) le_rfl φ.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => idealPowerQuotientMap J J (n + 1) (n + 1) le_rfl φ.hom ≫ k)
          (NeighbourhoodHoms.towerIso J K n).inv_hom_id).trans (Category.comp_id _))
  exact hL.trans hR.symm

/-- **The identification of the limits of the two towers is natural in the module.** -/
theorem adicLimitToCompletionLimit_naturality
    {H K : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (φ : H ⟶ K) :
    NeighbourhoodHoms.adicLimitToCompletionLimit J H ≫
        limMap ((completionFunctor X J).map φ).hom =
      limMap (adicQuotientSystemMap J φ.hom) ≫
        NeighbourhoodHoms.adicLimitToCompletionLimit J K := by
  refine limit.hom_ext fun n => ?_
  have hL : (NeighbourhoodHoms.adicLimitToCompletionLimit J H ≫
        limMap ((completionFunctor X J).map φ).hom) ≫
        limit.π ((completionFunctor X J).obj K).obj n =
      limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1)) ≫
        ((NeighbourhoodHoms.towerIso J H n.unop).inv ≫
          ((completionFunctor X J).map φ).hom.app n) := by
    rw [Category.assoc, limMap_π, ← Category.assoc,
      show NeighbourhoodHoms.adicLimitToCompletionLimit J H ≫
          limit.π ((completionFunctor X J).obj H).obj n =
        limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1)) ≫
          (NeighbourhoodHoms.towerIso J H n.unop).inv from
        limit.lift_π (NeighbourhoodHoms.adicLimitCone J H) n,
      Category.assoc]
  have hR : (limMap (adicQuotientSystemMap J φ.hom) ≫
        NeighbourhoodHoms.adicLimitToCompletionLimit J K) ≫
        limit.π ((completionFunctor X J).obj K).obj n =
      limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1)) ≫
        ((adicQuotientSystemMap J φ.hom).app (op (n.unop + 1)) ≫
          (NeighbourhoodHoms.towerIso J K n.unop).inv) := by
    rw [Category.assoc,
      show NeighbourhoodHoms.adicLimitToCompletionLimit J K ≫
          limit.π ((completionFunctor X J).obj K).obj n =
        limit.π (adicQuotientSystem J K.obj) (op (n.unop + 1)) ≫
          (NeighbourhoodHoms.towerIso J K n.unop).inv from
        limit.lift_π (NeighbourhoodHoms.adicLimitCone J K) n,
      ← Category.assoc, limMap_π, Category.assoc]
  refine hL.trans (Eq.trans ?_ hR.symm)
  exact congrArg (fun k => limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1)) ≫ k)
    (towerIso_inv_naturality_module J φ n.unop)

/-- The identification of the limit of the tower of ideal-power quotients with the limit of the
completion is natural in the module. -/
theorem adicCompletionLimitIso_hom_naturality
    {H K : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (φ : H ⟶ K) :
    (NeighbourhoodHoms.adicCompletionLimitIso J H).hom ≫
        limMap ((completionFunctor X J).map φ).hom =
      limMap (adicQuotientSystemMap J φ.hom) ≫
        (NeighbourhoodHoms.adicCompletionLimitIso J K).hom :=
  adicLimitToCompletionLimit_naturality J φ

/-! ### Maps out of a coherent module into the limit of an adic tower -/

/-- Postcomposing a map into the limit of a coherent adic system with a map of systems
corresponds, under the adjunction, to postcomposing the map out of the completion. -/
theorem homToAdicSystem_comp (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    {F G : Stacks.Coherent.CoherentAdicSystems J} (k : coherentObj P ⟶ limit F.obj)
    (ψ : F ⟶ G) :
    homToAdicSystem P F k ≫ ψ = homToAdicSystem P G (k ≫ limMap ψ.hom) := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
  have hepi : Epi (completionProjection X J P n.unop) := epi_completionProjection X J P n.unop
  refine (cancel_epi (completionProjection X J P n.unop)).1 ?_
  have hL : completionProjection X J P n.unop ≫
      ((homToAdicSystem P F k).hom.app n ≫ ψ.hom.app n) =
      (k ≫ limMap ψ.hom) ≫ limit.π G.obj n :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ ψ.hom.app n)
          (completionProjection_homToAdicSystem P F k n)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => k ≫ t) (limMap_π ψ.hom n).symm).trans
            (Category.assoc _ _ _).symm)))
  exact hL.trans (completionProjection_homToAdicSystem P G (k ≫ limMap ψ.hom) n).symm

/-- Postcomposing a map out of a completion with a map of systems corresponds, under the
adjunction, to postcomposing the map into the limit. -/
theorem adicSystemToHom_comp (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    {F G : Stacks.Coherent.CoherentAdicSystems J}
    (β : (completionFunctor X J).obj P ⟶ F) (ψ : F ⟶ G) :
    adicSystemToHom P F β ≫ limMap ψ.hom = adicSystemToHom P G (β ≫ ψ) := by
  refine limit.hom_ext fun n => ?_
  rw [Category.assoc, limMap_π, ← Category.assoc, adicSystemToHom_π, adicSystemToHom_π]
  exact Category.assoc _ _ _

/-! ### The limit of the towers is exact in the middle -/

omit [IsLocallyNoetherian X] in
/-- **The limits of the towers of ideal-power quotients of a short exact sequence of coherent
modules are exact in the middle**, on morphisms out of a coherent module: a morphism into the
limit of the middle tower whose composite into the limit of the third tower vanishes factors
through the limit of the first tower.

Maps out of a coherent module into the limit of an adic tower are maps out of its completion,
and completion is exact on coherent modules, so the factorization is the one through the kernel
of the completed sequence. -/
theorem exists_limMap_adicQuotientSystemMap_eq [IsNoetherian X]
    (S : ShortComplex (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf))
    (hS : S.ShortExact)
    (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (k : coherentObj P ⟶ limit (C := X.Modules) (adicQuotientSystem J S.X₂.obj))
    (hk : k ≫ limMap (adicQuotientSystemMap J S.g.hom) = 0) :
    ∃ l : coherentObj P ⟶ limit (C := X.Modules) (adicQuotientSystem J S.X₁.obj),
      l ≫ limMap (adicQuotientSystemMap J S.f.hom) = k := by
  obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff (completionFunctor X J)).1
    (completionFunctor_exact X J)
  have _ := hlim
  have _ := hcolim
  have hT : (S.map (completionFunctor X J)).ShortExact := hS.map_of_exact _
  have hmonoT : Mono (S.map (completionFunctor X J)).f := hT.mono_f
  have hk' : (k ≫ (NeighbourhoodHoms.adicCompletionLimitIso J S.X₂).hom) ≫
      limMap ((completionFunctor X J).map S.g).hom = 0 := by
    rw [Category.assoc, adicCompletionLimitIso_hom_naturality J S.g, ← Category.assoc, hk,
      zero_comp]
  have hα : homToAdicSystem P ((completionFunctor X J).obj S.X₂)
        (k ≫ (NeighbourhoodHoms.adicCompletionLimitIso J S.X₂).hom) ≫
      (S.map (completionFunctor X J)).g = 0 := by
    have h1 : homToAdicSystem P ((completionFunctor X J).obj S.X₂)
          (k ≫ (NeighbourhoodHoms.adicCompletionLimitIso J S.X₂).hom) ≫
        (completionFunctor X J).map S.g =
        homToAdicSystem P ((completionFunctor X J).obj S.X₃)
          ((k ≫ (NeighbourhoodHoms.adicCompletionLimitIso J S.X₂).hom) ≫
            limMap ((completionFunctor X J).map S.g).hom) :=
      homToAdicSystem_comp J P _ _
    have h2 : homToAdicSystem P ((completionFunctor X J).obj S.X₃)
        ((k ≫ (NeighbourhoodHoms.adicCompletionLimitIso J S.X₂).hom) ≫
          limMap ((completionFunctor X J).map S.g).hom) = 0 :=
      (congrArg (homToAdicSystem P ((completionFunctor X J).obj S.X₃)) hk').trans
        (map_zero (completionHomLimitEquiv P ((completionFunctor X J).obj S.X₃)))
    exact h1.trans h2
  obtain ⟨β, hβ⟩ : ∃ β : (completionFunctor X J).obj P ⟶ (completionFunctor X J).obj S.X₁,
      β ≫ (completionFunctor X J).map S.f =
        homToAdicSystem P ((completionFunctor X J).obj S.X₂)
          (k ≫ (NeighbourhoodHoms.adicCompletionLimitIso J S.X₂).hom) :=
    ⟨hT.exact.lift _ hα, hT.exact.lift_f _ hα⟩
  refine ⟨adicSystemToHom P ((completionFunctor X J).obj S.X₁) β ≫
    (NeighbourhoodHoms.adicCompletionLimitIso J S.X₁).inv, ?_⟩
  refine (cancel_mono (NeighbourhoodHoms.adicCompletionLimitIso J S.X₂).hom).1 ?_
  rw [Category.assoc, Category.assoc]
  have hinv : (NeighbourhoodHoms.adicCompletionLimitIso J S.X₁).inv ≫
      (limMap (adicQuotientSystemMap J S.f.hom) ≫
        (NeighbourhoodHoms.adicCompletionLimitIso J S.X₂).hom) =
      limMap ((completionFunctor X J).map S.f).hom :=
    (congrArg (fun t => (NeighbourhoodHoms.adicCompletionLimitIso J S.X₁).inv ≫ t)
        (adicCompletionLimitIso_hom_naturality J S.f).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ limMap ((completionFunctor X J).map S.f).hom)
            (NeighbourhoodHoms.adicCompletionLimitIso J S.X₁).inv_hom_id).trans
          (Category.id_comp _)))
  calc adicSystemToHom P ((completionFunctor X J).obj S.X₁) β ≫
        ((NeighbourhoodHoms.adicCompletionLimitIso J S.X₁).inv ≫
          (limMap (adicQuotientSystemMap J S.f.hom) ≫
            (NeighbourhoodHoms.adicCompletionLimitIso J S.X₂).hom))
      = adicSystemToHom P ((completionFunctor X J).obj S.X₁) β ≫
          limMap ((completionFunctor X J).map S.f).hom :=
        congrArg (fun t => adicSystemToHom P ((completionFunctor X J).obj S.X₁) β ≫ t) hinv
    _ = adicSystemToHom P ((completionFunctor X J).obj S.X₂)
          (β ≫ (completionFunctor X J).map S.f) :=
        adicSystemToHom_comp J P β ((completionFunctor X J).map S.f)
    _ = adicSystemToHom P ((completionFunctor X J).obj S.X₂)
          (homToAdicSystem P ((completionFunctor X J).obj S.X₂)
            (k ≫ (NeighbourhoodHoms.adicCompletionLimitIso J S.X₂).hom)) :=
        congrArg (adicSystemToHom P ((completionFunctor X J).obj S.X₂)) hβ
    _ = k ≫ (NeighbourhoodHoms.adicCompletionLimitIso J S.X₂).hom :=
        (completionHomLimitEquiv P ((completionFunctor X J).obj S.X₂)).symm_apply_apply _

/-! ### Global sections of the limit of a tower -/

omit [IsLocallyNoetherian X] in
/-- The identification of the global sections of the limit of a tower with the limit of the
global sections is the one determined by the projections. -/
theorem sectionsAbLimitIso_hom_π (D : ℕᵒᵖ ⥤ X.Modules) (n : ℕᵒᵖ) :
    (NeighbourhoodHoms.sectionsAbLimitIso D).hom ≫
        limit.π (D ⋙ NeighbourhoodHoms.sectionsAb X) n =
      (NeighbourhoodHoms.sectionsAb X).map (limit.π D n) := by
  have hsec : (NeighbourhoodHoms.sectionsLimitIso D).hom ≫
      limit.π (D ⋙ _root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))) n =
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
        (limit.π D n) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ n
  rw [NeighbourhoodHoms.sectionsAbLimitIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  exact (congrArg (fun t =>
        (forget₂ (ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) Ab.{u}).map
          (NeighbourhoodHoms.sectionsLimitIso D).hom ≫ t)
      (preservesLimitIso_hom_π
        (forget₂ (ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) Ab.{u}) _ n)).trans
    ((Functor.map_comp _ _ _).symm.trans
      (congrArg (forget₂ (ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) Ab.{u}).map
        hsec))

omit [IsLocallyNoetherian X] in
/-- The identification of the global sections of a limit with the limit of the global sections is
natural in the tower. -/
theorem sectionsAb_map_limMap_comp_sectionsAbLimitIso {D₁ D₂ : ℕᵒᵖ ⥤ X.Modules} (α : D₁ ⟶ D₂) :
    (NeighbourhoodHoms.sectionsAb X).map (limMap α) ≫
        (NeighbourhoodHoms.sectionsAbLimitIso D₂).hom =
      (NeighbourhoodHoms.sectionsAbLimitIso D₁).hom ≫
        limMap (Functor.whiskerRight α (NeighbourhoodHoms.sectionsAb X)) := by
  refine limit.hom_ext fun n => ?_
  rw [Category.assoc, sectionsAbLimitIso_hom_π, ← Functor.map_comp, limMap_π, Functor.map_comp,
    Category.assoc, limMap_π, ← Category.assoc, sectionsAbLimitIso_hom_π]
  rfl

/-! ### The inverse limits of global sections are exact in the middle -/

omit [IsLocallyNoetherian X] in
/-- The global section attached to the zero morphism out of the structure sheaf is zero. -/
theorem globalSectionOfHom_zero (M : _root_.SheafOfModules.{u} X.ringCatSheaf) :
    globalSectionOfHom M 0 = 0 := by
  change ((0 : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ M).val.app (op (⊤ : X.Opens)))
      (1 : X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) = 0
  rw [show (0 : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ M).val = 0 from rfl,
    PresheafOfModules.zero_app]
  rfl

omit [IsLocallyNoetherian X] in
/-- A morphism out of the structure sheaf is the one attached to the zero section once its own
global section vanishes. -/
theorem comp_eq_homOfGlobalSection_zero_of_app_eq_zero {M N : X.Modules} (ψ : M ⟶ N)
    (x : Γ(M, (⊤ : X.Opens))) (h : Scheme.Modules.Hom.app ψ ⊤ x = 0) :
    homOfGlobalSection M x ≫ ψ = homOfGlobalSection N 0 :=
  (homOfGlobalSection_globalSectionOfHom N (homOfGlobalSection M x ≫ ψ)).symm.trans
    (congrArg (homOfGlobalSection N)
      ((globalSectionOfHom_comp M (homOfGlobalSection M x) ψ).trans
        ((congrArg (Scheme.Modules.Hom.app ψ ⊤)
          (globalSectionOfHom_homOfGlobalSection M x)).trans h)))

omit [IsLocallyNoetherian X] in
/-- The map induced on global sections by a morphism of modules, read through the functor of
global sections in abelian groups. -/
theorem sectionsAb_map_apply {M N : X.Modules} (ψ : M ⟶ N) (x : Γ(M, (⊤ : X.Opens))) :
    ConcreteCategory.hom ((NeighbourhoodHoms.sectionsAb X).map ψ) x =
      Scheme.Modules.Hom.app ψ ⊤ x := rfl

omit [IsLocallyNoetherian X] in
/-- **The inverse limits of the global sections of the towers of ideal-power quotients of a short
exact sequence of coherent modules are exact in the middle.** A compatible family of global
sections of the quotients of the middle term whose image in the quotients of the third term
vanishes comes from one for the first term.

A compatible family of global sections of the tower is a global section of the limit of the
tower, hence a morphism out of the structure sheaf into that limit, where the statement is the
middle exactness of the limits of the towers. -/
theorem exists_limMap_whiskerRight_adicQuotientSystemMap_eq [IsNoetherian X]
    (S : ShortComplex (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf))
    (hS : S.ShortExact)
    (w : ToType (limit (adicQuotientSystem J S.X₂.obj ⋙ NeighbourhoodHoms.sectionsAb X)))
    (hw : ConcreteCategory.hom (limMap (Functor.whiskerRight
      (adicQuotientSystemMap J S.g.hom) (NeighbourhoodHoms.sectionsAb X))) w = 0) :
    ∃ v, ConcreteCategory.hom (limMap (Functor.whiskerRight
      (adicQuotientSystemMap J S.f.hom) (NeighbourhoodHoms.sectionsAb X))) v = w := by
  have hinv : ConcreteCategory.hom
      (NeighbourhoodHoms.sectionsAbLimitIso (adicQuotientSystem J S.X₂.obj)).hom
      (ConcreteCategory.hom
        (NeighbourhoodHoms.sectionsAbLimitIso (adicQuotientSystem J S.X₂.obj)).inv w) = w :=
    CategoryTheory.Iso.inv_hom_id_apply _ w
  have hw' : ConcreteCategory.hom
      ((NeighbourhoodHoms.sectionsAb X).map (limMap (adicQuotientSystemMap J S.g.hom)))
      (ConcreteCategory.hom
        (NeighbourhoodHoms.sectionsAbLimitIso (adicQuotientSystem J S.X₂.obj)).inv w) = 0 := by
    have hsq := ConcreteCategory.congr_hom
      (sectionsAb_map_limMap_comp_sectionsAbLimitIso (adicQuotientSystemMap J S.g.hom))
      (ConcreteCategory.hom
        (NeighbourhoodHoms.sectionsAbLimitIso (adicQuotientSystem J S.X₂.obj)).inv w)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hinv, hw] at hsq
    have hinj : Function.Injective (ConcreteCategory.hom
        (NeighbourhoodHoms.sectionsAbLimitIso (adicQuotientSystem J S.X₃.obj)).hom) :=
      ((ConcreteCategory.isIso_iff_bijective _).1 (Iso.isIso_hom _)).1
    exact hinj (hsq.trans (map_zero _).symm)
  have hz : globalSectionOfHom (limit (C := X.Modules) (adicQuotientSystem J S.X₃.obj))
      (0 : coherentObj (unitCoherentModule X) ⟶
        limit (C := X.Modules) (adicQuotientSystem J S.X₃.obj)) = 0 :=
    globalSectionOfHom_zero _
  obtain ⟨l, hl⟩ := exists_limMap_adicQuotientSystemMap_eq J S hS (unitCoherentModule X)
    (homOfGlobalSection _ (ConcreteCategory.hom
      (NeighbourhoodHoms.sectionsAbLimitIso (adicQuotientSystem J S.X₂.obj)).inv w))
    ((comp_eq_homOfGlobalSection_zero_of_app_eq_zero _ _ hw').trans
      ((congrArg (homOfGlobalSection _) hz.symm).trans
        (homOfGlobalSection_globalSectionOfHom _ _)))
  refine ⟨ConcreteCategory.hom
    (NeighbourhoodHoms.sectionsAbLimitIso (adicQuotientSystem J S.X₁.obj)).hom
    (globalSectionOfHom _ l), ?_⟩
  have hsq := ConcreteCategory.congr_hom
    (sectionsAb_map_limMap_comp_sectionsAbLimitIso (adicQuotientSystemMap J S.f.hom))
    (globalSectionOfHom (limit (C := X.Modules) (adicQuotientSystem J S.X₁.obj)) l)
  refine Eq.trans ((ConcreteCategory.comp_apply _ _ _).symm.trans
    (hsq.symm.trans (ConcreteCategory.comp_apply _ _ _))) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom
    (NeighbourhoodHoms.sectionsAbLimitIso (adicQuotientSystem J S.X₂.obj)).hom) ?_) hinv
  exact ((globalSectionOfHom_comp _ l (limMap (adicQuotientSystemMap J S.f.hom))).symm.trans
    (congrArg (globalSectionOfHom _) hl)).trans (globalSectionOfHom_homOfGlobalSection _ _)

/-! ### The bottom row of the ladder of a short exact sequence -/

section Neighbourhood

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)

/-- **The bottom row of the ladder of a short exact sequence of coherent modules on
`U = Spec(A) ∖ V(𝔞)` is exact in the middle.** A compatible family of sections of the quotients
`F / Iⁿ F` on `U` whose image in the quotients of `F''` vanishes comes from one for `F'`. -/
theorem exists_limMap_formalSectionsMap_eq
    (S : ShortComplex (complementZeroLocus A a : Scheme).Modules) (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (w : ToType (limit (formalSections A I a S.X₂)))
    (hw : ConcreteCategory.hom (limMap (formalSectionsMap A I a S.g)) w = 0) :
    ∃ v, ConcreteCategory.hom (limMap (formalSectionsMap A I a S.f)) v = w := by
  let P₁ : AlgebraicGeometry.SheafOfModules.CoherentModules
      (complementZeroLocus A a : Scheme).ringCatSheaf := ⟨S.X₁, ‹_›⟩
  let P₂ : AlgebraicGeometry.SheafOfModules.CoherentModules
      (complementZeroLocus A a : Scheme).ringCatSheaf := ⟨S.X₂, ‹_›⟩
  let P₃ : AlgebraicGeometry.SheafOfModules.CoherentModules
      (complementZeroLocus A a : Scheme).ringCatSheaf := ⟨S.X₃, ‹_›⟩
  let Scoh : ShortComplex
      (AlgebraicGeometry.SheafOfModules.CoherentModules
        (complementZeroLocus A a : Scheme).ringCatSheaf) :=
    ShortComplex.mk (ObjectProperty.homMk S.f : P₁ ⟶ P₂)
      (ObjectProperty.homMk S.g : P₂ ⟶ P₃) (ObjectProperty.hom_ext _ S.zero)
  have hScoh : Scoh.ShortExact :=
    ShortComplex.shortExact_of_shortExact_map
      (ObjectProperty.ι
        (fun M : _root_.SheafOfModules.{u} (complementZeroLocus A a : Scheme).ringCatSheaf =>
          M.IsCoherent)) hS
  exact exists_limMap_whiskerRight_adicQuotientSystemMap_eq
    (idealSheafNearVanishing A I a) Scoh hScoh w hw

end Neighbourhood

end Stacks.Algebraization
