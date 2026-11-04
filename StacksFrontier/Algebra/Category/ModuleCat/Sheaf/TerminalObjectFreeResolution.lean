module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Category.ModuleCat.LeftResolution
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorByBaseModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalTypesComparison

/-!
# Free resolutions of globally presented modules over a site with a terminal object

Let `(C, J)` be a site with a terminal object `U₀`, let `O` be a sheaf of commutative rings on
it and write `A = O(U₀)`. The functor

  `M ↦ O ⊗_A M : ModuleCat A ⥤ SheafOfModules O`

(the constant presheaf with value `M`, extended along `A → O(U)` over each object `U`, then
sheafified) is left adjoint to the global sections `Γ(U₀, -)`. This file shows that, under the
two hypotheses the source uses in the proof of Stacks 07B3,

* `U₀` is quasi-compact (Stacks 090H), so that the global sections of a direct sum of copies of
  `O` are the direct sum of copies of `A` (Stacks 0738, in the form of Stacks 0935 (2)), and
* every object is covered by objects `U` over which `A → O(U)` is flat,

a module `H` with a global presentation `⊕_K O ⟶ ⊕_I O ⟶ H ⟶ 0` (Stacks 03DE) has a resolution
by direct sums of copies of `O`: there is a bounded above complex `F` whose terms are direct sums
of copies of `O`, with a quasi-isomorphism `F ⟶ H[0]`. This is the step

> Choose a resolution `… → F_1 → F_0 → M → 0` by free `A`-modules. The complex
> `… → O ⊗_A F_1 → O ⊗_A F_0 → H → 0` is a resolution of `H` by free `O`-modules because for
> each object `U/X` the structure morphism `U → X` is flat.

of the source, carried out on an arbitrary site.

## Main definitions

* `Stacks.TerminalFreeResolution.baseChangeFunctor`: the functor `M ↦ O ⊗_A M`.
* `Stacks.TerminalFreeResolution.globalSectionsFunctor`: the global sections `Γ(U₀, -)`, as
  `A`-modules.
* `Stacks.TerminalFreeResolution.baseChangeAdjunction`: the adjunction between them.

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits MonoidalCategory TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings Stacks.TensorByBaseModule

universe v u w

namespace Stacks.TerminalFreeResolution

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (O : Sheaf J CommRingCat.{w})
  {U₀ : C} (hU₀ : IsTerminal U₀)
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The ring of global sections `A = O(U₀)` over the terminal object, as a type. -/
abbrev baseRing (U₀ : C) : Type w := O.val.obj (op U₀)

/-- The morphism of presheaves of rings from the constant presheaf with value `A = O(U₀)` to
`O`, given over `U` by restriction along the unique map `U ⟶ U₀`. -/
abbrev baseCoefficientMap : constantRingPresheaf (C := C) (baseRing O U₀) ⟶ O.val :=
  coefficientMap (baseRing O U₀) hU₀ (RingHom.id _)

/-- The presheaf `U ↦ O(U) ⊗_A M`, as a functor of the `A`-module `M`. -/
def baseChangePresheafFunctor : ModuleCat.{w} (baseRing O U₀) ⥤ PMod O.val :=
  constantModulePresheaf (C := C) (baseRing O U₀) ⋙ changeOfRings (baseCoefficientMap O hU₀)

/-- **The functor `M ↦ O ⊗_A M`** from `A`-modules to sheaves of `O`-modules, where
`A = O(U₀)`: the presheaf `U ↦ O(U) ⊗_A M`, sheafified. -/
def baseChangeFunctor : ModuleCat.{w} (baseRing O U₀) ⥤ SheafOfModules.{w} (ringSheaf J O) :=
  baseChangePresheafFunctor O hU₀ ⋙ sheafify J O

/-- **The global sections `Γ(U₀, -)`** of a sheaf of `O`-modules over the terminal object, as a
module over `A = O(U₀)`: the right adjoint of `baseChangeFunctor`. -/
def globalSectionsFunctor :
    SheafOfModules.{w} (ringSheaf J O) ⥤ ModuleCat.{w} (baseRing O U₀) :=
  (SheafOfModules.forget (ringSheaf J O) ⋙
      PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)) ⋙
    restrictScalars (baseCoefficientMap O hU₀) ⋙
    PresheafOfModules.evaluation (ringPresheaf (constantRingPresheaf (C := C) (baseRing O U₀)))
      (op U₀)

/-- **`O ⊗_A (-)` is left adjoint to `Γ(U₀, -)`**: the composite of the adjunction between the
constant presheaf and evaluation at the terminal object, extension and restriction of scalars,
and sheafification. -/
def baseChangeAdjunction : baseChangeFunctor O hU₀ ⊣ globalSectionsFunctor O hU₀ :=
  (constantModulePresheafAdjunction (baseRing O U₀) hU₀).comp
    ((changeOfRingsAdjunction (baseCoefficientMap O hU₀)).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)))

/-- The global sections over the terminal object are additive, sectionwise. -/
instance globalSectionsFunctor_additive : (globalSectionsFunctor O hU₀).Additive where
  map_add := rfl

/-- The base change functor `O ⊗_A (-)` is a left adjoint. -/
instance baseChangeFunctor_isLeftAdjoint : (baseChangeFunctor O hU₀).IsLeftAdjoint :=
  (baseChangeAdjunction O hU₀).isLeftAdjoint

/-- The base change functor `O ⊗_A (-)` preserves `w`-small colimits. -/
instance baseChangeFunctor_preservesColimits :
    PreservesColimitsOfSize.{w, w} (baseChangeFunctor O hU₀) :=
  (baseChangeAdjunction O hU₀).leftAdjoint_preservesColimits

/-- The base change functor `O ⊗_A (-)` is additive. -/
instance baseChangeFunctor_additive : (baseChangeFunctor O hU₀).Additive :=
  (baseChangeAdjunction O hU₀).left_adjoint_additive

/-- **`O ⊗_A A = O`.** -/
def baseChangeFunctorUnitIso :
    (baseChangeFunctor O hU₀).obj (ModuleCat.of _ (baseRing O U₀)) ≅
      SheafOfModules.unit (ringSheaf J O) :=
  (sheafify J O).mapIso
      ((changeOfRings (baseCoefficientMap O hU₀)).mapIso (constantModuleUnitIso _) ≪≫
        changeOfRingsUnitIso _ J O (baseCoefficientMap O hU₀)) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).counit).app
      (SheafOfModules.unit (ringSheaf J O))

/-- The counit of an adjunction is invertible at `Y` as soon as the right adjoint is bijective
on morphisms out of `Y`. -/
lemma _root_.CategoryTheory.Adjunction.isIso_counit_app_of_bijective_map {D E : Type*}
    [Category D] [Category E] {F : D ⥤ E} {G : E ⥤ D} (adj : F ⊣ G) (Y : E)
    (h : ∀ T : E, Function.Bijective (G.map : (Y ⟶ T) → (G.obj Y ⟶ G.obj T))) :
    IsIso (adj.counit.app Y) := by
  refine isIso_of_coyoneda_map_bijective _ fun T => ?_
  have : (fun x : Y ⟶ T => adj.counit.app Y ≫ x) =
      (adj.homEquiv (G.obj Y) T).symm ∘ G.map := by
    funext x
    apply (adj.homEquiv (G.obj Y) T).injective
    simp [Adjunction.homEquiv_unit]
  have key := (adj.homEquiv (G.obj Y) T).symm.bijective.comp (h T)
  rwa [← this] at key

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- A section of a presheaf of modules over a site with a terminal object is determined by its
value over the terminal object. -/
lemma sections_val_eq_map (T : SheafOfModules.{w} (ringSheaf J O)) (s : T.sections) (X : Cᵒᵖ) :
    s.val X = T.val.map (hU₀.from X.unop).op (s.val (op U₀)) :=
  (PresheafOfModules.sections_property s (hU₀.from X.unop).op).symm

/-- The section of a presheaf of modules over a site with a terminal object generated by an
element over the terminal object. -/
def sectionOfTerminal (T : SheafOfModules.{w} (ringSheaf J O)) (t : T.val.obj (op U₀)) :
    T.sections :=
  PresheafOfModules.sectionsMk (fun X => T.val.map (hU₀.from X.unop).op t) fun X Y g => by
    rw [← PresheafOfModules.map_comp_apply, op_from_comp hU₀ g]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **`Γ(U₀, -)` is bijective on morphisms out of `O`**: a morphism `O ⟶ T` is a global section
of `T`, that is (the site having a terminal object) an element of `T(U₀)`, which is the same as
an `A`-linear map `A ⟶ T(U₀)`. -/
lemma bijective_globalSectionsFunctor_map_unit (T : SheafOfModules.{w} (ringSheaf J O)) :
    Function.Bijective ((globalSectionsFunctor O hU₀).map :
      (SheafOfModules.unit (ringSheaf J O) ⟶ T) → _) := by
  have hid : (hU₀.from U₀).op = 𝟙 (op U₀) := Quiver.Hom.unop_inj hU₀.from_self
  refine ⟨fun x y hxy => ?_, fun φ => ?_⟩
  · apply T.unitHomEquiv.injective
    refine PresheafOfModules.sections_ext _ _ fun X => ?_
    rw [sections_val_eq_map O hU₀ T _ X, sections_val_eq_map O hU₀ T (T.unitHomEquiv y) X]
    congr 1
    exact congrArg (fun φ => ModuleCat.Hom.hom φ (1 : O.val.obj (op U₀))) hxy
  · refine ⟨T.unitHomEquiv.symm (sectionOfTerminal O hU₀ T (φ.hom (1 : O.val.obj (op U₀)))), ?_⟩
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    have e1 (a : O.val.obj (op U₀)) : O.val.map (hU₀.from U₀).op a = a := by simp
    let one : (globalSectionsFunctor O hU₀).obj (SheafOfModules.unit (ringSheaf J O)) :=
      (1 : O.val.obj (op U₀))
    have key : ∀ m : (globalSectionsFunctor O hU₀).obj (SheafOfModules.unit (ringSheaf J O)),
        φ.hom m = ((show O.val.obj (op U₀) from m) •
          (show T.val.obj (op U₀) from φ.hom one) : T.val.obj (op U₀)) := by
      intro m
      have h := φ.hom.map_smul (show baseRing O U₀ from m) one
      refine Eq.trans ?_ (h.trans ?_)
      · congr 1
        show m = O.val.map (hU₀.from U₀).op (show O.val.obj (op U₀) from m) *
          (1 : O.val.obj (op U₀))
        rw [e1, mul_one]
      · show (O.val.map (hU₀.from U₀).op (show O.val.obj (op U₀) from m) •
          (show T.val.obj (op U₀) from φ.hom one) : T.val.obj (op U₀)) = _
        rw [e1]
    rw [key]
    show ((show O.val.obj (op U₀) from m) • (show T.val.obj (op U₀) from
      T.val.map (hU₀.from U₀).op (φ.hom one)) : T.val.obj (op U₀)) = _
    congr 1
    rw [hid, T.val.map_id]
    rfl

/-- The counit of an adjunction is invertible at the point of a colimiting cofan which the right
adjoint carries to a colimiting cofan, as soon as it is invertible at every summand. -/
lemma _root_.CategoryTheory.Adjunction.isIso_counit_app_of_isColimit_cofan {D E : Type*}
    [Category D] [Category E] {F : D ⥤ E} {G : E ⥤ D} (adj : F ⊣ G) {ι : Type*} {X : ι → E}
    (c : Cofan X) (hc : IsColimit c) (hGc : IsColimit (G.mapCocone c))
    (h : ∀ i, IsIso (adj.counit.app (X i))) : IsIso (adj.counit.app c.pt) := by
  refine adj.isIso_counit_app_of_bijective_map c.pt fun T => ⟨fun f g hfg => ?_, fun φ => ?_⟩
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    exact (adj.bijective_map_of_isIso_counit (Y' := T) (h i)).1 (by
      show G.map (c.inj i ≫ f) = G.map (c.inj i ≫ g)
      rw [G.map_comp, G.map_comp, hfg])
  · choose f hf using fun i => (adj.bijective_map_of_isIso_counit (Y' := T) (h i)).2
      (G.map (c.inj i) ≫ φ)
    refine ⟨Cofan.IsColimit.desc hc f, hGc.hom_ext fun ⟨i⟩ => ?_⟩
    show G.map (c.inj i) ≫ _ = G.map (c.inj i) ≫ φ
    rw [← G.map_comp, Cofan.IsColimit.fac]
    exact hf i

/-- **`Γ(U₀, O ⊗_A A) = A`**: the counit of `O ⊗_A (-) ⊣ Γ(U₀, -)` is invertible at `O`. -/
instance isIso_baseChangeAdjunction_counit_app_unit :
    IsIso ((baseChangeAdjunction O hU₀).counit.app (SheafOfModules.unit (ringSheaf J O))) :=
  (baseChangeAdjunction O hU₀).isIso_counit_app_of_bijective_map _
    (bijective_globalSectionsFunctor_map_unit O hU₀)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **Global sections over a quasi-compact terminal object preserve direct sums** (Stacks 0738,
in the form of Stacks 0935 (2)), read in `A`-modules. -/
lemma isColimit_globalSectionsFunctor_mapCocone (hqc : J.IsQuasiCompactObject U₀) {ι : Type w}
    {X : ι → SheafOfModules.{w} (ringSheaf J O)} (c : Cofan X) (hc : IsColimit c) :
    Nonempty (IsColimit ((globalSectionsFunctor O hU₀).mapCocone c)) := by
  have := Stacks.Sites.sheafOfModules_sections_preserves_coproducts J (ringSheaf J O) U₀ hqc ι
  exact ⟨isColimitOfReflects (forget₂ (ModuleCat.{w} (baseRing O U₀)) AddCommGrpCat.{w})
    (isColimitOfPreserves (SheafOfModules.toSheaf.{w} (ringSheaf J O) ⋙
      (sheafSections J AddCommGrpCat.{w}).obj (op U₀)) hc)⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **`O ⊗_A Γ(U₀, ⊕_I O) = ⊕_I O`** over a quasi-compact terminal object: the counit of
`O ⊗_A (-) ⊣ Γ(U₀, -)` is invertible at a direct sum of copies of `O`. -/
lemma isIso_baseChangeAdjunction_counit_app_of_cofan (hqc : J.IsQuasiCompactObject U₀)
    {ι : Type w} (c : Cofan fun _ : ι => SheafOfModules.unit (ringSheaf J O))
    (hc : IsColimit c) : IsIso ((baseChangeAdjunction O hU₀).counit.app c.pt) :=
  (baseChangeAdjunction O hU₀).isIso_counit_app_of_isColimit_cofan c hc
    (isColimit_globalSectionsFunctor_mapCocone O hU₀ hqc c hc).some fun _ => inferInstance

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- A direct sum of copies of `O`, presented by any colimiting cofan, makes a module free. -/
lemma isFree_of_isColimit_cofan {ι : Type w} {X : ι → SheafOfModules.{w} (ringSheaf J O)}
    (c : Cofan X) (hc : IsColimit c) (e : ∀ i, X i ≅ SheafOfModules.unit (ringSheaf J O)) :
    SheafOfModules.IsFree c.pt :=
  ⟨ι, fun i => (e i).inv ≫ c.inj i, ⟨mkCofanColimit _
    (fun s => Cofan.IsColimit.desc hc fun i => (e i).hom ≫ s.inj i)
    (fun s i => by simp)
    (fun s m hm => Cofan.IsColimit.hom_ext hc _ _ fun i => by
      rw [Cofan.IsColimit.fac, ← hm i]
      simp)⟩⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **`O ⊗_A A^{(X)} = ⊕_X O` is free.** -/
lemma isFree_baseChangeFunctor_obj_free (X : Type w) :
    SheafOfModules.IsFree
      ((baseChangeFunctor O hU₀).obj ((ModuleCat.free (baseRing O U₀)).obj X)) :=
  isFree_of_isColimit_cofan O (Cofan.mk _ fun x : X => (baseChangeFunctor O hU₀).map
      (ModuleCat.ofHom (Finsupp.lsingle x : baseRing O U₀ →ₗ[baseRing O U₀] (X →₀ _))))
    (isColimitCofanMkObjOfIsColimit (baseChangeFunctor O hU₀) _ _
      (ModuleCat.finsuppCoconeIsColimit (baseRing O U₀) (baseRing O U₀) X))
    fun _ => baseChangeFunctorUnitIso O hU₀

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **A globally presented module is `O ⊗_A M`** over a quasi-compact terminal object: if
`⊕_K O ⟶ ⊕_I O ⟶ H ⟶ 0` is a global presentation (Stacks 03DE), then `H ≅ O ⊗_A M` for the
cokernel `M` of the induced map `Γ(⊕_K O) ⟶ Γ(⊕_I O)` of `A`-modules. -/
lemma exists_baseChangeFunctor_obj_iso (hqc : J.IsQuasiCompactObject U₀)
    (H : SheafOfModules.{w} (ringSheaf J O)) (hH : H.IsPresentedByGlobalSections) :
    ∃ M : ModuleCat.{w} (baseRing O U₀), Nonempty ((baseChangeFunctor O hU₀).obj M ≅ H) := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcok⟩⟩ := hH
  have hεP : IsIso ((baseChangeAdjunction O hU₀).counit.app P) :=
    isIso_baseChangeAdjunction_counit_app_of_cofan O hU₀ hqc (Cofan.mk P ι) hP
  have hεQ : IsIso ((baseChangeAdjunction O hU₀).counit.app Q) :=
    isIso_baseChangeAdjunction_counit_app_of_cofan O hU₀ hqc (Cofan.mk Q κ) hQ
  refine ⟨cokernel ((globalSectionsFunctor O hU₀).map a), ⟨?_⟩⟩
  refine (asIso (cokernelComparison ((globalSectionsFunctor O hU₀).map a)
    (baseChangeFunctor O hU₀))).symm ≪≫ ?_
  refine cokernel.mapIso _ a (asIso ((baseChangeAdjunction O hU₀).counit.app Q))
    (asIso ((baseChangeAdjunction O hU₀).counit.app P))
    ((baseChangeAdjunction O hU₀).counit.naturality a) ≪≫ ?_
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel a) hcok

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- A morphism of presheaves of abelian groups which is injective over a family of objects
covering every object of the site is locally injective. -/
lemma isLocallyInjective_of_injective_app_of_generate_mem {F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (φ : F₁ ⟶ F₂) (𝒰 : C → Prop)
    (hcov : ∀ X : C, Sieve.generate (fun Z (_ : Z ⟶ X) => 𝒰 Z) ∈ J X)
    (hinj : ∀ Z, 𝒰 Z → Function.Injective (φ.app (op Z))) :
    Presheaf.IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y hxy := by
    refine J.superset_covering ?_ (hcov X.unop)
    rintro Y f ⟨Z, g, h, hZ, rfl⟩
    have hZ' : F₁.map h.op x = F₁.map h.op y := hinj Z hZ (by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy])
    show F₁.map (h.op ≫ g.op) x = F₁.map (h.op ≫ g.op) y
    rw [F₁.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hZ']

section Flat

variable (𝒰 : C → Prop) (hcov : ∀ X : C, Sieve.generate (fun Z (_ : Z ⟶ X) => 𝒰 Z) ∈ J X)
  (hflat : ∀ Z, 𝒰 Z → (O.val.map (hU₀.from Z).op).hom.Flat)

include hcov hflat

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **`O ⊗_A (-)` preserves monomorphisms** when every object is covered by objects `U` over
which `A → O(U)` is flat: the presheaf map `O(U) ⊗_A M' ⟶ O(U) ⊗_A M` is then injective over
those objects, hence locally injective, and sheafification turns a locally injective map into a
monomorphism. -/
lemma baseChangeFunctor_map_mono {M' M : ModuleCat.{w} (baseRing O U₀)} (f : M' ⟶ M)
    [Mono f] : Mono ((baseChangeFunctor O hU₀).map f) := by
  have hloc : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map ((baseChangePresheafFunctor O hU₀).map f)) := by
    refine isLocallyInjective_of_injective_app_of_generate_mem _ 𝒰 hcov fun Z hZ => ?_
    let := coefficientAlgebra (baseRing O U₀) hU₀ (RingHom.id _) (op Z)
    have : Module.Flat (baseRing O U₀) (O.val.obj (op Z)) := hflat Z hZ
    show Function.Injective (LinearMap.baseChange (O.val.obj (op Z)) f.hom)
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      ((ModuleCat.mono_iff_injective f).1 inferInstance)
  have : Sheaf.IsLocallyInjective ((SheafOfModules.toSheaf _).map
      ((baseChangeFunctor O hU₀).map f)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J _).2 hloc
  exact (SheafOfModules.toSheaf _).mono_of_mono_map (Sheaf.mono_of_isLocallyInjective _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **`O ⊗_A (-)` is exact** when every object is covered by objects `U` over which `A → O(U)`
is flat. -/
lemma baseChangeFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (baseChangeFunctor O hU₀) := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have := hS.mono_f
  refine ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).1 inferInstance S
    hS).1, baseChangeFunctor_map_mono O hU₀ 𝒰 hcov hflat S.f⟩

end Flat

/-! ### Free resolutions of modules -/

section FreeResolution

variable (A : Type w) [CommRing A]

/-- Every `A`-module is functorially a quotient of the free module on its underlying set: the
counit of `ModuleCat.free A ⊣ forget`. -/
def freeLeftResolution : Abelian.LeftResolution (𝟭 (ModuleCat.{w} A)) where
  F := forget (ModuleCat.{w} A) ⋙ ModuleCat.free A
  π := (ModuleCat.adj A).counit

/-- Every term of the resolution built from `freeLeftResolution` is a free module. -/
lemma exists_iso_free_freeLeftResolution_X (M : ModuleCat.{w} A) (n : ℕ) :
    ∃ Y : Type w, Nonempty (((freeLeftResolution A).chainComplex M).X n ≅
      (ModuleCat.free A).obj Y) := by
  rcases n with _ | _ | n
  · exact ⟨_, ⟨(freeLeftResolution A).chainComplexXZeroIso M⟩⟩
  · exact ⟨_, ⟨(freeLeftResolution A).chainComplexXOneIso M⟩⟩
  · exact ⟨_, ⟨(freeLeftResolution A).chainComplexXIso M n⟩⟩

/-- The augmentation `F_0 ⟶ M` of the free resolution. -/
def freeAugmentation (M : ModuleCat.{w} A) : ((freeLeftResolution A).chainComplex M).X 0 ⟶ M :=
  ((freeLeftResolution A).chainComplexXZeroIso M).hom ≫ (freeLeftResolution A).π.app M

/-- The differential `F_1 ⟶ F_0` of the free resolution is, up to the identifications of `F_1`
and `F_0`, the counit at the kernel of `F_0 ⟶ M` followed by the inclusion of that kernel. -/
lemma freeLeftResolution_d_one_zero_eq (M : ModuleCat.{w} A) :
    ((freeLeftResolution A).chainComplex M).d 1 0 =
      ((freeLeftResolution A).chainComplexXOneIso M).hom ≫
        (freeLeftResolution A).π.app (kernel ((freeLeftResolution A).π.app M)) ≫
          kernel.ι _ ≫ ((freeLeftResolution A).chainComplexXZeroIso M).inv :=
  (freeLeftResolution A).map_chainComplex_d_1_0 M

/-- The composite of the differential `F_1 ⟶ F_0` with the augmentation `F_0 ⟶ M` is zero. -/
lemma freeLeftResolution_d_one_zero_comp (M : ModuleCat.{w} A) :
    ((freeLeftResolution A).chainComplex M).d 1 0 ≫ freeAugmentation A M = 0 := by
  simp [freeLeftResolution_d_one_zero_eq, freeAugmentation]

/-- The free resolution is exact at degree zero, with `F_0 ⟶ M` surjective. -/
lemma exact_freeAugmentation (M : ModuleCat.{w} A) :
    (ShortComplex.mk _ _ (freeLeftResolution_d_one_zero_comp A M)).Exact ∧
      Epi (freeAugmentation A M) := by
  refine ⟨?_, by rw [freeAugmentation]; infer_instance⟩
  let φ : ShortComplex.mk _ _ (freeLeftResolution_d_one_zero_comp A M) ⟶
      ShortComplex.mk (kernel.ι ((freeLeftResolution A).π.app M)) _ (kernel.condition _) :=
    { τ₁ := ((freeLeftResolution A).chainComplexXOneIso M).hom ≫
        (freeLeftResolution A).π.app (kernel ((freeLeftResolution A).π.app M))
      τ₂ := ((freeLeftResolution A).chainComplexXZeroIso M).hom
      τ₃ := 𝟙 M
      comm₁₂ := by
        show (((freeLeftResolution A).chainComplexXOneIso M).hom ≫
          (freeLeftResolution A).π.app (kernel ((freeLeftResolution A).π.app M))) ≫
            kernel.ι ((freeLeftResolution A).π.app M) =
          ((freeLeftResolution A).chainComplex M).d 1 0 ≫
            ((freeLeftResolution A).chainComplexXZeroIso M).hom
        rw [freeLeftResolution_d_one_zero_eq]
        simp
      comm₂₃ := by
        show freeAugmentation A M ≫ 𝟙 M = _
        rw [Category.comp_id, freeAugmentation] }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

/-- **A resolution of an `A`-module by free `A`-modules**, as a projective resolution. -/
def freeProjectiveResolution (M : ModuleCat.{w} A) : ProjectiveResolution M where
  complex := (freeLeftResolution A).chainComplex M
  projective n := by
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_free_freeLeftResolution_X A M n
    exact Projective.of_iso e.symm inferInstance
  π := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨freeAugmentation A M, freeLeftResolution_d_one_zero_comp A M⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 (exact_freeAugmentation A M)
        refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
        · simp only [Iso.refl_hom]
          rfl
        · exact (Category.id_comp _).trans (Category.comp_id _).symm
      all_goals first
        | rfl
        | exact ((freeLeftResolution A).chainComplex M).shape 0 0 (by simp)
    · rw [quasiIsoAt_iff_exactAt']
      · exact (freeLeftResolution A).exactAt_map_chainComplex_succ M _
      · apply ChainComplex.exactAt_succ_single_obj⟩

end FreeResolution

/-! ### The free resolution of a globally presented module -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- A zero module is free, on the empty family. -/
lemma isFree_of_isZero {F : SheafOfModules.{w} (ringSheaf J O)} (h : IsZero F) : F.IsFree :=
  ⟨PEmpty, fun b => b.elim, ⟨mkCofanColimit _ (fun s => h.to_ s.pt) (fun _ b => b.elim)
    (fun _ _ _ => h.eq_of_src _ _)⟩⟩

variable (𝒰 : C → Prop) (hcov : ∀ X : C, Sieve.generate (fun Z (_ : Z ⟶ X) => 𝒰 Z) ∈ J X)
  (hflat : ∀ Z, 𝒰 Z → (O.val.map (hU₀.from Z).op).hom.Flat)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hU₀ hcov hflat in
/-- **A globally presented module has a resolution by free modules** over a site with a
quasi-compact terminal object `U₀` every object of which is covered by objects `U` over which
`O(U₀) → O(U)` is flat: there are a bounded above complex `F` all of whose terms are direct sums
of copies of `O`, and a quasi-isomorphism `F ⟶ H[0]`. This is the free resolution
`O ⊗_A F_• ⟶ H` of the proof of Stacks 07B3. -/
theorem exists_quasiIso_isFree_of_isPresentedByGlobalSections
    (hqc : J.IsQuasiCompactObject U₀) (H : SheafOfModules.{w} (ringSheaf J O))
    (hH : H.IsPresentedByGlobalSections) :
    ∃ (F : CochainComplex (SheafOfModules.{w} (ringSheaf J O)) ℤ)
      (π : F ⟶ (CochainComplex.singleFunctor _ 0).obj H),
      F.IsStrictlyLE 0 ∧ QuasiIso π ∧ ∀ n, (F.X n).IsFree := by
  obtain ⟨M, ⟨e⟩⟩ := exists_baseChangeFunctor_obj_iso O hU₀ hqc H hH
  have := baseChangeFunctor_preservesFiniteLimits O hU₀ 𝒰 hcov hflat
  let R := freeProjectiveResolution (baseRing O U₀) M
  have hzero (i : ℤ) (hi : 0 < i) :
      IsZero ((baseChangeFunctor O hU₀).obj (R.cochainComplex.X i)) :=
    (baseChangeFunctor O hU₀).map_isZero (R.cochainComplex.isZero_of_isStrictlyLE 0 i hi)
  refine ⟨((baseChangeFunctor O hU₀).mapHomologicalComplex _).obj R.cochainComplex,
    ((baseChangeFunctor O hU₀).mapHomologicalComplex _).map R.π' ≫
      (HomologicalComplex.singleMapHomologicalComplex (baseChangeFunctor O hU₀)
        (ComplexShape.up ℤ) 0).hom.app M ≫
      (CochainComplex.singleFunctor _ 0).map e.hom, ?_, ?_, fun n => ?_⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hzero i hi
  · infer_instance
  · by_cases hn : n ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k := ⟨n.natAbs, by omega⟩
      obtain ⟨Y, ⟨eY⟩⟩ := exists_iso_free_freeLeftResolution_X (baseRing O U₀) M k
      exact Stacks.Sheaves.QcohTypeComparison.isFree_of_iso
        ((baseChangeFunctor O hU₀).mapIso (R.cochainComplexXIso (-k) k ≪≫ eY))
        (isFree_baseChangeFunctor_obj_free O hU₀ Y)
    · exact isFree_of_isZero O (hzero n (by omega))

end Stacks.TerminalFreeResolution

end
