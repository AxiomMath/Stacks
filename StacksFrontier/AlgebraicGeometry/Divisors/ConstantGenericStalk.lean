module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsComparisonMap
public import StacksFrontier.Topology.Sheaves.Sheaf.Constant

/-!
# The constant sheaf of modules on the stalk at the generic point

Let `X` be an integral scheme and `F` a sheaf of `𝒪_X`-modules. The function field `R(X)` is
the stalk of `𝒪_X` at the generic point, and the stalk `F_η` is a module over it. This file
builds the constant sheaf of `R(X)`-modules with value `F_η` — a sheaf of modules over the
constant sheaf of rings on `R(X)`, which by Tag 01X5 part (1) is the sheaf of meromorphic
functions — and shows that its global sections are exactly the constant ones.

That last statement is the input the order of vanishing of a meromorphic section needs: a
meromorphic section of `F` on an integral scheme is one element of `F_η`, determined uniquely.

## Main definitions

* `AlgebraicGeometry.constantGenericStalkModuleSheaf`: the constant sheaf of modules on the
  stalk of `F` at the generic point, over the constant sheaf of rings on the function field.
* `AlgebraicGeometry.constantGenericStalkModuleSection`: the constant section of that sheaf
  determined by an element of the stalk at the generic point.

## Main results

* `AlgebraicGeometry.exists_eq_constantSheafOnSpace_section`: on an integral scheme a section
  of a constant sheaf of commutative rings over a nonempty open is constant.
* `AlgebraicGeometry.constantSheafOnSpaceSectionRingEquiv`: therefore the sections of that
  sheaf over a nonempty open are the value ring itself.
* `AlgebraicGeometry.exists_unique_eq_constantGenericStalkModuleSection`: a global section of
  the constant generic-stalk module sheaf is the constant section of a unique element of the
  stalk at the generic point.

## Implementation notes

The constant sheaf of modules is built as in Tag 01X5: the constant presheaf of modules on
`F_η` over the constant presheaf of rings on `R(X)` is pushed along the sheafification unit of
that presheaf of rings by extension of scalars, and then sheafified. Its sections over `U` thus
receive `𝒪(U) ⊗_{R(X)} F_η` where `𝒪` is the constant *sheaf* on `R(X)`; the constant section
is the image of `1 ⊗ m`.

Everything is read off from two facts about sheafification: the unit is an isomorphism on every
stalk, and on an integral scheme the generic point lies in every nonempty open, so that a
germ at the generic point already determines a section. The first gives, locally around each
point, a representative of the shape `1 ⊗ m`; the second, applied at the generic point, shows
that the element `m` is the same for all of them. Injectivity of `m ↦ 1 ⊗ m` comes from the
evaluation `𝒪(U) ⊗_{R(X)} F_η → F_η` obtained from the ring isomorphism
`R(X) ≃+* 𝒪(U)`.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 006W](https://stacks.math.columbia.edu/tag/006W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Sections of a constant sheaf of rings on an integral scheme -/

/-- A section on an integral scheme which locally agrees, near every point, with a section from a
compatible family `c`, with `c` injective on germs at the generic point, is itself from `c`. -/
private theorem exists_eq_of_germ_eq_generic {X : Scheme.{u}} [IsIntegral X]
    {A : Type*} [Category.{u} A] {FC : A → A → Type*} {CC : A → Type u}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} A FC]
    [HasLimits A] [HasColimits A] [PreservesLimits (forget A)]
    [PreservesFilteredColimits (forget A)]
    [(forget A).ReflectsIsomorphisms]
    {S : TopCat.Presheaf A X} (hS : S.IsSheaf) {ι : Type*}
    (c : ∀ V : X.Opens, ι → ToType (S.obj (op V)))
    (hres : ∀ {U V : X.Opens} (h : V ≤ U) (a : ι),
      ConcreteCategory.hom (S.map (homOfLE h).op) (c U a) = c V a)
    (hinj : ∀ {V W : X.Opens} (hV : genericPoint X ∈ V) (hW : genericPoint X ∈ W) (a b : ι),
      S.germ V _ hV (c V a) = S.germ W _ hW (c W b) → a = b)
    {U : X.Opens} (hU : Nonempty U) (s : ToType (S.obj (op U)))
    (hloc : ∀ (x : X) (hx : x ∈ U), ∃ (V : X.Opens) (_ : V ≤ U) (hV : x ∈ V) (a : ι),
      S.germ U x hx s = S.germ V x hV (c V a)) :
    ∃ a : ι, s = c U a := by
  have hmem : ∀ (V : X.Opens) {x : X}, x ∈ V → genericPoint X ∈ V := fun V x hx =>
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 ⟨x, ⟨Set.mem_univ _, hx⟩⟩
  obtain ⟨x₀, hx₀⟩ := hU
  have hηU := hmem U hx₀
  obtain ⟨Vη, -, hVηgen, aη, hgeneric⟩ := hloc _ hηU
  refine ⟨aη, hS.section_ext fun x hx => ?_⟩
  obtain ⟨V, hVU, hV, a, ha⟩ := hloc x hx
  have hVη := hmem V hV
  have hspec := congrArg (ConcreteCategory.hom (S.stalkSpecializes
    (genericPoint_specializes x))) ha
  have hspec' : S.germ U _ hηU s = S.germ V _ hVη (c V a) := by
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      TopCat.Presheaf.germ_stalkSpecializes, TopCat.Presheaf.germ_stalkSpecializes] at hspec
  obtain rfl := hinj hVηgen hVη aη a (hgeneric.symm.trans hspec')
  obtain ⟨W, hW, iWU, iWU', heq⟩ := TopCat.Presheaf.germ_eq S x hx hx s (c U aη)
    (ha.trans (by rw [← hres hVU, TopCat.Presheaf.germ_res_apply]))
  exact ⟨W, iWU.le, hW, by rwa [Subsingleton.elim iWU iWU'] at heq⟩

section ConstantRingSheaf

variable (X : Scheme.{u}) [IsIntegral X] (A : CommRingCat.{u})

omit [IsIntegral X] in
/-- Near any point, a section of the constant sheaf with value `A` agrees with the constant
section of an element of `A`. -/
private theorem exists_germ_eq_constantSheafOnSpace_section (U : X.Opens)
    (s : (constantSheafOnSpace X CommRingCat.{u} A).obj.obj (op U)) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (_ : V ≤ U) (hV : x ∈ V) (a : A),
      TopCat.Presheaf.germ (constantSheafOnSpace X CommRingCat.{u} A).obj U x hx s =
        TopCat.Presheaf.germ (constantSheafOnSpace X CommRingCat.{u} A).obj V x hV
          (((toSheafify (Opens.grothendieckTopology X)
            ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op V)).hom a) := by
  let P : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
  let α : P ⟶ (constantSheafOnSpace X CommRingCat.{u} A).obj :=
    toSheafify (Opens.grothendieckTopology X) P
  have : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α) := by
    dsimp [α, P]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x CommRingCat.{u} ((Functor.const (Opens X)ᵒᵖ).obj A)
  let ex := asIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α)
  let tx := TopCat.Presheaf.germ (constantSheafOnSpace X CommRingCat.{u} A).obj U x hx s
  obtain ⟨V, hVU, hV, a, ha⟩ := TopCat.Presheaf.exists_le_germ_eq P (ex.inv tx) hx
  refine ⟨V, hVU, hV, a, ?_⟩
  have hh := congrArg (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor
    CommRingCat.{u} x).map α)) ha
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hh
  exact (hh.trans (ex.inv_hom_id_apply tx)).symm

omit [IsIntegral X] in
/-- Two constant sections of the constant sheaf with value `A` with the same germ at a point
come from the same element of `A`. -/
private theorem constantSheafOnSpace_germ_injective {x : X} {V W : X.Opens} (hV : x ∈ V)
    (hW : x ∈ W) {a b : A}
    (hab : TopCat.Presheaf.germ (constantSheafOnSpace X CommRingCat.{u} A).obj V x hV
        (((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op V)).hom a) =
      TopCat.Presheaf.germ (constantSheafOnSpace X CommRingCat.{u} A).obj W x hW
        (((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op W)).hom b)) : a = b := by
  let P : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
  let α : P ⟶ (constantSheafOnSpace X CommRingCat.{u} A).obj :=
    toSheafify (Opens.grothendieckTopology X) P
  have : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α) := by
    dsimp [α, P]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x CommRingCat.{u} ((Functor.const (Opens X)ᵒᵖ).obj A)
  obtain ⟨T, hT, iTV, iTW, heq⟩ := TopCat.Presheaf.germ_eq P x hV hW a b
    ((ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α)).1 (by
        rwa [TopCat.Presheaf.stalkFunctor_map_germ_apply,
          TopCat.Presheaf.stalkFunctor_map_germ_apply]))
  simpa [P] using heq

/-- On an integral scheme, a section of the constant sheaf with value `A` over a nonempty open
set is the constant section of an element of `A`. -/
theorem exists_eq_constantSheafOnSpace_section
    (U : X.Opens) (hU : Nonempty U)
    (s : (constantSheafOnSpace X CommRingCat.{u} A).obj.obj (op U)) :
    ∃ a : A, s = ((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op U)).hom a := by
  exact exists_eq_of_germ_eq_generic (constantSheafOnSpace X CommRingCat.{u} A).property
    (fun V a => ((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op V)).hom a)
    (fun h a => ((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj A)).naturality_apply (homOfLE h).op a).symm)
    (fun hV hW a b hab => constantSheafOnSpace_germ_injective X A hV hW hab) hU s
    (fun _ hx => exists_germ_eq_constantSheafOnSpace_section X A U s hx)

/-- On an integral scheme the sections of the constant sheaf with value `A` over a nonempty
open set are the ring `A` itself, through the constant-section map. -/
def constantSheafOnSpaceSectionRingEquiv (U : X.Opens) (hU : Nonempty U) :
    A ≃+* (constantSheafOnSpace X CommRingCat.{u} A).obj.obj (op U) := by
  classical
  let P : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
  let α : P ⟶ (constantSheafOnSpace X CommRingCat.{u} A).obj :=
    toSheafify (Opens.grothendieckTopology X) P
  let η : X := genericPoint X
  have hηU : η ∈ U := by
    rcases hU with ⟨x, hx⟩
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨x, ⟨Set.mem_univ _, hx⟩⟩
  have hsurj : Function.Surjective ((α.app (op U)).hom) := fun s =>
    (exists_eq_constantSheafOnSpace_section X A U hU s).imp fun _ ha => ha.symm
  have hinj : Function.Injective ((α.app (op U)).hom) := by
    intro a b hab
    have hstalk :
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} η).map α).hom
            (TopCat.Presheaf.germ P U η hηU a) =
          ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} η).map α).hom
            (TopCat.Presheaf.germ P U η hηU b) := by
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
        TopCat.Presheaf.stalkFunctor_map_germ_apply]
      exact congrArg (fun s => TopCat.Presheaf.germ
        (constantSheafOnSpace X CommRingCat.{u} A).obj U η hηU s) hab
    have hαη : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} η).map α) := by
      dsimp [α, P]
      exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso η CommRingCat.{u}
        ((Functor.const (Opens X)ᵒᵖ).obj A)
    obtain ⟨T, hT, iTU, iTU', heq⟩ := TopCat.Presheaf.germ_eq P η hηU hηU a b
      ((ConcreteCategory.bijective_of_isIso
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} η).map α)).1 hstalk)
    simpa [P] using heq
  exact RingEquiv.ofBijective ((α.app (op U)).hom) ⟨hinj, hsurj⟩

/-- Every element of `𝒪(U) ⊗_A V`, where `𝒪` is the constant sheaf on `A` and `U` is a nonempty
open set of an integral scheme, is of the shape `1 ⊗ v`. -/
theorem exists_tmul_one_constantSheafOnSpace
    (U : X.Opens) (hU : Nonempty U) (V : Type u) [AddCommGroup V] (hV : Module A V) :
    let P : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
    let S := (constantSheafOnSpace X CommRingCat.{u} A).obj
    let α : P ⟶ S := toSheafify (Opens.grothendieckTopology X) P
    letI : Module A V := hV
    letI : Module A (S.obj (op U)) := (α.app (op U)).hom.toAlgebra.toModule
    ∀ p : TensorProduct A (S.obj (op U)) V,
      ∃ v : V, p = (1 : S.obj (op U)) ⊗ₜ[A] v := by
  let P : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
  let S := (constantSheafOnSpace X CommRingCat.{u} A).obj
  let α : P ⟶ S := toSheafify (Opens.grothendieckTopology X) P
  let : Module A V := hV
  let : Algebra A (S.obj (op U)) := (α.app (op U)).hom.toAlgebra
  let : Module A (S.obj (op U)) := (α.app (op U)).hom.toAlgebra.toModule
  let e := constantSheafOnSpaceSectionRingEquiv X A U hU
  have hM : ∀ p : TensorProduct A (S.obj (op U)) V, ∃ v : V, p = (1 : S.obj (op U)) ⊗ₜ[A] v := by
    intro p
    induction p using TensorProduct.inductionOn with
    | add p q hp hq =>
      obtain ⟨v, rfl⟩ := hp
      obtain ⟨w, rfl⟩ := hq
      exact ⟨v + w, by rw [← TensorProduct.tmul_add]⟩
    | tmul r v =>
      refine ⟨e.symm r • v, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1
      rw [Algebra.smul_def, mul_one]
      change r = e (e.symm r)
      exact (e.apply_symm_apply r).symm
  exact hM

/-- Evaluation of `𝒪(U) ⊗_A V` onto `V`, where `𝒪` is the constant sheaf on `A` and `U` is a
nonempty open set of an integral scheme: the inverse of the constant-section isomorphism,
tensored with the identity. -/
def constantSheafOnSpaceTensorEval
    (U : X.Opens) (hU : Nonempty U) (V : Type u) [AddCommGroup V] (hV : Module A V) :
    let P : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
    let S := (constantSheafOnSpace X CommRingCat.{u} A).obj
    let α : P ⟶ S := toSheafify (Opens.grothendieckTopology X) P
    letI : Module A V := hV
    letI : Module A (S.obj (op U)) := (α.app (op U)).hom.toAlgebra.toModule
    TensorProduct A (S.obj (op U)) V →ₗ[A] V := by
  let P : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
  let S := (constantSheafOnSpace X CommRingCat.{u} A).obj
  let α : P ⟶ S := toSheafify (Opens.grothendieckTopology X) P
  letI : Module A V := hV
  letI : Algebra A (S.obj (op U)) := (α.app (op U)).hom.toAlgebra
  letI : Module A (S.obj (op U)) := (α.app (op U)).hom.toAlgebra.toModule
  let e := constantSheafOnSpaceSectionRingEquiv X A U hU
  let ev : S.obj (op U) →ₗ[A] A :=
    { toFun := e.symm
      map_add' := e.symm.map_add
      map_smul' := by
        intro a r
        change e.symm (e a * r) = a * e.symm r
        simp }
  refine TensorProduct.lift
    { toFun := fun r =>
        { toFun := fun v => ev.toFun r • v
          map_add' := smul_add _
          map_smul' := by
            intro a v
            simp [smul_smul, mul_comm, RingHom.id_apply] }
      map_add' := by
        intro r s
        ext v
        change ev.toFun (r + s) • v = ev.toFun r • v + ev.toFun s • v
        rw [ev.map_add']
        exact add_smul _ _ _
      map_smul' := by
        intro a r
        ext v
        change ev.toFun (a • r) • v = a • (ev.toFun r • v)
        rw [ev.map_smul' a r, smul_smul]
        simp [smul_eq_mul] }

end ConstantRingSheaf

/-! ### The constant sheaf of modules on the stalk at the generic point -/

/-- The constant sheaf of modules on the stalk of `F` at the generic point, over the constant
sheaf of rings on the function field. -/
def constantGenericStalkModuleSheaf (X : Scheme.{u}) [IsIntegral X] (F : X.Modules) :
    SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf
      (C := Opens X) (J := Opens.grothendieckTopology X)
      (constantSheafOnSpace X CommRingCat.{u} X.functionField)) := by
  let O : TopCat.Presheaf CommRingCat.{u} X :=
    (Functor.const (Opens X)ᵒᵖ).obj X.functionField
  let S := constantSheafOnSpace X CommRingCat.{u} X.functionField
  let α : O ⟶ S.obj := toSheafify (Opens.grothendieckTopology X) O
  letI : Module X.functionField (F.presheaf.stalk (genericPoint X)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (genericPoint X)
  let M : PresheafOfModules.{u} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O) :=
    Stacks.AssociatedSheaf.constantModulePresheaf X.toRingedSpace
      (ModuleCat.of X.functionField (F.presheaf.stalk (genericPoint X)))
  exact (PresheafOfModules.sheafification
    (𝟙 (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
      (J := Opens.grothendieckTopology X) S).obj)).obj
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α).obj M)

/-- The constant section of `constantGenericStalkModuleSheaf` determined by an element of the
stalk at the generic point. -/
def constantGenericStalkModuleSection (X : Scheme.{u}) [IsIntegral X] (F : X.Modules)
    (U : X.Opens) (m : F.presheaf.stalk (genericPoint X)) :
    (constantGenericStalkModuleSheaf X F).val.obj (op U) := by
  let O : TopCat.Presheaf CommRingCat.{u} X :=
    (Functor.const (Opens X)ᵒᵖ).obj X.functionField
  let S := constantSheafOnSpace X CommRingCat.{u} X.functionField
  let α : O ⟶ S.obj := toSheafify (Opens.grothendieckTopology X) O
  letI : Module X.functionField (F.presheaf.stalk (genericPoint X)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (genericPoint X)
  let M : PresheafOfModules.{u} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O) :=
    Stacks.AssociatedSheaf.constantModulePresheaf X.toRingedSpace
      (ModuleCat.of X.functionField (F.presheaf.stalk (genericPoint X)))
  letI : Algebra X.functionField (S.obj.obj (op U)) :=
    (α.app (op U)).hom.toAlgebra
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
      (J := Opens.grothendieckTopology X) S).obj)).unit.app
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α).obj M)).app (op U)
          (1 ⊗ₜ[X.functionField] m)

/-- A global section of the constant generic-stalk module sheaf agrees, near every point, with
a constant section. -/
theorem exists_germ_eq_constantGenericStalkModuleSection
    (X : Scheme.{u}) [IsIntegral X] (F : X.Modules)
    (t : (constantGenericStalkModuleSheaf X F).val.obj (op ⊤)) (x : X) :
    ∃ (U : X.Opens) (hUx : x ∈ U) (m : F.presheaf.stalk (genericPoint X)),
      TopCat.Presheaf.germ (constantGenericStalkModuleSheaf X F).val.presheaf
          ⊤ x (Set.mem_univ x) t =
        TopCat.Presheaf.germ (constantGenericStalkModuleSheaf X F).val.presheaf U x hUx
          (constantGenericStalkModuleSection X F U m) := by
  classical
  let O : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} :=
    (Functor.const (Opens X)ᵒᵖ).obj X.functionField
  let S := constantSheafOnSpace X CommRingCat.{u} X.functionField
  let α : O ⟶ S.obj := toSheafify (Opens.grothendieckTopology X) O
  let η : X := genericPoint X
  let : Module X.functionField (F.presheaf.stalk η) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val η
  let M : PresheafOfModules.{u} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O) :=
    Stacks.AssociatedSheaf.constantModulePresheaf X.toRingedSpace
      (ModuleCat.of X.functionField (F.presheaf.stalk η))
  let RH := Stacks.Sheaves.Differentials.ringSheaf
    (C := Opens X) (J := Opens.grothendieckTopology X) S
  let N : PresheafOfModules RH.obj := (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α).obj M
  let ηM := (PresheafOfModules.sheafificationAdjunction (𝟙 RH.obj)).unit.app N
  let η0 := (PresheafOfModules.toPresheaf RH.obj).map ηM
  have hη0 (y : X) : IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map η0) := by
    dsimp [η0, ηM]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y Ab N.presheaf
  let ty := TopCat.Presheaf.germ
    (constantGenericStalkModuleSheaf X F).val.presheaf ⊤ x (Set.mem_univ x) t
  let ey := asIso ((TopCat.Presheaf.stalkFunctor Ab x).map η0)
  obtain ⟨U, hUtop, hUx, p, hp⟩ :=
    TopCat.Presheaf.exists_le_germ_eq N.presheaf (ey.inv ty)
      (show x ∈ (⊤ : X.Opens) from Set.mem_univ x)
  let : Algebra X.functionField (S.obj.obj (op U)) := (α.app (op U)).hom.toAlgebra
  let : Module X.functionField (S.obj.obj (op U)) := (α.app (op U)).hom.toAlgebra.toModule
  change TensorProduct X.functionField (S.obj.obj (op U)) (F.presheaf.stalk η) at p
  obtain ⟨m, hm⟩ := exists_tmul_one_constantSheafOnSpace X X.functionField U ⟨x, hUx⟩
    (F.presheaf.stalk η) inferInstance p
  have hh := congrArg (ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor Ab x).map η0)) hp
  have hmap' :
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab x).map η0))
          (TopCat.Presheaf.germ N.presheaf U x hUx p) =
        TopCat.Presheaf.germ (constantGenericStalkModuleSheaf X F).val.presheaf U x hUx
          ((ConcreteCategory.hom (η0.app (op U))) p) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply U x hUx η0 p
  refine ⟨U, hUx, m, ?_⟩
  have h1 : ty = (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab x).map η0))
      ((ConcreteCategory.hom ey.inv) ty) := (ey.inv_hom_id_apply ty).symm
  have h2 : (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab x).map η0))
      ((ConcreteCategory.hom ey.inv) ty) =
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab x).map η0))
        (TopCat.Presheaf.germ N.presheaf U x hUx p) := hh.symm
  change ty = _
  rw [h1, h2, hmap', hm]
  rfl

/-- Two constant sections of the constant generic-stalk module sheaf with the same germ at the
generic point come from the same element of the stalk. -/
private theorem eq_of_germ_constantGenericStalkModuleSection_eq
    (X : Scheme.{u}) [IsIntegral X] (F : X.Modules) {V W : X.Opens}
    (hV : genericPoint X ∈ V) (hW : genericPoint X ∈ W)
    (m n : F.presheaf.stalk (genericPoint X))
    (hab : TopCat.Presheaf.germ (constantGenericStalkModuleSheaf X F).val.presheaf V _ hV
          (constantGenericStalkModuleSection X F V m) =
        TopCat.Presheaf.germ (constantGenericStalkModuleSheaf X F).val.presheaf W _ hW
          (constantGenericStalkModuleSection X F W n)) : m = n := by
  classical
  let O : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} :=
    (Functor.const (Opens X)ᵒᵖ).obj X.functionField
  let S := constantSheafOnSpace X CommRingCat.{u} X.functionField
  let α : O ⟶ S.obj := toSheafify (Opens.grothendieckTopology X) O
  let η : X := genericPoint X
  let : Module X.functionField (F.presheaf.stalk η) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val η
  let M : PresheafOfModules.{u} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O) :=
    Stacks.AssociatedSheaf.constantModulePresheaf X.toRingedSpace
      (ModuleCat.of X.functionField (F.presheaf.stalk η))
  let RH := Stacks.Sheaves.Differentials.ringSheaf
    (C := Opens X) (J := Opens.grothendieckTopology X) S
  let N : PresheafOfModules RH.obj := (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α).obj M
  let ηM := (PresheafOfModules.sheafificationAdjunction (𝟙 RH.obj)).unit.app N
  let η0 := (PresheafOfModules.toPresheaf RH.obj).map ηM
  have hη0 : IsIso ((TopCat.Presheaf.stalkFunctor Ab η).map η0) := by
    dsimp [η0, ηM]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso η Ab N.presheaf
  let : Algebra X.functionField (S.obj.obj (op V)) := (α.app (op V)).hom.toAlgebra
  let : Module X.functionField (S.obj.obj (op V)) :=
    (α.app (op V)).hom.toAlgebra.toModule
  let : Algebra X.functionField (S.obj.obj (op W)) := (α.app (op W)).hom.toAlgebra
  let : Module X.functionField (S.obj.obj (op W)) :=
    (α.app (op W)).hom.toAlgebra.toModule
  let pV : N.presheaf.obj (op V) := by
    change TensorProduct X.functionField (S.obj.obj (op V)) (F.presheaf.stalk η)
    exact (1 : S.obj.obj (op V)) ⊗ₜ[X.functionField] m
  let pW : N.presheaf.obj (op W) := by
    change TensorProduct X.functionField (S.obj.obj (op W)) (F.presheaf.stalk η)
    exact (1 : S.obj.obj (op W)) ⊗ₜ[X.functionField] n
  have hsrc : TopCat.Presheaf.germ N.presheaf V η hV pV =
      TopCat.Presheaf.germ N.presheaf W η hW pW :=
    (ConcreteCategory.bijective_of_isIso ((TopCat.Presheaf.stalkFunctor Ab η).map η0)).1 <|
      (TopCat.Presheaf.stalkFunctor_map_germ_apply V η hV η0 pV).trans <|
        hab.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply W η hW η0 pW).symm
  obtain ⟨T, hT, iTV, iTW, heq⟩ :=
    TopCat.Presheaf.germ_eq N.presheaf η hV hW pV pW hsrc
  let : Algebra X.functionField (S.obj.obj (op T)) := (α.app (op T)).hom.toAlgebra
  let : Module X.functionField (S.obj.obj (op T)) :=
    (α.app (op T)).hom.toAlgebra.toModule
  let ev := constantSheafOnSpaceTensorEval X X.functionField T ⟨η, hT⟩
    (F.presheaf.stalk η) inferInstance
  change ((S.obj.map iTV.op).hom 1) ⊗ₜ[X.functionField] m =
    ((S.obj.map iTW.op).hom 1) ⊗ₜ[X.functionField] n at heq
  simpa [ev, constantSheafOnSpaceTensorEval] using congrArg (fun z => ev z) heq

/-- Restriction sends the constant section of the constant generic-stalk module sheaf
determined by `m` to the constant section determined by `m`. -/
private theorem constantGenericStalkModuleSection_map
    (X : Scheme.{u}) [IsIntegral X] (F : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (m : F.presheaf.stalk (genericPoint X)) :
    (ConcreteCategory.hom
      ((constantGenericStalkModuleSheaf X F).val.presheaf.map (homOfLE hVU).op))
      (constantGenericStalkModuleSection X F U m) =
    constantGenericStalkModuleSection X F V m := by
  classical
  let O : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} :=
    (Functor.const (Opens X)ᵒᵖ).obj X.functionField
  let S := constantSheafOnSpace X CommRingCat.{u} X.functionField
  let α : O ⟶ S.obj := toSheafify (Opens.grothendieckTopology X) O
  let η : X := genericPoint X
  let : Module X.functionField (F.presheaf.stalk η) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val η
  let M : PresheafOfModules.{u} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O) :=
    Stacks.AssociatedSheaf.constantModulePresheaf X.toRingedSpace
      (ModuleCat.of X.functionField (F.presheaf.stalk η))
  let RH := Stacks.Sheaves.Differentials.ringSheaf
    (C := Opens X) (J := Opens.grothendieckTopology X) S
  let N : PresheafOfModules RH.obj := (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α).obj M
  let ηM := (PresheafOfModules.sheafificationAdjunction (𝟙 RH.obj)).unit.app N
  let η0 := (PresheafOfModules.toPresheaf RH.obj).map ηM
  let i := (homOfLE hVU).op
  let : Algebra X.functionField (S.obj.obj (op U)) := (α.app (op U)).hom.toAlgebra
  let : Module X.functionField (S.obj.obj (op U)) :=
    (α.app (op U)).hom.toAlgebra.toModule
  let : Algebra (O.obj (op U)) (S.obj.obj (op U)) := (α.app (op U)).hom.toAlgebra
  let : Module (O.obj (op U)) (S.obj.obj (op U)) :=
    (α.app (op U)).hom.toAlgebra.toModule
  let : Algebra (O.obj (op V)) (S.obj.obj (op V)) := (α.app (op V)).hom.toAlgebra
  let : Module (O.obj (op V)) (S.obj.obj (op V)) :=
    (α.app (op V)).hom.toAlgebra.toModule
  let : Algebra X.functionField (S.obj.obj (op V)) := (α.app (op V)).hom.toAlgebra
  let : Module X.functionField (S.obj.obj (op V)) :=
    (α.app (op V)).hom.toAlgebra.toModule
  have hsource : (N.map i).hom
        ((1 : S.obj.obj (op U)) ⊗ₜ[X.functionField] m) =
      (1 : S.obj.obj (op V)) ⊗ₜ[X.functionField] m := by
    refine (Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul α M i (1 : S.obj.obj (op U))
      m).trans ?_
    rw [show (M.map i).hom m = m from rfl, map_one]
    rfl
  have hnat := (η0.naturality_apply i
    ((1 : S.obj.obj (op U)) ⊗ₜ[X.functionField] m)).symm
  change _ = (ConcreteCategory.hom (η0.app (op V))) ((N.map i).hom
    ((1 : S.obj.obj (op U)) ⊗ₜ[X.functionField] m)) at hnat
  rwa [hsource] at hnat

/-- **A meromorphic section on an integral scheme is one element of the generic stalk.** A
global section of the constant generic-stalk module sheaf of `F` is the constant section of a
unique element of the stalk of `F` at the generic point. -/
theorem exists_unique_eq_constantGenericStalkModuleSection
    (X : Scheme.{u}) [IsIntegral X] (F : X.Modules)
    (t : (constantGenericStalkModuleSheaf X F).val.obj (op ⊤)) :
    ∃ m : F.presheaf.stalk (genericPoint X),
      t = constantGenericStalkModuleSection X F ⊤ m ∧
        ∀ n : F.presheaf.stalk (genericPoint X),
          t = constantGenericStalkModuleSection X F ⊤ n → m = n := by
  have hη : genericPoint X ∈ (⊤ : X.Opens) := Set.mem_univ _
  obtain ⟨m, hm⟩ := exists_eq_of_germ_eq_generic (constantGenericStalkModuleSheaf X F).isSheaf
    (fun V m => constantGenericStalkModuleSection X F V m)
    (fun h m => constantGenericStalkModuleSection_map X F h m)
    (fun hV hW m n => eq_of_germ_constantGenericStalkModuleSection_eq X F hV hW m n)
    (⟨⟨_, hη⟩⟩ : Nonempty (⊤ : X.Opens)) t (fun x hx => by
      obtain ⟨U, hUx, n, h⟩ := exists_germ_eq_constantGenericStalkModuleSection X F t x
      exact ⟨U, le_top, hUx, n, h⟩)
  exact ⟨m, hm, fun n hn => eq_of_germ_constantGenericStalkModuleSection_eq X F hη hη m n
    (congrArg (TopCat.Presheaf.germ (constantGenericStalkModuleSheaf X F).val.presheaf ⊤ _ hη)
      (hm.symm.trans hn))⟩

end AlgebraicGeometry

end
