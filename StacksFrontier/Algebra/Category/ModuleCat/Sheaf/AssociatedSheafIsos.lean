module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# Universe lifts of sheaves of modules, and the comparison of constructions (1) and (3) of 01BH

Let `(X, 𝒪_X)` be a ringed space, let `α : R → Γ(X, 𝒪_X)` be a ring homomorphism and let `M` be
an `R`-module. Of the constructions of the associated sheaf of `𝒪_X`-modules — pullback along
`π : X → ({*}, R)`, the cokernel of a presentation matrix over `𝒪_X`, and the sheafification of
`U ↦ 𝒪_X(U) ⊗_R M` — this file identifies the first with the third, naturally in `M`, together
with the equation that characterizes the comparison. It also constructs the universe lifts of
presheaves and sheaves of modules, and shows that sheafification commutes with them.

## Main definitions

* `PresheafOfModules.uliftObj`, `PresheafOfModules.uliftMap` and
  `PresheafOfModules.uliftFunctor`: the universe lift of a presheaf of modules, lifting the
  section modules and keeping the presheaf of rings.
* `SheafOfModules.uliftObj` and `SheafOfModules.uliftFunctor`: the same for sheaves of modules.
* `PresheafOfModules.uliftSheafifyUnit` and `PresheafOfModules.sheafifyULiftHom`: the
  comparison morphism `sheafify (ULift M₀) ⟶ ULift (sheafify M₀)`.
* `Stacks.AssociatedSheaf.associatedPresheafFunctor` and
  `Stacks.AssociatedSheaf.moduleSheafification`: construction (3) split as the tensor presheaf
  followed by module sheafification.
* `Stacks.AssociatedSheaf.tensorUnitSection`: the section `1 ⊗ m` of construction (3) on an
  open `U`.
* `Stacks.AssociatedSheaf.pointRing`: the ring map `R → 𝒪_{pt}({*})`.
* `Stacks.AssociatedSheaf.coefficientPointModuleFunctor`: construction (3) on the coefficient
  point, i.e. an `R`-module regarded as a sheaf of modules on `({*}, R)`.

## Main results

* `PresheafOfModules.isIso_sheafifyULiftHom`: sheafification commutes with the universe lift of
  a presheaf of modules.
* `Stacks.AssociatedSheaf.tensorUnitSection_eq_toSheafify`: `tensorUnitSection` is the image of
  `1 ⊗ m` under the sheafification map of the underlying presheaves of abelian groups.
* `Stacks.AssociatedSheaf.associatedSheafAdjunction_unit_app_tensorUnitSection`: the unit of the
  tensor-sheafification adjunction sends `m` to the section `1 ⊗ m`.
* `Stacks.AssociatedSheaf.uliftAssociatedPresheafIso` and `uliftAssociatedSheafIso`: lifting the
  module universe does not change construction (3), and
  `uliftAssociatedSheafIso_hom_app_tensorUnitSection` computes the comparison on `1 ⊗ m`.
* `Stacks.AssociatedSheaf.pushforwardGlobalSectionsIso`: pushforward along `π` followed by
  global sections on the coefficient point is global sections on `X` with scalars restricted
  along `α`.
* `Stacks.AssociatedSheaf.associatedSheafPullbackIso`: the comparison of (1) and (3) at a module
  universe containing that of `R`, and `associatedSheafPullbackIso_hom_app_apply`, its
  characterizing equation.
* `Stacks.AssociatedSheaf.pullbackAssociatedSheafIso`: pullback along `π` of `M` regarded as a
  sheaf of modules on the coefficient point is construction (3), naturally in `M`, at an
  arbitrary module universe; and `pullbackAssociatedSheafIso_hom_app_apply`, which pins it down
  by sending the image of `1 ⊗ m` under the unit of `π^* ⊣ π_*` to `1 ⊗ m`.
* `Stacks.AssociatedSheaf.associatedSheafULiftIso`: the universe lift of construction (3) on `M`
  is construction (3) on the universe lift of `M`.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v₁ u₁ w z t u v

namespace PresheafOfModules

section ULift

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- The universe lift of a presheaf of modules: the presheaf of modules whose sections on `U`
are `ULift` of the sections of `M`, over the same presheaf of rings. -/
def uliftObj (M : PresheafOfModules.{z} R) : PresheafOfModules.{max z t} R where
  obj U := ModuleCat.of _ (ULift.{t} (M.obj U))
  map {U V} f := ModuleCat.ofHom
    (R := R.obj U)
    (X := ModuleCat.of (R.obj U) (ULift.{t} (M.obj U)))
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of (R.obj V) (ULift.{t} (M.obj V))))
    { toFun := fun m ↦ ULift.up (M.map f m.down)
      map_add' := fun x y ↦ congrArg ULift.up ((M.map f).hom.map_add _ _)
      map_smul' := fun r m ↦ congrArg ULift.up (M.map_smul f r m.down) }
  map_id U := by
    ext m
    change ULift.up (M.map (𝟙 U) m.down) = m
    rw [M.map_id]
    rfl
  map_comp f g := by
    ext m
    exact congrArg ULift.up (M.map_comp_apply f g m.down)

/-- The restriction maps of `PresheafOfModules.uliftObj M` are those of `M` on the lifted
sections. -/
@[simp]
lemma uliftObj_map_apply (M : PresheafOfModules.{z} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (m : (uliftObj.{_, _, _, _, t} M).obj U) :
    (uliftObj.{_, _, _, _, t} M).map f m = ULift.up (M.map f m.down) := rfl

/-- The underlying presheaf of abelian groups of `PresheafOfModules.uliftObj M` is that of `M`
composed with the universe lift of abelian groups. -/
lemma uliftObj_presheaf (M : PresheafOfModules.{z} R) :
    (uliftObj.{_, _, _, _, t} M).presheaf = M.presheaf ⋙ AddCommGrpCat.uliftFunctor.{t} := rfl

/-- The universe lift of a morphism of presheaves of modules. -/
def uliftMap {M N : PresheafOfModules.{z} R} (φ : M ⟶ N) :
    uliftObj.{_, _, _, _, t} M ⟶ uliftObj.{_, _, _, _, t} N where
  app U := ModuleCat.ofHom
    (R := R.obj U)
    (X := ModuleCat.of (R.obj U) (ULift.{t} (M.obj U)))
    (Y := ModuleCat.of (R.obj U) (ULift.{t} (N.obj U)))
    { toFun := fun m ↦ ULift.up (Hom.app φ U m.down)
      map_add' := fun x y ↦ congrArg ULift.up ((Hom.app φ U).hom.map_add _ _)
      map_smul' := fun r m ↦ congrArg ULift.up ((Hom.app φ U).hom.map_smul r m.down) }
  naturality {U V} f := by
    ext m
    exact congrArg ULift.up (naturality_apply φ f m.down)

/-- `PresheafOfModules.uliftMap φ` acts as `φ` on the lifted sections. -/
@[simp]
lemma uliftMap_app_apply {M N : PresheafOfModules.{z} R} (φ : M ⟶ N) (U : Cᵒᵖ)
    (m : (uliftObj.{_, _, _, _, t} M).obj U) :
    Hom.app (uliftMap.{_, _, _, _, t} φ) U m = ULift.up (Hom.app φ U m.down) := rfl

/-- The universe-lifting functor on presheaves of modules. -/
@[simps]
def uliftFunctor : PresheafOfModules.{z} R ⥤ PresheafOfModules.{max z t} R where
  obj M := uliftObj.{_, _, _, _, t} M
  map φ := uliftMap.{_, _, _, _, t} φ
  map_id M := by ext U m; rfl
  map_comp φ ψ := by ext U m; rfl

/-- On underlying presheaves of abelian groups, `PresheafOfModules.uliftMap φ` is `φ` whiskered
by the universe lift of abelian groups. -/
lemma toPresheaf_map_uliftMap {M N : PresheafOfModules.{z} R} (φ : M ⟶ N) :
    (toPresheaf R).map (uliftMap.{_, _, _, _, t} φ) =
      Functor.whiskerRight ((toPresheaf R).map φ) AddCommGrpCat.uliftFunctor.{t} := rfl

end ULift

end PresheafOfModules

namespace CategoryTheory.Presheaf

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {F G : Cᵒᵖ ⥤ AddCommGrpCat.{z}} (f : F ⟶ G)

/-- The image sieve of a lifted section under the universe lift of `f` is the image sieve of the
section under `f`. -/
lemma imageSieve_whiskerRight_uliftFunctor {U : C}
    (s : (G ⋙ AddCommGrpCat.uliftFunctor.{t}).obj (op U)) :
    imageSieve (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{t}) s = imageSieve f s.down := by
  ext V i
  simp only [imageSieve_apply]
  exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.down, congrArg ULift.down hx⟩,
    fun ⟨x, hx⟩ ↦ ⟨ULift.up x, congrArg ULift.up hx⟩⟩

/-- The equalizer sieve of two lifted sections is the equalizer sieve of the sections they
lift. -/
lemma equalizerSieve_whiskerRight_uliftFunctor {U : C}
    (x y : (F ⋙ AddCommGrpCat.uliftFunctor.{t}).obj (op U)) :
    equalizerSieve (F := F ⋙ AddCommGrpCat.uliftFunctor.{t}) x y =
      equalizerSieve x.down y.down := by
  ext V i
  simp only [equalizerSieve_apply]
  exact ⟨fun h ↦ congrArg ULift.down h, fun h ↦ congrArg ULift.up h⟩

/-- The universe lift of a locally surjective morphism of presheaves of abelian groups is locally
surjective. -/
instance isLocallySurjective_whiskerRight_uliftFunctor [IsLocallySurjective J f] :
    IsLocallySurjective J (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{t}) where
  imageSieve_mem s := by
    rw [imageSieve_whiskerRight_uliftFunctor]
    exact imageSieve_mem J f _

/-- The universe lift of a locally injective morphism of presheaves of abelian groups is locally
injective. -/
instance isLocallyInjective_whiskerRight_uliftFunctor [IsLocallyInjective J f] :
    IsLocallyInjective J (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{t}) where
  equalizerSieve_mem x y h := by
    rw [equalizerSieve_whiskerRight_uliftFunctor]
    exact equalizerSieve_mem J f _ _ (congrArg ULift.down h)

end CategoryTheory.Presheaf

namespace SheafOfModules

section ULift

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The universe lift of a sheaf of modules. -/
def uliftObj (F : SheafOfModules.{z} R) : SheafOfModules.{max z t} R where
  val := PresheafOfModules.uliftObj.{_, _, _, _, t} F.val
  isSheaf := Presheaf.isSheaf_comp_of_isSheaf J F.val.presheaf
    AddCommGrpCat.uliftFunctor.{t} F.isSheaf

/-- The universe-lifting functor on sheaves of modules. -/
@[simps]
def uliftFunctor : SheafOfModules.{z} R ⥤ SheafOfModules.{max z t} R where
  obj F := uliftObj.{_, _, _, _, t} F
  map φ := { val := PresheafOfModules.uliftMap.{_, _, _, _, t} φ.val }
  map_id F := by ext U m; rfl
  map_comp φ ψ := by ext U m; rfl

end ULift

end SheafOfModules

namespace PresheafOfModules

section SheafifyULift

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max z t}]
  [HasWeakSheafify J AddCommGrpCat.{max z t}]

/-- The universe lift of the sheafification unit, viewed as a morphism into the universe lift
of the associated sheaf. -/
def uliftSheafifyUnit (M : PresheafOfModules.{z} R₀) :
    uliftObj.{_, _, _, _, t} M ⟶
      (SheafOfModules.forget R ⋙ restrictScalars α).obj
        (SheafOfModules.uliftObj.{_, _, _, _, t} ((sheafification.{z} α).obj M)) :=
  uliftMap.{_, _, _, _, t} ((sheafificationAdjunction.{z} α).unit.app M)

/-- The comparison morphism from the associated sheaf of a universe lift to the universe lift
of the associated sheaf. -/
def sheafifyULiftHom (M : PresheafOfModules.{z} R₀) :
    (sheafification.{max z t} α).obj (uliftObj.{_, _, _, _, t} M) ⟶
      SheafOfModules.uliftObj.{_, _, _, _, t} ((sheafification.{z} α).obj M) :=
  ((sheafificationAdjunction.{max z t} α).homEquiv _ _).symm
    (uliftSheafifyUnit.{_, _, _, _, t} α M)

/-- The comparison from the associated sheaf of a universe lift to the universe lift of the
associated sheaf is an isomorphism. -/
instance isIso_sheafifyULiftHom (M : PresheafOfModules.{z} R₀) :
    IsIso (sheafifyULiftHom.{_, _, _, _, t} α M) := by
  have fac : (toPresheaf R₀).map ((sheafificationAdjunction.{max z t} α).unit.app
        (uliftObj.{_, _, _, _, t} M)) ≫
      (toPresheaf R₀).map ((SheafOfModules.forget R ⋙ restrictScalars α).map
        (sheafifyULiftHom.{_, _, _, _, t} α M)) =
      (toPresheaf R₀).map (uliftSheafifyUnit.{_, _, _, _, t} α M) := by
    rw [← Functor.map_comp]
    exact congrArg (toPresheaf R₀).map (sheafificationAdjunction_unit_comp_homEquiv_symm α _)
  have h₁ : Presheaf.IsLocallyInjective J
      ((toPresheaf R₀).map (uliftSheafifyUnit.{_, _, _, _, t} α M)) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (Functor.whiskerRight
      ((toPresheaf R₀).map ((sheafificationAdjunction.{z} α).unit.app M))
      AddCommGrpCat.uliftFunctor.{t}))
  have h₂ : Presheaf.IsLocallySurjective J
      ((toPresheaf R₀).map (uliftSheafifyUnit.{_, _, _, _, t} α M)) :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (Functor.whiskerRight
      ((toPresheaf R₀).map ((sheafificationAdjunction.{z} α).unit.app M))
      AddCommGrpCat.uliftFunctor.{t}))
  have h₃ := Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J
    _ fac
  have h₄ := Presheaf.isLocallySurjective_of_isLocallySurjective_fac J fac
  have : IsIso ((SheafOfModules.toSheaf R).map (sheafifyULiftHom.{_, _, _, _, t} α M)) :=
    (Sheaf.isLocallyBijective_iff_isIso (A := AddCommGrpCat.{max z t})
      ((SheafOfModules.toSheaf R).map (sheafifyULiftHom.{_, _, _, _, t} α M))).mp ⟨h₃, h₄⟩
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)

/-- The comparison `sheafifyULiftHom` carries the lift of a section into the sheafification to
the lift of its image. -/
lemma sheafifyULiftHom_unit_apply (M : PresheafOfModules.{z} R₀) (U : Cᵒᵖ) (x : M.obj U) :
    Hom.app (sheafifyULiftHom.{_, _, _, _, t} α M).val U
        (Hom.app ((sheafificationAdjunction.{max z t} α).unit.app
          (uliftObj.{_, _, _, _, t} M)) U (ULift.up x)) =
      ULift.up (Hom.app ((sheafificationAdjunction.{z} α).unit.app M) U x) :=
  hom_congr_apply' (sheafificationAdjunction_unit_comp_homEquiv_symm α
    (uliftSheafifyUnit.{_, _, _, _, t} α M)) U (ULift.up x)

end SheafifyULift

end PresheafOfModules

namespace Stacks.AssociatedSheaf

open AlgebraicGeometry
open scoped TensorProduct

section Comparison

variable (X : RingedSpace.{u, u}) {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- Two additive maps out of a tensor product which agree on pure tensors are equal. -/
private theorem tensor_addMonoidHom_ext {S A M P : Type*} [CommSemiring S] [AddCommMonoid A]
    [AddCommMonoid M] [AddCommMonoid P] [Module S A] [Module S M] {F G : A ⊗[S] M →+ P}
    (h : ∀ (a : A) (m : M), F (a ⊗ₜ[S] m) = G (a ⊗ₜ[S] m)) : F = G :=
  AddMonoidHom.ext fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | tmul a m => exact h a m

/-- Two morphisms out of the change-of-rings presheaf `U ↦ 𝒪₂(U) ⊗_{𝒪₁(U)} G(U)` which agree
on pure tensors of sections are equal. -/
lemma cofObj_hom_ext {D : Type u₁} [Category.{v₁} D] {O₁ O₂ : Dᵒᵖ ⥤ CommRingCat.{w}}
    (θ : O₁ ⟶ O₂) (G : PresheafOfModules.{z} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
      O₁)) (U : Dᵒᵖ)
    {P : ModuleCat.{max w z} ((Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O₂).obj U)}
    {f g : Stacks.PresheafOfModules.ChangeOfRings.cofObj θ G U ⟶ P}
    (h : ∀ (a : O₂.obj U) (m : G.obj U),
      letI : Algebra (O₁.obj U) (O₂.obj U) := (θ.app U).hom.toAlgebra
      f.hom (a ⊗ₜ[O₁.obj U] m) = g.hom (a ⊗ₜ[O₁.obj U] m)) :
    f = g := by
  let : Algebra (O₁.obj U) (O₂.obj U) := (θ.app U).hom.toAlgebra
  exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ DFunLike.congr_fun
    (tensor_addMonoidHom_ext (F := f.hom.toAddMonoidHom) (G := g.hom.toAddMonoidHom) h) x)

/-- On a pure tensor, the universe-lift comparison of `uliftTensorIso` forgets the lift. -/
lemma uliftTensorIso_hom_tmul (M : ModuleCat.{v} R) (U : (Opens X.carrier)ᵒᵖ)
    (a : X.presheaf.obj U) (m : M) :
    letI : Algebra R (X.presheaf.obj U) := ((globalSectionsMap X α).app U).hom.toAlgebra
    (uliftTensorIso X α M U).hom (a ⊗ₜ[R] (ULift.up.{u} m)) = a ⊗ₜ[R] m := rfl

/-- Construction (3) before sheafification, as a functor of the module: the presheaf
`U ↦ 𝒪_X(U) ⊗_R M`. -/
abbrev associatedPresheafFunctor : ModuleCat.{v} R ⥤
    PresheafOfModules.{max u v} (structureSheafRing X).obj :=
  constantModuleFunctor.{u, v} X ⋙ Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
    (globalSectionsMap X α)

/-- Module sheafification on `X`, in any module universe containing the universe of `X`. -/
abbrev moduleSheafification :
    PresheafOfModules.{max u v} (structureSheafRing X).obj ⥤
      SheafOfModules.{max u v} (structureSheafRing X) :=
  letI := hasModuleSheafify.{u, v} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, v} X
  PresheafOfModules.sheafification.{max u v}
    (R := structureSheafRing X)
    (𝟙 (structureSheafRing X).obj)

/-- Construction (3) as the composite of the tensor presheaf with sheafification. -/
lemma associatedSheafFunctor_eq :
    associatedSheafFunctor.{u, v} X α =
      associatedPresheafFunctor.{u, v} X α ⋙ moduleSheafification.{u, v} X := rfl

/-- The image of `1 ⊗ m` under the canonical map into construction (3) on an open `U`. -/
def tensorUnitSection (M : ModuleCat.{v} R) (U : (Opens X.carrier)ᵒᵖ) (m : M) :
    (associatedSheaf X α M).val.obj U :=
  letI := hasModuleSheafify.{u, v} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, v} X
  letI : Algebra R (X.presheaf.obj U) := ((globalSectionsMap X α).app U).hom.toAlgebra
  PresheafOfModules.Hom.app
    ((PresheafOfModules.sheafificationAdjunction.{max u v}
      (R := structureSheafRing X)
      (𝟙 (structureSheafRing X).obj)).unit.app
        (associatedPresheaf X α M)) U ((1 : X.presheaf.obj U) ⊗ₜ[R] m)

/-- `tensorUnitSection` is the image of `1 ⊗ m` under the sheafification map of the underlying
presheaves of abelian groups. -/
lemma tensorUnitSection_eq_toSheafify (M : ModuleCat.{v} R) (U : (Opens X.carrier)ᵒᵖ) (m : M) :
    letI := hasModuleSheafify.{u, v} X
    letI : Algebra R (X.presheaf.obj U) := ((globalSectionsMap X α).app U).hom.toAlgebra
    tensorUnitSection X α M U m =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X.carrier)
        (associatedPresheaf X α M).presheaf).app U ((1 : X.presheaf.obj U) ⊗ₜ[R] m) := rfl

/-- Lifting the module universe does not change the presheaf `U ↦ 𝒪_X(U) ⊗_R M`, naturally in
`M`. -/
def uliftAssociatedPresheafIso :
    ModuleCat.uliftFunctor.{u} R ⋙ associatedPresheafFunctor.{u, max u v} X α ≅
      associatedPresheafFunctor.{u, v} X α :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModules.isoMk (fun U ↦ uliftTensorIso X α M U)
      (fun {_ _} _ ↦ cofObj_hom_ext _ _ _ (fun _ _ ↦ rfl)))
    (fun _ ↦ PresheafOfModules.hom_ext (fun _ ↦ cofObj_hom_ext _ _ _ (fun _ _ ↦ rfl)))

/-- Lifting the module universe does not change construction (3). -/
def uliftAssociatedSheafIso :
    ModuleCat.uliftFunctor.{u} R ⋙ associatedSheafFunctor.{u, max u v} X α ≅
      associatedSheafFunctor.{u, v} X α :=
  Functor.isoWhiskerRight (uliftAssociatedPresheafIso.{u, v} X α) (moduleSheafification.{u, v} X)

/-- The universe-lift comparison for construction (3) sends the lifted section `1 ⊗ m` to
`1 ⊗ m`. -/
@[simp]
lemma uliftAssociatedSheafIso_hom_app_tensorUnitSection (M : ModuleCat.{v} R)
    (U : (Opens X.carrier)ᵒᵖ) (m : M) :
    PresheafOfModules.Hom.app ((uliftAssociatedSheafIso.{u, v} X α).hom.app M).val U
        (tensorUnitSection X α ((ModuleCat.uliftFunctor.{u} R).obj M) U (ULift.up m)) =
      tensorUnitSection X α M U m :=
  let := hasModuleSheafify.{u, v} X
  let := moduleSheafifyWEqualsLocallyBijective.{u, v} X
  PresheafOfModules.unit_naturality_apply
    ((uliftAssociatedPresheafIso.{u, v} X α).hom.app M) U _

/-- The unit of the tensor-sheafification adjunction is `m ↦ 1 ⊗ m`, read as a section. -/
lemma associatedSheafAdjunction_unit_app_tensorUnitSection (M : ModuleCat.{max u v} R) (m : M) :
    ModuleCat.Hom.hom ((associatedSheafAdjunction.{u, v} X α).unit.app M) m =
      tensorUnitSection X α M (op ⊤) m := rfl

section PointComparison

/-- The ring map `R → 𝒪_{pt}({*})` of the coefficient point: the canonical identification. -/
abbrev pointRing : R →+* (coefficientPoint (CommRingCat.of R)).presheaf.obj (op ⊤) :=
  (coefficientPointSectionsIso (CommRingCat.of R)).hom.hom

/-- The scalar map of construction (3) on `X` is the one of the coefficient point followed by
`π^♯` on the whole space, read on elements. -/
theorem globalSectionsMap_app_top_comp_apply (x : R) :
    (pointStructureMap X α).hom
        (((globalSectionsMap (coefficientPoint (CommRingCat.of R))
          (pointRing (R := R))).app (op ⊤)).hom x) =
      ((globalSectionsMap X α).app (op ⊤)).hom x := by
  refine Eq.trans ?_ (globalSectionsMap_app_top_apply X α x).symm
  refine Eq.trans ?_ (structureSheafHom_app_top_apply X α x)
  exact congrArg _ (globalSectionsMap_app_top_apply
    (coefficientPoint (CommRingCat.of R)) (pointRing (R := R)) x)

/-- Pushforward along `π : X ⟶ ({*}, R)` followed by global sections on the coefficient point
is global sections on `X`, with scalars restricted along `α`. -/
def pushforwardGlobalSectionsIso :
    SheafOfModules.pushforward.{max u v}
        (RingedSpaceModuleAdjunction.structureSheafHom (toCoefficientPoint' X α)) ⋙
      globalSectionsFunctor.{u, v} (coefficientPoint (CommRingCat.of R)) (pointRing (R := R)) ≅
    globalSectionsFunctor.{u, v} X α := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · refine (ModuleCat.restrictScalars _).mapIso (ModuleCat.restrictScalarsId'App _ rfl _) ≪≫
      (ModuleCat.restrictScalarsComp'App _ (pointStructureMap X α).hom _ ?_ _).symm ≪≫
      (ModuleCat.restrictScalars _).mapIso (ModuleCat.restrictScalarsId'App _ rfl _).symm
    exact RingHom.ext fun x ↦ (globalSectionsMap_app_top_comp_apply X α x).symm
  · exact fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- `pushforwardGlobalSectionsIso` is the identity on sections. -/
@[simp]
lemma pushforwardGlobalSectionsIso_inv_app_apply
    (N : SheafOfModules.{max u v} (structureSheafRing X))
    (x : (globalSectionsFunctor.{u, v} X α).obj N) :
    ModuleCat.Hom.hom ((pushforwardGlobalSectionsIso.{u, v} X α).inv.app N) x = x := rfl

/-- Construction (3) on the coefficient point followed by pullback along `π` is construction (3)
on `X`, at a module universe containing that of the ring. -/
def associatedSheafPullbackIso :
    associatedSheafFunctor.{u, max u v} (coefficientPoint (CommRingCat.of R))
          (pointRing (R := R)) ⋙
        coefficientPointPullback.{u, v} X α ≅
      associatedSheafFunctor.{u, max u v} X α :=
  Adjunction.leftAdjointUniq
    ((associatedSheafAdjunction.{u, v} (coefficientPoint (CommRingCat.of R))
      (pointRing (R := R))).comp (coefficientPointAdjunction.{u, v} X α))
    (Adjunction.ofNatIsoRight (associatedSheafAdjunction.{u, v} X α)
      (pushforwardGlobalSectionsIso.{u, v} X α).symm)

/-- The comparison of constructions (1) and (3) carries the image of `1 ⊗ m` under the
pullback adjunction unit to `1 ⊗ m`. -/
lemma associatedSheafPullbackIso_hom_app_apply (M : ModuleCat.{max u v} R) (m : M) :
    PresheafOfModules.Hom.app
        ((associatedSheafPullbackIso.{u, v} X α).hom.app M).val (op ⊤)
      (PresheafOfModules.Hom.app ((coefficientPointAdjunction.{u, v} X α).unit.app
        ((associatedSheafFunctor.{u, max u v} (coefficientPoint (CommRingCat.of R))
          (pointRing (R := R))).obj M)).val (op ⊤)
        (tensorUnitSection (coefficientPoint (CommRingCat.of R)) (pointRing (R := R))
          M (op ⊤) m)) =
      tensorUnitSection X α M (op ⊤) m :=
  congrArg (fun φ ↦ ModuleCat.Hom.hom φ m)
    (Adjunction.unit_leftAdjointUniq_hom_app
      ((associatedSheafAdjunction.{u, v} (coefficientPoint (CommRingCat.of R))
        (pointRing (R := R))).comp (coefficientPointAdjunction.{u, v} X α))
      (Adjunction.ofNatIsoRight (associatedSheafAdjunction.{u, v} X α)
        (pushforwardGlobalSectionsIso.{u, v} X α).symm) M)

/-- For an isomorphism `f` of sheaves of modules, `f.inv` undoes `f.hom` on sections. -/
lemma sheafIso_inv_app_hom_app
    {A B : SheafOfModules.{max u v} (structureSheafRing X)} (f : A ≅ B)
    (U : (Opens X.carrier)ᵒᵖ) (x : A.val.obj U) :
    PresheafOfModules.Hom.app f.inv.val U (PresheafOfModules.Hom.app f.hom.val U x) = x :=
  congrArg (fun φ : A ⟶ A ↦ PresheafOfModules.Hom.app φ.val U x) f.hom_inv_id

/-- The inverse of the universe-lift comparison for construction (3), on `1 ⊗ m`. -/
lemma uliftAssociatedSheafIso_inv_app_tensorUnitSection (M : ModuleCat.{v} R)
    (U : (Opens X.carrier)ᵒᵖ) (m : M) :
    PresheafOfModules.Hom.app ((uliftAssociatedSheafIso.{u, v} X α).inv.app M).val U
        (tensorUnitSection X α M U m) =
      tensorUnitSection X α ((ModuleCat.uliftFunctor.{u} R).obj M) U (ULift.up m) := by
  conv_lhs => rw [← uliftAssociatedSheafIso_hom_app_tensorUnitSection X α M U m]
  exact sheafIso_inv_app_hom_app X ((uliftAssociatedSheafIso.{u, v} X α).app M) U _

/-- Naturality of the unit of `π^* ⊣ π_*` on global sections. -/
lemma coefficientPointAdjunction_unit_naturality_apply
    {N N' : SheafOfModules.{max u v}
      (structureSheafRing (coefficientPoint (CommRingCat.of R)))}
    (g : N ⟶ N') (x : N.val.obj (op ⊤)) :
    PresheafOfModules.Hom.app ((coefficientPointPullback.{u, v} X α).map g).val (op ⊤)
        (PresheafOfModules.Hom.app
          ((coefficientPointAdjunction.{u, v} X α).unit.app N).val (op ⊤) x) =
      PresheafOfModules.Hom.app
        ((coefficientPointAdjunction.{u, v} X α).unit.app N').val (op ⊤)
          (PresheafOfModules.Hom.app g.val (op ⊤) x) :=
  (congrArg (fun φ : N ⟶ _ ↦ PresheafOfModules.Hom.app φ.val (op ⊤) x)
    ((coefficientPointAdjunction.{u, v} X α).unit.naturality g)).symm

/-- An `R`-module, regarded as a sheaf of modules on the coefficient point by construction (3)
there. -/
abbrev coefficientPointModuleFunctor : ModuleCat.{v} R ⥤
    SheafOfModules.{max u v}
      (structureSheafRing (coefficientPoint (CommRingCat.of R))) :=
  associatedSheafFunctor.{u, v} (coefficientPoint (CommRingCat.of R)) (pointRing (R := R))

/-- Pullback along `π : X ⟶ ({*}, R)` of `M` regarded as a sheaf of modules on the coefficient
point is construction (3), naturally in `M`, with the module universe independent of the
universe of `X` and `R`. -/
@[stacks 01BH "comparison_of_three_constructions"]
def pullbackAssociatedSheafIso :
    coefficientPointModuleFunctor.{u, v} (R := R) ⋙ coefficientPointPullback.{u, v} X α ≅
      associatedSheafFunctor.{u, v} X α :=
  Functor.isoWhiskerRight
      (uliftAssociatedSheafIso.{u, v} (coefficientPoint (CommRingCat.of R))
        (pointRing (R := R))).symm (coefficientPointPullback.{u, v} X α) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.uliftFunctor.{u} R)
      (associatedSheafPullbackIso.{u, v} X α) ≪≫
    uliftAssociatedSheafIso.{u, v} X α

/-- The comparison `pullbackAssociatedSheafIso` carries the image of `1 ⊗ m` under the unit of
`π^* ⊣ π_*` to `1 ⊗ m`. -/
@[stacks 01BH "comparison_of_three_constructions"]
lemma pullbackAssociatedSheafIso_hom_app_apply (M : ModuleCat.{v} R) (m : M) :
    PresheafOfModules.Hom.app ((pullbackAssociatedSheafIso.{u, v} X α).hom.app M).val (op ⊤)
        (PresheafOfModules.Hom.app ((coefficientPointAdjunction.{u, v} X α).unit.app
          ((coefficientPointModuleFunctor.{u, v} (R := R)).obj M)).val (op ⊤)
          (tensorUnitSection (coefficientPoint (CommRingCat.of R)) (pointRing (R := R))
            M (op ⊤) m)) =
      tensorUnitSection X α M (op ⊤) m := by
  have h₁ := coefficientPointAdjunction_unit_naturality_apply X α
    ((uliftAssociatedSheafIso.{u, v} (coefficientPoint (CommRingCat.of R))
      (pointRing (R := R))).inv.app M)
    (tensorUnitSection (coefficientPoint (CommRingCat.of R)) (pointRing (R := R)) M (op ⊤) m)
  change PresheafOfModules.Hom.app ((uliftAssociatedSheafIso.{u, v} X α).hom.app M).val (op ⊤)
      (PresheafOfModules.Hom.app ((associatedSheafPullbackIso.{u, v} X α).hom.app
          ((ModuleCat.uliftFunctor.{u} R).obj M)).val (op ⊤)
        (PresheafOfModules.Hom.app ((coefficientPointPullback.{u, v} X α).map
            ((uliftAssociatedSheafIso.{u, v} (coefficientPoint (CommRingCat.of R))
              (pointRing (R := R))).inv.app M)).val (op ⊤)
          (PresheafOfModules.Hom.app ((coefficientPointAdjunction.{u, v} X α).unit.app
            ((associatedSheafFunctor.{u, v} (coefficientPoint (CommRingCat.of R))
              (pointRing (R := R))).obj M)).val (op ⊤)
            (tensorUnitSection (coefficientPoint (CommRingCat.of R)) (pointRing (R := R))
              M (op ⊤) m)))) = _
  rw [h₁, uliftAssociatedSheafIso_inv_app_tensorUnitSection]
  refine Eq.trans ?_ (uliftAssociatedSheafIso_hom_app_tensorUnitSection X α M (op ⊤) m)
  exact congrArg (fun y ↦ PresheafOfModules.Hom.app
      ((uliftAssociatedSheafIso.{u, v} X α).hom.app M).val (op ⊤) y)
    (associatedSheafPullbackIso_hom_app_apply X α ((ModuleCat.uliftFunctor.{u} R).obj M)
      (ULift.up m))

section ULiftSheaf

/-- Two morphisms out of a universe lift of a change-of-rings presheaf which agree on lifts of
pure tensors are equal. -/
lemma uliftCofObj_hom_ext {D : Type u₁} [Category.{v₁} D] {O₁ O₂ : Dᵒᵖ ⥤ CommRingCat.{w}}
    (θ : O₁ ⟶ O₂) (G : PresheafOfModules.{z} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
      O₁)) (U : Dᵒᵖ)
    {P : ModuleCat.{max w z t} ((Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O₂).obj U)}
    {f g : ModuleCat.of ((Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O₂).obj U)
      (ULift.{t} (Stacks.PresheafOfModules.ChangeOfRings.cofObj θ G U)) ⟶ P}
    (h : ∀ (a : O₂.obj U) (m : G.obj U),
      letI : Algebra (O₁.obj U) (O₂.obj U) := (θ.app U).hom.toAlgebra
      f.hom (ULift.up (a ⊗ₜ[O₁.obj U] m)) = g.hom (ULift.up (a ⊗ₜ[O₁.obj U] m))) :
    f = g := by
  let : Algebra (O₁.obj U) (O₂.obj U) := (θ.app U).hom.toAlgebra
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  exact DFunLike.congr_fun (tensor_addMonoidHom_ext
    (F := f.hom.toAddMonoidHom.comp AddEquiv.ulift.symm.toAddMonoidHom)
    (G := g.hom.toAddMonoidHom.comp AddEquiv.ulift.symm.toAddMonoidHom) h) x.down

/-- Lifting the module universe commutes with the tensor presheaf of construction (3):
`ULift (𝒪_X(U) ⊗_R M) ≅ 𝒪_X(U) ⊗_R ULift M`. -/
def uliftAssociatedPresheafULiftIso (M : ModuleCat.{v} R) :
    PresheafOfModules.uliftObj.{_, _, _, _, t} ((associatedPresheafFunctor.{u, v} X α).obj M) ≅
      (associatedPresheafFunctor.{u, max v t} X α).obj
        (ModuleCat.of R (ULift.{t} M.carrier)) :=
  PresheafOfModules.isoMk
    (fun U ↦
      letI : Algebra R (X.presheaf.obj U) := ((globalSectionsMap X α).app U).hom.toAlgebra
      let e : ULift.{t} (Stacks.PresheafOfModules.ChangeOfRings.cofObj (globalSectionsMap X α)
            ((constantModuleFunctor.{u, v} X).obj M) U) ≃ₗ[X.presheaf.obj U]
          Stacks.PresheafOfModules.ChangeOfRings.cofObj (globalSectionsMap X α)
            ((constantModuleFunctor.{u, max v t} X).obj
              (ModuleCat.of R (ULift.{t} M.carrier))) U :=
        ULift.moduleEquiv.trans
          (TensorProduct.AlgebraTensorModule.congr
            (LinearEquiv.refl (X.presheaf.obj U) (X.presheaf.obj U))
            (ULift.moduleEquiv (R := R) (M := M.carrier))).symm
      LinearEquiv.toModuleIso e)
    (fun {_ _} _ ↦ uliftCofObj_hom_ext _ _ _ (fun _ _ ↦ rfl))

/-- The universe lift of the sheaf associated to `M` is the sheaf associated to the universe lift
of `M`. -/
def associatedSheafULiftIso (M : ModuleCat.{v} R) :
    SheafOfModules.uliftObj.{_, _, _, _, t} (associatedSheaf X α M) ≅
      associatedSheaf X α (ModuleCat.of R (ULift.{t} M.carrier)) :=
  letI := hasModuleSheafify.{u, v} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, v} X
  letI := hasModuleSheafify.{u, max v t} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, max v t} X
  (asIso (PresheafOfModules.sheafifyULiftHom.{_, _, _, _, t}
      (𝟙 (structureSheafRing X).obj)
      ((associatedPresheafFunctor.{u, v} X α).obj M))).symm ≪≫
    (moduleSheafification.{u, max v t} X).mapIso (uliftAssociatedPresheafULiftIso X α M)

end ULiftSheaf

end PointComparison





end Comparison



end Stacks.AssociatedSheaf

end
