module

public import StacksFrontier.Algebra.Category.ModuleCat.FiniteFilteredColimit
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# The functor `Hom_R(N, -)` for an `(R, S)`-bimodule `N`

Let `N` be a left `R`-module with a commuting right action of a ring `S` (a left action of
`Sᵐᵒᵖ`). Then `Hom_R(N, X)` is a left `S`-module by `(s • f)(n) = f(n • s)`, naturally in the
`R`-module `X`, which gives an additive functor `Hom_R(N, -) : Mod_R ⥤ Mod_S`. It preserves
limits, its underlying sets being those of the corepresentable functor `Hom(N, -)`, and when `R`
and `N` are finite it preserves filtered colimits: a linear map from `N` into a filtered colimit
factors through a stage, essentially uniquely
(`ModuleCat.FiniteFilteredColimit.exists_lift`).

## Main definitions

* `ModuleCat.BimoduleHom.Obj`: `Hom_R(N, X)` with its `S`-module structure.
* `ModuleCat.BimoduleHom.functor`: the functor `Hom_R(N, -) : Mod_R ⥤ Mod_S`.

## Main results

* `ModuleCat.BimoduleHom.preservesLimits`.
* `ModuleCat.BimoduleHom.preservesFilteredColimits`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v' v u u'

namespace ModuleCat.BimoduleHom

variable {R : Type u} [Ring R] {S : Type u'} [Ring S] {N : Type w} [AddCommGroup N] [Module R N]
  [Module Sᵐᵒᵖ N] [SMulCommClass Sᵐᵒᵖ R N]

/-- `Hom_R(N, X)`, a type synonym carrying the `S`-module structure `(s • f)(n) = f(n • s)` for
every right action of `S` on `N` commuting with that of `R`. -/
def Obj (R : Type u) [Ring R] (N : Type w) [AddCommGroup N] [Module R N] (X : Type*)
    [AddCommGroup X] [Module R X] : Type _ := N →ₗ[R] X

section Obj

variable (X : Type*) [AddCommGroup X] [Module R X]

/-- The additive group structure of `N →ₗ[R] X`. -/
instance : AddCommGroup (Obj R N X) := inferInstanceAs (AddCommGroup (N →ₗ[R] X))

/-- The identification of `Hom_R(N, X)` with the group of linear maps `N →ₗ[R] X`. -/
def toLinearMap : Obj R N X ≃+ (N →ₗ[R] X) := AddEquiv.refl _

/-- The action `(s • f)(n) = f(n • s)` of `S` on `Hom_R(N, X)`. -/
instance : SMul S (Obj R N X) where
  smul s f := (toLinearMap X).symm
    ((toLinearMap X f).comp (DistribSMul.toLinearMap R N (MulOpposite.op s)))

/-- `(s • f)(n) = f(n • s)`. -/
lemma smul_apply (s : S) (f : Obj R N X) (n : N) :
    toLinearMap X (s • f) n = toLinearMap X f (MulOpposite.op s • n) := rfl

/-- Two elements of `Hom_R(N, X)` are equal if and only if they agree at every `n : N`. -/
lemma ext_iff' {f g : Obj R N X} : f = g ↔ ∀ n, toLinearMap X f n = toLinearMap X g n :=
  ⟨fun h _ => h ▸ rfl, fun h => LinearMap.ext h⟩

/-- `Hom_R(N, X)` is a left `S`-module under `(s • f)(n) = f(n • s)`. -/
instance : Module S (Obj R N X) where
  one_smul f := (ext_iff' X).2 fun n => by rw [smul_apply, MulOpposite.op_one, one_smul]
  mul_smul s t f := (ext_iff' X).2 fun n => by
    rw [smul_apply, smul_apply, smul_apply, MulOpposite.op_mul, mul_smul]
  smul_zero s := (ext_iff' X).2 fun n => by rw [smul_apply]; rfl
  smul_add s f g := (ext_iff' X).2 fun n => by
    rw [smul_apply, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, smul_apply,
      smul_apply]
  add_smul s t f := (ext_iff' X).2 fun n => by
    rw [smul_apply, map_add, LinearMap.add_apply, smul_apply, smul_apply, MulOpposite.op_add,
      add_smul, map_add]
  zero_smul f := (ext_iff' X).2 fun n => by
    rw [smul_apply, MulOpposite.op_zero, zero_smul, map_zero]; rfl

end Obj

variable (R S N)

/-- **The functor `Hom_R(N, -) : Mod_R ⥤ Mod_S`.** -/
@[simps]
def functor : ModuleCat.{w} R ⥤ ModuleCat.{w} S where
  obj X := ModuleCat.of S (Obj R N X)
  map {X Y} g := ModuleCat.ofHom
    { toFun := fun f => (toLinearMap Y).symm (g.hom.comp (toLinearMap X f))
      map_add' := fun f f' => by
        change g.hom.comp (toLinearMap X f + toLinearMap X f') = _
        rw [LinearMap.comp_add]; rfl
      map_smul' := fun s f => rfl }
  map_id X := rfl
  map_comp f g := rfl

/-- The functor `Hom_R(N, -)` is additive. -/
instance : (functor R S N).Additive where
  map_add {X Y f g} := by
    ext φ
    change (f.hom + g.hom).comp (toLinearMap X φ) = _
    rw [LinearMap.add_comp]; rfl

/-- The underlying sets of `Hom_R(N, -)` are those of the corepresentable functor `Hom(N, -)`. -/
def functorCompForgetIso :
    functor R S N ⋙ forget (ModuleCat.{w} S) ≅ coyoneda.obj (Opposite.op (ModuleCat.of R N)) :=
  NatIso.ofComponents (fun X =>
    { hom := TypeCat.ofHom fun (f : Obj R N X) => ModuleCat.ofHom (toLinearMap X f)
      inv := TypeCat.ofHom fun (g : ModuleCat.of R N ⟶ X) => (toLinearMap X).symm g.hom })
    (fun _ => rfl)

/-- The functor `Hom_R(N, -) : Mod_R ⥤ Mod_S` preserves limits. -/
instance preservesLimits [Small.{w} S] : PreservesLimits (functor R S N) :=
  have : PreservesLimits (functor R S N ⋙ forget (ModuleCat.{w} S)) :=
    preservesLimits_of_natIso (functorCompForgetIso R S N).symm
  have : ReflectsLimits (forget (ModuleCat.{w} S)) := reflectsLimits_of_reflectsIsomorphisms
  preservesLimits_of_reflects_of_preserves (functor R S N) (forget (ModuleCat.{w} S))

/-- **`Hom_R(N, -)` preserves filtered colimits when `R` and `N` are finite.** -/
instance preservesFilteredColimits [Finite R] [Finite N] [Small.{w} S] :
    PreservesFilteredColimitsOfSize.{w, w} (functor R S N) where
  preserves_filtered_colimits J _ _ := ⟨fun {F} => ⟨fun {c} hc => by
    have : PreservesColimitsOfShape J (forget (ModuleCat.{w} S)) := by
      change PreservesColimitsOfShape J
        (forget₂ (ModuleCat.{w} S) AddCommGrpCat.{w} ⋙ forget AddCommGrpCat.{w})
      infer_instance
    have : PreservesColimitsOfShape J (forget (ModuleCat.{w} R)) := by
      change PreservesColimitsOfShape J
        (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ⋙ forget AddCommGrpCat.{w})
      infer_instance
    have : ReflectsColimitsOfShape J (forget (ModuleCat.{w} S)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    refine ⟨isColimitOfReflects (forget (ModuleCat.{w} S)) ?_⟩
    refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun j x y hxy => ?_)
    · obtain ⟨j, ψ, hψ⟩ := ModuleCat.FiniteFilteredColimit.exists_lift F hc N (toLinearMap _ x)
      exact ⟨j, (toLinearMap _).symm ψ, (toLinearMap _).injective hψ.symm⟩
    · obtain ⟨k, t, ht⟩ := ModuleCat.FiniteFilteredColimit.exists_map_comp_eq F hc N
        (toLinearMap _ x) (toLinearMap _ y) (congrArg (toLinearMap _) hxy)
      exact ⟨k, t, (toLinearMap _).injective ht⟩⟩⟩

end ModuleCat.BimoduleHom

end
