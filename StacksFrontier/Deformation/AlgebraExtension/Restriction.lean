module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalClassRestriction
public import StacksFrontier.Deformation.AlgebraExtension.ChangeOfLift
import all StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass

/-!
# The conormal map of a lift of generators, and shifting a lift

Let `α : ℰ ⟶ 𝒪` be a family of generators of `𝒪` over `𝒜`, with relation ideal
`ℐ = Ker(𝒜[ℰ] ⟶ 𝒪)`, and let `β` be a lift of `α` to an extension `P` of `𝒜`-algebras of `𝒪`
by `ℳ`. The restriction `ℐ ⟶ ℳ` of `β` is linear over `𝒜[ℰ]` acting through `𝒜[ℰ] ⟶ 𝒪`, so
it is a restriction datum in the sense of `Stacks.Sites.Conormal.IdealRestriction` and descends
to a morphism of `𝒪`-modules `δ_β : ℐ/ℐ² ⟶ ℳ` out of the degree `-1` term of `NL(α)`. This is
the map `ℐ/ℐ² ⟶ ℳ` attached to an extension and a lift in the proofs of
[Stacks Project, Tag 08UG] and [Stacks Project, Tag 08UK].

A morphism `θ : Ω ⟶ ℳ` out of the degree `0` term `Ω = 𝒪 ⊗ Ω_{𝒜[ℰ]/𝒜}` of `NL(α)` *shifts*
the lift: `(β + θ)(e) = β(e) + θ(1 ⊗ d e)`. The homomorphism `𝒜[ℰ] ⟶ 𝒪'` of the shifted lift is
`y ↦ β(y) + θ(1 ⊗ d y)`, and `δ_{β + θ} = δ_β + θ ∘ d`. Every other lift of `α` to `P` is a
shift of `β`, which is the change-of-lift indeterminacy of Step 2 of the proof of
[Stacks Project, Tag 08UG].

## Main definitions

* `Deformation.AlgebraExtension.GeneratorLift.idealRestriction`: the restriction datum of `β`.
* `Deformation.AlgebraExtension.GeneratorLift.conormalHom`: the morphism `δ_β : ℐ/ℐ² ⟶ ℳ`.
* `Deformation.AlgebraExtension.GeneratorLift.shift`: the lift `β + θ`.

## Main results

* `Deformation.AlgebraExtension.GeneratorLift.conormalHom_comp`: `δ_{k ∘ β} = φ ∘ δ_β` for a
  morphism `k` of extensions along `φ`.
* `Deformation.AlgebraExtension.GeneratorLift.shift_hom_app`: the homomorphism of `β + θ`.
* `Deformation.AlgebraExtension.GeneratorLift.conormalHom_shift`: `δ_{β + θ} = δ_β + θ ∘ d`.
* `Deformation.AlgebraExtension.GeneratorLift.exists_eq_shift`: any two lifts differ by a shift.
* `Deformation.AlgebraExtension.GeneratorLift.tensorHom_ext`: a morphism out of `Ω` is
  determined by its values on the differentials of the variables.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sites.Conormal (kernelIdeal tensorDifferential conormalClass IdealRestriction
  conormalDesc underlyingRingHomForPullback)
open Stacks.Sites.FreeAlgebra
open Stacks.SheafOfModules (presentation presentationConormalSequence)

universe u

namespace Deformation.AlgebraExtension

section Tensor

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {O : Sheaf J CommRingCat.{u}}

/-- A sheaf of `𝒪`-modules, read as a module over `Stacks.SheafOfModules.Tensor.ringSheaf 𝒪`,
the ring sheaf over which the naive cotangent complex and its `Ext` groups are formed. The two
ring sheaves are the same sheaf `𝒪 ⋙ forget₂`, so this is the identity. -/
abbrev tensorModule (M : SheafOfModules.{u} (underlyingRingSheaf O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  M

/-- A morphism of sheaves of `𝒪`-modules, read over `Stacks.SheafOfModules.Tensor.ringSheaf 𝒪`. -/
abbrev tensorMap {M N : SheafOfModules.{u} (underlyingRingSheaf O)} (φ : M ⟶ N) :
    tensorModule M ⟶ tensorModule N :=
  φ

end Tensor

namespace GeneratorLift

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M N : SheafOfModules.{u} (underlyingRingSheaf O)}
  {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O}
  {P : AlgebraExtension a M} {Q : AlgebraExtension a N}

omit [HasWeakSheafify J CommRingCat] in
/-- Two lifts of `α` to `P` with the same underlying map `ℰ ⟶ 𝒪'` are equal. -/
@[ext]
theorem ext {β β' : GeneratorLift α P} (h : β.lift = β'.lift) : β = β' := by
  cases β; cases β'; cases h; rfl

/-- The homomorphism of a lift sends the differential variable `e` to `β(e)`. -/
private theorem hom_app_variable (β : GeneratorLift α P) (U : Cᵒᵖ) (e : E.obj U) :
    β.hom.hom.app U ((freeAlgebraSheafVariable J A E).app U e) = β.lift.app U e :=
  congrArg (fun t => t.app U e) β.variable_hom

variable [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]

/-- The `1 ⊗ d y` of a local section `y` of `𝒜[ℰ]`, in the degree `0` term of `NL(α)`. -/
noncomputable abbrev dTensor (U : Cᵒᵖ) (y : (freeAlgebraSheaf J A E).obj.obj U) :
    (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂.val.obj U :=
  tensorDifferential.{u, u, u, u} J A (freeAlgebraSheaf J A E) O
    (freeAlgebraSheafCoefficientMap J A E) (presentation J A O a E α) U y

/-- The class of a local relation in the degree `-1` term `ℐ/ℐ²` of `NL(α)`. -/
noncomputable abbrev relClass (U : Cᵒᵖ) (g : kernelIdeal (presentation J A O a E α).hom U) :
    (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁.val.obj U :=
  conormalClass.{u, u, u, u} J A (freeAlgebraSheaf J A E) O
    (freeAlgebraSheafCoefficientMap J A E) (presentation J A O a E α) U g

/-- The map `ℐ/ℐ² ⟶ Ω` of `NL(α)` sends the class of a local relation `g` to `1 ⊗ d g`. -/
theorem f_relClass (U : Cᵒᵖ) (g : kernelIdeal (presentation J A O a E α).hom U) :
    (presentationConormalSequence.{u, u, u, u} J A O a E α).f.val.app U (relClass U g) =
      dTensor U (g : (freeAlgebraSheaf J A E).obj.obj U) :=
  Stacks.Sites.Conormal.conormalSequence_f_class _ _ _ _ _ _ _ _

section ExtGenerators

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}]

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **A morphism out of the degree `0` term of `NL(α)` is determined by its values on the
differentials of the variables**: that term is the free `𝒪`-module on `ℰ`. -/
theorem tensorHom_ext
    {θ₁ θ₂ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ tensorModule N}
    (h : ∀ (U : Cᵒᵖ) (e : E.obj U),
      θ₁.val.app U (dTensor U ((freeAlgebraSheafVariable J A E).app U e)) =
        θ₂.val.app U (dTensor U ((freeAlgebraSheafVariable J A E).app U e))) :
    θ₁ = θ₂ := by
  have : Presheaf.IsLocallySurjective J
      ((toSheafification J CommRingCat.{u}).app (polynomialPresheaf J A E)) :=
    (J.W_toSheafify _).isLocallySurjective
  refine (Stacks.SheafOfModules.tensorHomEquivDerivation.{u, u, u} J A O a E α N).injective ?_
  refine Stacks.SheafOfModules.freeAlgebraSheafDerivation_ext J A E _ _ _ fun V e => ?_
  exact (Stacks.SheafOfModules.tensorHomEquivDerivation_d.{u, u, u} J A O a E α N θ₁ V _).trans
    ((h V e).trans
      (Stacks.SheafOfModules.tensorHomEquivDerivation_d.{u, u, u} J A O a E α N θ₂ V _).symm)

end ExtGenerators

/-! ### Morphisms of extensions are determined by a lift -/

section Determined

omit [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom] in
/-- Two lifts of `α` to `P` with the same homomorphism `𝒜[ℰ] ⟶ 𝒪'` are equal. -/
theorem ext_of_hom {β β' : GeneratorLift α P} (h : β.hom = β'.hom) : β = β' :=
  ext (by rw [← β.variable_hom, ← β'.variable_hom, h])

/-- **A morphism of extensions out of `P` is determined by its composite with a lift**: `𝒪'_P` is
locally generated by the image of `𝒜[ℰ]` and the ideal `ℳ`, on which the morphism is
prescribed. -/
theorem _root_.Deformation.AlgebraExtension.MapAlong.ext_of_comp {φ : M ⟶ N}
    {k₁ k₂ : MapAlong φ P Q} (β : GeneratorLift α P) (h : β.comp k₁ = β.comp k₂) :
    k₁ = k₂ := by
  have hh : β.hom ≫ k₁.hom = β.hom ≫ k₂.hom := by rw [← comp_hom, ← comp_hom, h]
  refine MapAlong.ext ?_
  apply Sheaf.hom_ext
  ext U x
  refine Stacks.Sites.SqZeroPushout.eq_of_locally_eq
    (Stacks.Sites.SqZeroPushout.isSheaf_forgetCommRing Q.extension)
    (Presheaf.imageSieve_mem J (β.hom ≫ P.reduction).hom (P.reduction.hom.app U x)) _ _
    fun Y f hf => ?_
  obtain ⟨y, hy⟩ := hf
  have hnat : P.reduction.hom.app (op Y) (P.extension.obj.map f.op x) =
      O.obj.map f.op (P.reduction.hom.app U x) :=
    NatTrans.naturality_apply P.reduction.hom f.op x
  have hd : P.reduction.hom.app (op Y)
      (P.extension.obj.map f.op x - β.hom.hom.app (op Y) y) = 0 := by
    rw [map_sub, hnat]
    exact sub_eq_zero.2 hy.symm
  obtain ⟨m, hm⟩ := P.exists_incl _ hd
  have hx : P.extension.obj.map f.op x = β.hom.hom.app (op Y) y + P.incl m := by
    rw [hm, add_sub_cancel]
  show (Q.extension.obj.map f.op) (k₁.hom.hom.app U x) =
    (Q.extension.obj.map f.op) (k₂.hom.hom.app U x)
  rw [← NatTrans.naturality_apply k₁.hom.hom, ← NatTrans.naturality_apply k₂.hom.hom, hx,
    map_add, map_add, k₁.kernel_comm, k₂.kernel_comm]
  exact congrArg (· + _) (congrArg (fun t => t.hom.app (op Y) y) hh)

variable [J.WEqualsLocallyBijective CommRingCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]

/-- **Step 3 of the proof of [Stacks Project, Tag 08UG], with its output pinned down**: if two
lifts have restrictions to the relations related by `φ`, there is a morphism of extensions along
`φ` carrying the one lift to the other. -/
theorem exists_mapAlong_comp_eq {φ : M ⟶ N} (β : GeneratorLift α P) (β' : GeneratorLift α Q)
    (h : ∀ (U : Cᵒᵖ) (g : kernelIdeal (presentation J A O a E α).hom U),
      β'.restriction U g = φ.val.app U (β.restriction U g)) :
    ∃ k : MapAlong φ P Q, β.comp k = β' := by
  have hq : β'.hom ≫ Q.reduction = β.hom ≫ P.reduction := by
    rw [β'.hom_reduction, β.hom_reduction]
  have hψ : ∀ (U : Cᵒᵖ) (g : kernelIdeal (β.hom ≫ P.reduction).hom U),
      β'.hom.hom.app U (g : (freeAlgebraSheaf J A E).obj.obj U) =
        Q.incl ((φ.val.app U (P.liftKernel β.hom U g)) : N.val.obj U) := fun U g => by
    have hg : (g : (freeAlgebraSheaf J A E).obj.obj U) ∈
        kernelIdeal (presentation J A O a E α).hom U := by
      have h1 : (β.hom ≫ P.reduction).hom.app U g.1 =
          (presentation J A O a E α).hom.app U g.1 :=
        congrArg (fun t : freeAlgebraSheaf J A E ⟶ O => t.hom.app U g.1) β.hom_reduction
      exact h1.symm.trans g.2
    rw [← β'.incl_restriction U ⟨g.1, hg⟩, h U ⟨g.1, hg⟩]
    rfl
  refine ⟨P.mapAlongOfLift β.hom (freeAlgebraSheafCoefficientMap J A E) β.coefficientMap_hom φ
    β'.hom hq β'.coefficientMap_hom hψ, ext_of_hom ?_⟩
  rw [comp_hom]
  exact P.lift_mapAlongOfLift_hom β.hom _ _ φ β'.hom hq β'.coefficientMap_hom hψ

/-- **Step 3 of the proof of [Stacks Project, Tag 08UG] for extensions by the same module**:
two lifts with the same restriction to the relations are carried one to the other by a
morphism of extensions. -/
theorem exists_hom_comp_eq {P' : AlgebraExtension a M} (β : GeneratorLift α P)
    (β' : GeneratorLift α P')
    (h : ∀ (U : Cᵒᵖ) (g : kernelIdeal (presentation J A O a E α).hom U),
      β'.restriction U g = β.restriction U g) :
    ∃ k : P ⟶ P', β.comp k = β' :=
  exists_mapAlong_comp_eq (φ := 𝟙 M) β β' h

end Determined

/-! ### The conormal map of a lift -/

section Conormal

variable (β : GeneratorLift α P)

/-- **The restriction datum of a lift**: the restriction `ℐ ⟶ ℳ` of `β` is linear over
`𝒜[ℰ]` acting through `𝒜[ℰ] ⟶ 𝒪` and natural. -/
noncomputable def idealRestriction :
    IdealRestriction.{u, u, u, u} (presentation J A O a E α) M where
  app U := AddMonoidHom.mk' (β.restriction U) fun g h => P.incl_injective (by
    rw [P.incl_add, incl_restriction, incl_restriction, incl_restriction]
    exact map_add (β.hom.hom.app U).hom _ _)
  app_smul U r g := P.incl_injective (by
    change P.incl (β.restriction U (r • g)) =
      P.incl (scalar ((presentation J A O a E α).hom.app U r) • β.restriction U g)
    have hr : (β.hom ≫ P.reduction).hom.app U r = (presentation J A O a E α).hom.app U r :=
      congrArg (fun t : freeAlgebraSheaf J A E ⟶ O => t.hom.app U r) β.hom_reduction
    rw [← hr, incl_restriction]
    change β.hom.hom.app U (r * (g : (freeAlgebraSheaf J A E).obj.obj U)) = _
    rw [map_mul]
    change _ = P.incl (scalar (P.reduction.hom.app U (β.hom.hom.app U r)) • β.restriction U g)
    rw [← P.mul_incl, incl_restriction])
  app_map {U V} f g := P.incl_injective (by
    refine (incl_restriction β V _).trans ?_
    refine Eq.trans ?_ (P.incl_naturality f (β.restriction U g)).symm
    rw [incl_restriction]
    exact NatTrans.naturality_apply β.hom.hom f (g : (freeAlgebraSheaf J A E).obj.obj U))

/-- The restriction datum of `β` evaluates to the restriction of `β` to `ℐ`. -/
@[simp]
theorem idealRestriction_app (U : Cᵒᵖ) (g : kernelIdeal (presentation J A O a E α).hom U) :
    β.idealRestriction.app U g = β.restriction U g :=
  rfl

/-- **The conormal map of a lift**, `δ_β : ℐ/ℐ² ⟶ ℳ`. -/
noncomputable def conormalHom :
    (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ ⟶ tensorModule M :=
  conormalDesc (presentation J A O a E α) (tensorModule M) β.idealRestriction

/-- The conormal map `δ_β` sends the class of a local relation `g` to `β(g)`. -/
theorem conormalHom_relClass (U : Cᵒᵖ) (g : kernelIdeal (presentation J A O a E α).hom U) :
    β.conormalHom.val.app U (relClass U g) = β.restriction U g :=
  Stacks.Sites.Conormal.conormalDesc_conormalClass _ _ _ _ _ _ _

/-- Two morphisms out of `ℐ/ℐ²` agreeing on the classes of local relations are equal. -/
theorem conormal_ext
    {f₁ f₂ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ ⟶ tensorModule N}
    (h : ∀ (U : Cᵒᵖ) (g : kernelIdeal (presentation J A O a E α).hom U),
      f₁.val.app U (relClass U g) = f₂.val.app U (relClass U g)) : f₁ = f₂ :=
  Stacks.Sites.Conormal.conormal_hom_ext _ _ h

/-- **Step 2 of the proof of [Stacks Project, Tag 08UG], on `ℐ/ℐ²`**: transporting a lift
along a morphism of extensions along `φ` composes its conormal map with `φ`. -/
theorem conormalHom_comp {φ : M ⟶ N} (k : MapAlong φ P Q) :
    (β.comp k).conormalHom = β.conormalHom ≫ tensorMap φ :=
  conormal_ext fun U g => by
    rw [conormalHom_relClass, restriction_comp]
    exact (congrArg (φ.val.app U) (β.conormalHom_relClass U g)).symm

end Conormal

/-! ### Shifting a lift -/

section Shift

variable (β : GeneratorLift α P)
  (θ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ tensorModule M)

/-- **The shift `β + θ` of a lift** by a morphism out of the degree `0` term of `NL(α)`:
`e ↦ β(e) + θ(1 ⊗ d e)`. -/
noncomputable def shift : GeneratorLift α P where
  lift :=
    { app := fun U => TypeCat.ofHom fun e => (show P.extension.obj.obj U from β.lift.app U e) +
        P.incl (θ.val.app U (dTensor U ((freeAlgebraSheafVariable J A E).app U e)))
      naturality := fun U V f => by
        ext e
        have h1 := NatTrans.naturality_apply β.lift f e
        have h2 := NatTrans.naturality_apply (freeAlgebraSheafVariable J A E) f e
        have h3 := Stacks.Sites.Conormal.tensorDifferential_map.{u, u, u, u} J A
          (freeAlgebraSheaf J A E) O (freeAlgebraSheafCoefficientMap J A E)
          (presentation J A O a E α) f ((freeAlgebraSheafVariable J A E).app U e)
        have h4 := PresheafOfModules.naturality_apply θ.val f
          (dTensor U ((freeAlgebraSheafVariable J A E).app U e))
        have h5 := P.incl_naturality f
          (θ.val.app U (dTensor U ((freeAlgebraSheafVariable J A E).app U e)))
        refine Eq.trans (congrArg₂ (fun (x y : P.extension.obj.obj V) => x + y) h1
          ((congrArg P.incl ((congrArg (θ.val.app V) ((congrArg (dTensor V) h2).trans h3)).trans
            h4)).trans h5)) ?_
        exact (map_add (P.extension.obj.map f).hom _ _).symm }
  lift_comp := by
    ext U e
    change P.reduction.hom.app U ((show P.extension.obj.obj U from β.lift.app U e) +
      P.incl _) = α.app U e
    rw [map_add, P.reduction_incl, add_zero]
    exact congrArg (fun t => t.app U e) β.lift_comp

/-- The shift `β + θ` sends a local section `e` of `ℰ` to `β(e) + θ(1 ⊗ d e)`. -/
theorem shift_lift_app (U : Cᵒᵖ) (e : E.obj U) :
    (β.shift θ).lift.app U e = (show P.extension.obj.obj U from β.lift.app U e) +
      P.incl (θ.val.app U (dTensor U ((freeAlgebraSheafVariable J A E).app U e))) :=
  rfl

/-- Shifting by zero does nothing. -/
theorem shift_zero : β.shift 0 = β := by
  ext U e
  show (show P.extension.obj.obj U from β.lift.app U e) + P.incl 0 = β.lift.app U e
  rw [P.incl_zero, add_zero]

/-- Shifts add up. -/
theorem shift_shift
    (θ' : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ tensorModule M) :
    (β.shift θ).shift θ' = β.shift (θ + θ') := by
  ext U e
  show (show P.extension.obj.obj U from β.lift.app U e) + P.incl _ + P.incl _ =
    (show P.extension.obj.obj U from β.lift.app U e) + P.incl _
  rw [add_assoc, ← P.incl_add]
  rfl

omit [HasWeakSheafify J CommRingCat]
  [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom] in
/-- Composing two transports of a lift is transporting along the composite. -/
theorem comp_comp {L : SheafOfModules.{u} (underlyingRingSheaf O)} {R : AlgebraExtension a L}
    {φ : M ⟶ N} {ψ : N ⟶ L} {χ : M ⟶ L} (k : MapAlong φ P Q) (k' : MapAlong ψ Q R)
    (h : φ ≫ ψ = χ) : (β.comp k).comp k' = β.comp (k.comp k' h) :=
  rfl

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}]

/-- **The homomorphism of a shifted lift**: `(β + θ)(y) = β(y) + θ(1 ⊗ d y)`. -/
theorem shift_hom_app (U : Cᵒᵖ) (y : (freeAlgebraSheaf J A E).obj.obj U) :
    (β.shift θ).hom.hom.app U y = β.hom.hom.app U y + P.incl (θ.val.app U (dTensor U y)) := by
  obtain ⟨θ', hθ'⟩ := β.exists_tensorHom_sub (β.shift θ)
  have heq : θ' = θ := tensorHom_ext fun V e => P.incl_injective (by
    rw [hθ', incl_diff]
    rw [hom_app_variable, hom_app_variable, shift_lift_app, add_sub_cancel_left])
  subst heq
  rw [hθ', incl_diff, add_sub_cancel]

/-- **The restriction of a shifted lift**: `δ_{β + θ} = δ_β + θ ∘ d` on local relations. -/
theorem shift_restriction (U : Cᵒᵖ) (g : kernelIdeal (presentation J A O a E α).hom U) :
    (β.shift θ).restriction U g = β.restriction U g +
      θ.val.app U ((presentationConormalSequence.{u, u, u, u} J A O a E α).f.val.app U
        (relClass U g)) :=
  P.incl_injective (by
    rw [incl_restriction, shift_hom_app, P.incl_add, incl_restriction, f_relClass])

/-- **The conormal map of a shifted lift**: `δ_{β + θ} = δ_β + θ ∘ d`. -/
theorem conormalHom_shift :
    (β.shift θ).conormalHom =
      β.conormalHom + (presentationConormalSequence.{u, u, u, u} J A O a E α).f ≫ θ :=
  conormal_ext fun U g => by
    rw [conormalHom_relClass, shift_restriction]
    exact (congrArg (· + _) (β.conormalHom_relClass U g)).symm

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- Transporting a shifted lift along a morphism of extensions along `φ` is the transported
lift shifted by `φ ∘ θ`. -/
theorem shift_comp {φ : M ⟶ N} (k : MapAlong φ P Q) :
    (β.shift θ).comp k = (β.comp k).shift (θ ≫ tensorMap φ) := by
  ext U e
  show k.hom.hom.app U ((show P.extension.obj.obj U from β.lift.app U e) + P.incl _) =
    k.hom.hom.app U (β.lift.app U e) + _
  rw [map_add, k.kernel_comm]
  rfl

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Shifting is free**: a shift by `θ` fixes the lift only for `θ = 0`. -/
theorem shift_injective {θ θ' : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶
    tensorModule M} (h : β.shift θ = β.shift θ') : θ = θ' :=
  tensorHom_ext fun U e => P.incl_injective (add_left_cancel
    (congrArg (fun γ : GeneratorLift α P => γ.lift.app U e) h :))

/-- **Any two lifts differ by a shift.** -/
theorem exists_eq_shift (β' : GeneratorLift α P) :
    ∃ θ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ tensorModule M,
      β' = β.shift θ := by
  obtain ⟨θ, hθ⟩ := β.exists_tensorHom_sub β'
  refine ⟨θ, ext ?_⟩
  ext U e
  show β'.lift.app U e = (show P.extension.obj.obj U from β.lift.app U e) + P.incl _
  rw [hθ, incl_diff, hom_app_variable, hom_app_variable, add_sub_cancel]

end Shift

end GeneratorLift

end Deformation.AlgebraExtension

end
