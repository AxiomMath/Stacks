module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Products
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.RingedPoint

/-!
# Reflectivity of the derived-complete objects on a ringed site

Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊂ 𝒪` a sheaf of ideals. [Stacks, Tag 099F] asserts, for
`ℐ` of finite type, that the inclusion of the derived-complete objects
`D_comp(𝒪) ⥤ D(𝒪)` has a left adjoint. This file contains two things: the reduction of that
assertion to the construction of a completion functor, at the names and in the universes in
which the assertion is stated; and the assertion itself for a sheaf of ideals whose local
sections all vanish, which is the case in which a completion functor is available, namely the
identity.

## Main definitions

* `AlgebraicGeometry.RingedSite.zeroSubmodule`: the zero sheaf of ideals of the structure
  sheaf, that is, the bottom submodule of the unit sheaf of modules.

## Main results

* `Stacks.SheafOfModules.terminalSectionToEnd_zero`: multiplication by the zero section over a
  terminal object is the zero endomorphism.
* `AlgebraicGeometry.RingedSite.isZero_zeroSubmodule` and
  `AlgebraicGeometry.RingedSite.isFiniteType_zeroSubmodule`: the zero sheaf of ideals is a zero
  object, and is of finite type.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_of_forall_eq_zero`: every object of `D(𝒪)` is
  derived complete along a sheaf of ideals whose local sections all vanish.
* `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_completionFunctor`: the
  inclusion of the derived-complete objects has a left adjoint as soon as there is an
  endofunctor `Φ` of `D(𝒪)` with a map `η : 𝟭 ⟶ Φ` such that every `Φ K` is derived complete,
  `η_K` is invertible on derived-complete `K`, and `Φ η_K = η_{Φ K}`.
* `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_zeroSubmodule`: the
  inclusion of the derived-complete objects along the zero sheaf of ideals has a left adjoint.
* `AlgebraicGeometry.RingedSite.chaoticPoint` and
  `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_chaoticPoint`: the previous
  statement at a ringed site exhibited from nothing, so that it is not vacuous.

## Implementation notes

The reduction is the specialisation of
`Stacks.Algebraization.isRightAdjoint_ι_of_idempotentCompletionFunctor` to the object property
`AlgebraicGeometry.RingedSite.IsDerivedComplete` of [Stacks, Tag 0999]. Its three hypotheses
are exactly the three conditions the source's proof verifies, the third being the one that the
two-object counterexample of `StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletion.lean`
shows cannot be dropped. What is not reduced is the construction of `(Φ, η)` itself: that is
[Stacks, Tag 099E], `AlgebraicGeometry.RingedSite.exists_isGlobalExtendedCech` of
`FiniteTypeExtendedCech.lean`, and the tag is
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete` of `FiniteTypeReflector.lean`.

The universes are those of [Stacks, Tag 099F]: the site is a `RingedSite.{u, v, max u v}` and
the coefficient universe of the sheaves of modules is `max u v`, which is where the ambient
`Abelian (SheafOfModules 𝒪)` instance is found. The derived category is the standard model, as
it is in the definition of the predicate; the pin is forced rather than chosen, since the
predicate carries it in its type and no free-model version of it exists.

The zero sheaf of ideals makes the whole statement non-vacuous: its sections vanish, so the
derived-complete objects are all of `D(𝒪)` and the identity functor is a completion functor;
and it is of finite type, which is the instance hypothesis of [Stacks, Tag 099F] and had no
inhabitant anywhere — the only instance of `SheafOfModules.IsFiniteType` in Mathlib is the one
deduced from `IsFinitePresentation`, which is not available here. The generating sections are
the empty family over the covering of the terminal object by all objects of the site, which is
legitimate because the zero sheaf of ideals is a zero object.

No `@[stacks]` attribute is attached: Tag 0999 is carried by the predicate itself, and Tag 099F
is not proved here.

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u v w

namespace Stacks.SheafOfModules

/-- Multiplication by the zero section over a terminal object is the zero endomorphism. -/
theorem terminalSectionToEnd_zero {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [∀ U, IsMulCommutative (R.obj.obj U)]
    (T : C) (hT : IsTerminal T) :
    terminalSectionToEnd.{v, u, w, w} R T hT 0 = 0 := by
  ext M U x
  rw [terminalSectionToEnd_apply, map_zero, zero_smul]
  simp [show ((0 : M ⟶ M)).val = 0 from rfl]

/-- The empty family of generating sections of a zero sheaf of modules. -/
def emptyGeneratingSections {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : _root_.SheafOfModules.{w} R) (hM : IsZero M) : M.GeneratingSections where
  I := PEmpty.{w + 1}
  s := fun e => e.elim
  epi := { left_cancellation := fun g h _ => hM.eq_of_src g h }

/-- The empty family of generating sections of a zero sheaf of modules is of finite type. -/
theorem isFiniteType_emptyGeneratingSections {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : _root_.SheafOfModules.{w} R) (hM : IsZero M) :
    (emptyGeneratingSections M hM).IsFiniteType :=
  { finite := inferInstanceAs (Finite PEmpty.{w + 1}) }

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v})

section ZeroIdeal

/-- The zero sheaf of ideals of the structure sheaf of a ringed site: the bottom submodule of
the unit sheaf of modules. Its membership condition is local because the structure sheaf is
separated. -/
def zeroSubmodule :
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).Submodule where
  toSubmodule := ⊥
  isSheaf := by
    intro U s hs
    have hsheaf : Presieve.IsSheaf X.J
        ((SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.presheaf ⋙
          forget AddCommGrpCat) :=
      (CategoryTheory.isSheaf_iff_isSheaf_of_type X.J _).mp
        (GrothendieckTopology.HasSheafCompose.isSheaf _
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).isSheaf)
    simp only [PresheafOfModules.Submodule.bot_obj, Pi.bot_apply, Submodule.mem_bot]
    refine (hsheaf.isSeparated _ hs).ext (t₂ := 0) ?_
    intro Y f hf
    have h0 : ((SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.presheaf ⋙
        forget AddCommGrpCat).map f.op s = 0 := hf
    rw [h0]
    exact (map_zero (ConcreteCategory.hom
      ((SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.presheaf.map
        f.op))).symm

/-- Every local section of the zero sheaf of ideals vanishes. -/
theorem zeroSubmodule_eq_zero_of_mem (U : X.C)
    (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U))
    (hf : f ∈ (zeroSubmodule X).toSubmodule.obj (op U)) : f = 0 :=
  have h : f ∈ (⊥ : Submodule (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U))
    ((SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.obj (op U))) := hf
  (Submodule.mem_bot _).mp h

/-- The zero sheaf of ideals is a zero object of the category of sheaves of modules. -/
theorem isZero_zeroSubmodule : IsZero ((zeroSubmodule X).toSheafOfModules) := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  have hx : x = 0 := Subtype.ext ((Submodule.mem_bot _).mp x.2)
  simp [hx, show ((0 : (zeroSubmodule X).toSheafOfModules ⟶
    (zeroSubmodule X).toSheafOfModules)).val = 0 from rfl]

/-- The restriction of the zero sheaf of ideals to a slice site is a zero object. -/
theorem isZero_zeroSubmodule_over (U : X.C) :
    IsZero (((zeroSubmodule X).toSheafOfModules).over U) :=
  Functor.map_isZero
    (SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
    (isZero_zeroSubmodule X)

/-- The local generating data of the zero sheaf of ideals: the empty family of sections over the
covering of the terminal object by all the objects of the site. -/
def zeroSubmoduleLocalGenerators :
    ((zeroSubmodule X).toSheafOfModules).LocalGeneratorsData where
  I := X.C
  X := id
  coversTop := by
    intro U
    convert X.J.top_mem U
    rw [eq_top_iff]
    intro V f _
    exact (Sieve.mem_ofObjects_iff _ _).mpr ⟨V, ⟨CategoryStruct.id V⟩⟩
  generators i :=
    Stacks.SheafOfModules.emptyGeneratingSections
      (((zeroSubmodule X).toSheafOfModules).over i) (isZero_zeroSubmodule_over X i)

/-- The zero sheaf of ideals is of finite type: it is generated by the empty family of
sections. -/
instance isFiniteType_zeroSubmodule :
    ((zeroSubmodule X).toSheafOfModules).IsFiniteType where
  exists_localGeneratorsData :=
    ⟨zeroSubmoduleLocalGenerators X,
      { isFiniteType := fun (i : X.C) =>
          Stacks.SheafOfModules.isFiniteType_emptyGeneratingSections.{max u v, v, max u v}
            (((zeroSubmodule X).toSheafOfModules).over i) (isZero_zeroSubmodule_over X i) }⟩

end ZeroIdeal

section Reflection

attribute [local instance] HasDerivedCategory.standard

variable (I : SheafOfModules.Submodule
  (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **Every object is derived complete along a sheaf of ideals with vanishing sections.** The
scalar whose Milnor difference map has to be invertible is multiplication by a local section of
the sheaf of ideals; when that section is zero the scalar is zero, hence nilpotent. -/
theorem isDerivedComplete_of_forall_eq_zero
    (hI : ∀ (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)),
      f ∈ I.toSubmodule.obj (op U) → f = 0)
    (K : DerivedCategory
      (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    IsDerivedComplete.{u, v, max u v, max u v} X I K := by
  intro V f hf
  obtain rfl := hI V f hf
  let RV := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over V
  let A := SheafOfModules.{max u v} RV
  let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
  let : ∀ W : (Over V)ᵒᵖ, IsMulCommutative (RV.obj.obj W) := fun W ↦ by
    show IsMulCommutative (X.O.obj.obj (op W.unop.left))
    infer_instance
  have hLim : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  have hColim : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
  have hProd : HasProductsOfShape ℕ (DerivedCategory A) :=
    hasProductsOfShape_nat_derivedCategory_over.{u, v, max u v} X V
  refine ⟨inferInstance, hLim, hColim, hProd, ?_⟩
  have hc : Stacks.SheafOfModules.terminalSectionToEnd
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over V)
      (Over.mk (𝟙 V)) Over.mkIdTerminal
      (0 : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op V)) = 0 :=
    Stacks.SheafOfModules.terminalSectionToEnd_zero _ _ _
  refine isDerivedCompleteAt_of_isNilpotent ⟨1, ?_⟩
  exact (pow_one _).trans
    ((congrArg (fun c : CatCenter A => c • (1 : End _)) hc).trans (zero_smul _ _))

/-- **[Stacks, Tag 099F] reduced to the construction of a completion functor.** If there is an
endofunctor `Φ` of `D(𝒪)` together with `η : 𝟭 ⟶ Φ` such that `Φ K` is derived complete for
every `K`, that `η_K` is invertible whenever `K` is derived complete, and that
`Φ η_K = η_{Φ K}`, then the inclusion of the derived-complete objects into `D(𝒪)` has a left
adjoint. The construction of `(Φ, η)` is not done here; for a sheaf of ideals of finite type it
is `R𝑆heafHom_𝒪(K, -)` for the map `K ⟶ 𝒪` of
`AlgebraicGeometry.RingedSite.exists_isGlobalExtendedCech` of `FiniteTypeExtendedCech.lean`, and
the tag is `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete` of
`FiniteTypeReflector.lean`. -/
theorem isRightAdjoint_ι_isDerivedComplete_of_completionFunctor
    {Φ : DerivedCategory (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⥤
      DerivedCategory (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (η : 𝟭 (DerivedCategory
      (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ⟶ Φ)
    (hΦ : ∀ K, IsDerivedComplete.{u, v, max u v, max u v} X I (Φ.obj K))
    (hη : ∀ K, IsDerivedComplete.{u, v, max u v, max u v} X I K → IsIso (η.app K))
    (hcomm : ∀ K, Φ.map (η.app K) = η.app (Φ.obj K)) :
    (ObjectProperty.ι (IsDerivedComplete.{u, v, max u v, max u v} X I)).IsRightAdjoint :=
  Stacks.Algebraization.isRightAdjoint_ι_of_idempotentCompletionFunctor η hΦ hη hcomm

/-- The conclusion of [Stacks, Tag 099F] for a sheaf of ideals whose local sections all vanish:
there every object is derived complete, so the identity functor is a completion functor. -/
theorem isRightAdjoint_ι_isDerivedComplete_of_forall_eq_zero
    (hI : ∀ (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)),
      f ∈ I.toSubmodule.obj (op U) → f = 0) :
    (ObjectProperty.ι (IsDerivedComplete.{u, v, max u v, max u v} X I)).IsRightAdjoint :=
  isRightAdjoint_ι_isDerivedComplete_of_completionFunctor X I
    (𝟙 (𝟭 (DerivedCategory
      (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))))
    (fun _ ↦ isDerivedComplete_of_forall_eq_zero X I hI _)
    (fun K _ ↦ by simpa using (inferInstance : IsIso (𝟙 K)))
    (fun _ ↦ rfl)

/-- The conclusion of [Stacks, Tag 099F] for the zero sheaf of ideals, which is of finite type
and so is an instance of the hypothesis of that statement. -/
theorem isRightAdjoint_ι_isDerivedComplete_zeroSubmodule :
    (ObjectProperty.ι
      (IsDerivedComplete.{u, v, max u v, max u v} X (zeroSubmodule X))).IsRightAdjoint :=
  isRightAdjoint_ι_isDerivedComplete_of_forall_eq_zero X _ (zeroSubmodule_eq_zero_of_mem X)

end Reflection

section ChaoticPoint

attribute [local instance] HasDerivedCategory.standard

/-- The ringed point on the chaotic one-object site, with the trivial ring: a ringed site at the
universe shape of [Stacks, Tag 099F], exhibited so that the statements above are not vacuous. -/
def chaoticPoint : RingedSite.{u, u, u} where
  C := Discrete PUnit.{u + 1}
  J := GrothendieckTopology.trivial (Discrete PUnit.{u + 1})
  O := (sheafBotEquivalence (C := Discrete PUnit.{u + 1}) CommRingCat.{u}).inverse.obj
    ((Functor.const (Discrete PUnit.{u + 1})ᵒᵖ).obj (CommRingCat.of PUnit.{u + 1}))

/-- The hypothesis of [Stacks, Tag 099F] is inhabited at a concrete ringed site. -/
instance isFiniteType_zeroSubmodule_chaoticPoint :
    ((zeroSubmodule chaoticPoint.{u}).toSheafOfModules).IsFiniteType :=
  isFiniteType_zeroSubmodule _

/-- The conclusion of [Stacks, Tag 099F] holds at a concrete ringed site, for a concrete sheaf
of ideals satisfying its finite type hypothesis. -/
theorem isRightAdjoint_ι_isDerivedComplete_chaoticPoint :
    (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u}
      chaoticPoint.{u} (zeroSubmodule chaoticPoint.{u}))).IsRightAdjoint :=
  isRightAdjoint_ι_isDerivedComplete_zeroSubmodule _

end ChaoticPoint

end AlgebraicGeometry.RingedSite

end
