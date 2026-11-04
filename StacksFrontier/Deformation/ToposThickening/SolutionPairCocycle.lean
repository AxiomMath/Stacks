module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClassVanishing
public import StacksFrontier.Deformation.ToposThickening.SolutionPairObstruction

/-!
# The obstruction class of two solutions is a cocycle

For three solutions `𝒪'₁, 𝒪'₂, 𝒪'₃` of the square-zero extension problem of
[Stacks Project, Tag 08UF], the obstruction classes of the pairs satisfy

`o(𝒪'₁, 𝒪'₂) + o(𝒪'₂, 𝒪'₃) = o(𝒪'₁, 𝒪'₃)`.

The three classes are computed on one family of generators, the sheaf of sets
`ℰ = 𝒪'₁ ×_𝒪 𝒪'₂ ×_𝒪 𝒪'₃` with its three projections. On a local section `p` of the kernel `ℐ'`
of `f⁻¹𝒪_{B'}[ℰ] ⟶ 𝒪` the three difference maps are `φ₂(p) - φ₁(p)`, `φ₃(p) - φ₂(p)` and
`φ₃(p) - φ₁(p)`, so the first two add up to the third. The first Ext class of a conormal
homomorphism is additive, and the class of a pair does not depend on the family of generators.

## Main definitions

* `RingedToposExtensionProblem.CompatibleFirstOrderThickening.tripleGenerators`: the sheaf of
  sets `𝒪'₁ ×_𝒪 𝒪'₂ ×_𝒪 𝒪'₃`.
* `RingedToposExtensionProblem.CompatibleFirstOrderThickening.tripleDatum₁₂`, `tripleDatum₂₃`,
  `tripleDatum₁₃`: the three pair data on it.

## Main results

* `RingedToposExtensionProblem.CompatibleFirstOrderThickening.pairDatumObstruction_add`: the
  cocycle identity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u w v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf baseChange)
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal conormalDesc)

variable {X : RingedTopos.{v, u, max u v w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B}

attribute [local instance] CategoryTheory.Sheaf.wEqualsLocallyBijective_commRingCat

namespace CompatibleFirstOrderThickening

variable (Q₁ Q₂ Q₃ : S.CompatibleFirstOrderThickening)

/-! ### The fibre product of three solutions -/

/-- The sheaf of sets `ℰ = 𝒪'₁ ×_𝒪 𝒪'₂ ×_𝒪 𝒪'₃` underlying the fibre product of three thickened
structure sheaves over `𝒪`. -/
def tripleGenerators : X.Cᵒᵖ ⥤ Type (max u v w) where
  obj U := {x : Q₁.extension.obj.obj U × Q₂.extension.obj.obj U × Q₃.extension.obj.obj U //
    Q₁.reduction.hom.app U x.1 = Q₂.reduction.hom.app U x.2.1 ∧
      Q₂.reduction.hom.app U x.2.1 = Q₃.reduction.hom.app U x.2.2}
  map {U V} g := TypeCat.ofHom fun x ↦ ⟨(Q₁.extension.obj.map g x.1.1,
    Q₂.extension.obj.map g x.1.2.1, Q₃.extension.obj.map g x.1.2.2),
      by rw [NatTrans.naturality_apply, NatTrans.naturality_apply, x.2.1],
      by rw [NatTrans.naturality_apply, NatTrans.naturality_apply, x.2.2]⟩
  map_id U := by
    ext x
    · exact CategoryTheory.congr_fun (Q₁.extension.obj.map_id U) x.1.1
    · exact CategoryTheory.congr_fun (Q₂.extension.obj.map_id U) x.1.2.1
    · exact CategoryTheory.congr_fun (Q₃.extension.obj.map_id U) x.1.2.2
  map_comp f g := by
    ext x
    · exact CategoryTheory.congr_fun (Q₁.extension.obj.map_comp f g) x.1.1
    · exact CategoryTheory.congr_fun (Q₂.extension.obj.map_comp f g) x.1.2.1
    · exact CategoryTheory.congr_fun (Q₃.extension.obj.map_comp f g) x.1.2.2

/-- The first projection `𝒪'₁ ×_𝒪 𝒪'₂ ×_𝒪 𝒪'₃ ⟶ 𝒪'₁`. -/
def tripleFst : tripleGenerators Q₁ Q₂ Q₃ ⟶ underlyingPresheaf X.J Q₁.extension where
  app _ := TypeCat.ofHom fun x ↦ x.1.1
  naturality _ _ _ := rfl

/-- The second projection `𝒪'₁ ×_𝒪 𝒪'₂ ×_𝒪 𝒪'₃ ⟶ 𝒪'₂`. -/
def tripleSnd : tripleGenerators Q₁ Q₂ Q₃ ⟶ underlyingPresheaf X.J Q₂.extension where
  app _ := TypeCat.ofHom fun x ↦ x.1.2.1
  naturality _ _ _ := rfl

/-- The third projection `𝒪'₁ ×_𝒪 𝒪'₂ ×_𝒪 𝒪'₃ ⟶ 𝒪'₃`. -/
def tripleThd : tripleGenerators Q₁ Q₂ Q₃ ⟶ underlyingPresheaf X.J Q₃.extension where
  app _ := TypeCat.ofHom fun x ↦ x.1.2.2
  naturality _ _ _ := rfl

/-- The map `𝒪'₁ ×_𝒪 𝒪'₂ ×_𝒪 𝒪'₃ ⟶ 𝒪`. -/
abbrev tripleMap : tripleGenerators Q₁ Q₂ Q₃ ⟶ underlyingPresheaf X.J X.O :=
  tripleFst Q₁ Q₂ Q₃ ≫ Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w})

/-- The second projection lies over the map to `𝒪`. -/
theorem tripleSnd_comp_reduction :
    tripleSnd Q₁ Q₂ Q₃ ≫ Functor.whiskerRight Q₂.reduction.hom (forget CommRingCat.{max u v w}) =
      tripleMap Q₁ Q₂ Q₃ := by
  ext U x
  exact x.2.1.symm

/-- The third projection lies over the map to `𝒪`. -/
theorem tripleThd_comp_reduction :
    tripleThd Q₁ Q₂ Q₃ ≫ Functor.whiskerRight Q₃.reduction.hom (forget CommRingCat.{max u v w}) =
      tripleMap Q₁ Q₂ Q₃ := by
  ext U x
  exact (x.2.1.trans x.2.2).symm

/-- The map `𝒪'₁ ×_𝒪 𝒪'₂ ×_𝒪 𝒪'₃ ⟶ 𝒪` is locally surjective, the three reductions being so. -/
theorem isLocallySurjective_tripleMap :
    Presheaf.IsLocallySurjective X.J (tripleMap Q₁ Q₂ Q₃) where
  imageSieve_mem {U} s := by
    have h₁ := (Presheaf.isLocallySurjective_iff_whisker_forget X.J Q₁.reduction.hom).mp
      Q₁.locallySurjective
    have h₂ := (Presheaf.isLocallySurjective_iff_whisker_forget X.J Q₂.reduction.hom).mp
      Q₂.locallySurjective
    have h₃ := (Presheaf.isLocallySurjective_iff_whisker_forget X.J Q₃.reduction.hom).mp
      Q₃.locallySurjective
    refine X.J.superset_covering ?_ (X.J.intersection_covering
      (Presheaf.imageSieve_mem X.J
        (Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w})) s)
      (X.J.intersection_covering
        (Presheaf.imageSieve_mem X.J
          (Functor.whiskerRight Q₂.reduction.hom (forget CommRingCat.{max u v w})) s)
        (Presheaf.imageSieve_mem X.J
          (Functor.whiskerRight Q₃.reduction.hom (forget CommRingCat.{max u v w})) s)))
    rintro V f ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩, ⟨q₃, hq₃⟩⟩
    exact ⟨⟨(q₁, q₂, q₃), hq₁.trans hq₂.symm, hq₂.trans hq₃.symm⟩, hq₁⟩

/-- The presentation `f⁻¹𝒪_B[𝒪'₁ ×_𝒪 𝒪'₂ ×_𝒪 𝒪'₃] ⟶ 𝒪` is surjective. -/
instance isLocallySurjective_triplePresentation :
    Presheaf.IsLocallySurjective X.J
      (Stacks.SheafOfModules.presentation X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
        (tripleGenerators Q₁ Q₂ Q₃) (tripleMap Q₁ Q₂ Q₃)).hom := by
  have := isLocallySurjective_tripleMap Q₁ Q₂ Q₃
  exact (Presheaf.isLocallySurjective_iff_whisker_forget X.J _).mpr
    (Presheaf.isLocallySurjective_of_isLocallySurjective_fac X.J
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O (tripleGenerators Q₁ Q₂ Q₃)
        S.f.fSharpInverseImage (tripleMap Q₁ Q₂ Q₃)))

/-- The pair datum of `(𝒪'₁, 𝒪'₂)` on the fibre product of the three solutions. -/
abbrev tripleDatum₁₂ : PairDatum Q₁ Q₂ where
  E := tripleGenerators Q₁ Q₂ Q₃
  α := tripleMap Q₁ Q₂ Q₃
  β₁ := tripleFst Q₁ Q₂ Q₃
  β₂ := tripleSnd Q₁ Q₂ Q₃
  comm₁ := rfl
  comm₂ := tripleSnd_comp_reduction Q₁ Q₂ Q₃
  isLocallySurjective := isLocallySurjective_triplePresentation Q₁ Q₂ Q₃

/-- The pair datum of `(𝒪'₂, 𝒪'₃)` on the fibre product of the three solutions. -/
abbrev tripleDatum₂₃ : PairDatum Q₂ Q₃ where
  E := tripleGenerators Q₁ Q₂ Q₃
  α := tripleMap Q₁ Q₂ Q₃
  β₁ := tripleSnd Q₁ Q₂ Q₃
  β₂ := tripleThd Q₁ Q₂ Q₃
  comm₁ := tripleSnd_comp_reduction Q₁ Q₂ Q₃
  comm₂ := tripleThd_comp_reduction Q₁ Q₂ Q₃
  isLocallySurjective := isLocallySurjective_triplePresentation Q₁ Q₂ Q₃

/-- The pair datum of `(𝒪'₁, 𝒪'₃)` on the fibre product of the three solutions. -/
abbrev tripleDatum₁₃ : PairDatum Q₁ Q₃ where
  E := tripleGenerators Q₁ Q₂ Q₃
  α := tripleMap Q₁ Q₂ Q₃
  β₁ := tripleFst Q₁ Q₂ Q₃
  β₂ := tripleThd Q₁ Q₂ Q₃
  comm₁ := rfl
  comm₂ := tripleThd_comp_reduction Q₁ Q₂ Q₃
  isLocallySurjective := isLocallySurjective_triplePresentation Q₁ Q₂ Q₃

/-! ### Adding the differences -/

/-- The conormal sheaf `ℐ/ℐ²` of the presentation `f⁻¹𝒪_B[ℰ] ⟶ 𝒪` of the fibre product of the
three solutions. -/
noncomputable abbrev tripleConormal :
    SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max u v w, w} X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
    (tripleGenerators Q₁ Q₂ Q₃) (tripleMap Q₁ Q₂ Q₃)).X₁

/-- On a local section `p` of `ℐ'`, the differences `φ₂(p) - φ₁(p)` and `φ₃(p) - φ₂(p)` add up
to `φ₃(p) - φ₁(p)`. -/
theorem tripleDatum_difference_add {U : X.Cᵒᵖ}
    (p : kernelIdeal (tripleDatum₁₃ Q₁ Q₂ Q₃).restrictedPresentation.hom U) :
    (tripleDatum₁₂ Q₁ Q₂ Q₃).difference.app U p + (tripleDatum₂₃ Q₁ Q₂ Q₃).difference.app U p =
      (tripleDatum₁₃ Q₁ Q₂ Q₃).difference.app U p :=
  sub_add_sub_cancel' _ _ _

/-- The descended differences of the three pairs add up in the same way. -/
theorem tripleDatum_descendedDifference_add {U : X.Cᵒᵖ}
    (x : kernelIdeal (tripleDatum₁₃ Q₁ Q₂ Q₃).presentation.hom U) :
    (tripleDatum₁₂ Q₁ Q₂ Q₃).descendedDifference.app U x +
        (tripleDatum₂₃ Q₁ Q₂ Q₃).descendedDifference.app U x =
      (tripleDatum₁₃ Q₁ Q₂ Q₃).descendedDifference.app U x := by
  symm
  refine Stacks.Sites.Conormal.IdealRestriction.descendApp_eq
    (tripleDatum₁₃ Q₁ Q₂ Q₃).difference
    (fun _ k hk ↦ (tripleDatum₁₃ Q₁ Q₂ Q₃).difference_eq_zero_of_baseChange k hk) x _
    (Presheaf.imageSieve (baseChange X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction)
        (tripleGenerators Q₁ Q₂ Q₃)).hom (U := U.unop) x.1)
    (Presheaf.imageSieve_mem X.J _ _) fun Y f hf ↦ ?_
  obtain ⟨k, hk⟩ := hf
  let K : kernelIdeal (tripleDatum₁₃ Q₁ Q₂ Q₃).restrictedPresentation.hom (op Y) :=
    ⟨k, Stacks.Sites.Conormal.IdealRestriction.lift_mem_kernelIdeal x f k hk⟩
  refine ⟨K, hk, ?_⟩
  rw [map_add]
  refine (congrArg₂ (· + ·)
    (Stacks.Sites.Conormal.IdealRestriction.map_descendApp (tripleDatum₁₂ Q₁ Q₂ Q₃).difference
      (fun _ k hk ↦ (tripleDatum₁₂ Q₁ Q₂ Q₃).difference_eq_zero_of_baseChange k hk) x f K hk)
    (Stacks.Sites.Conormal.IdealRestriction.map_descendApp (tripleDatum₂₃ Q₁ Q₂ Q₃).difference
      (fun _ k hk ↦ (tripleDatum₂₃ Q₁ Q₂ Q₃).difference_eq_zero_of_baseChange k hk) x f K
        hk)).trans ?_
  exact tripleDatum_difference_add Q₁ Q₂ Q₃ K

/-- The difference maps `ℐ/ℐ² ⟶ G` of the three pairs: `D̄₁₂ + D̄₂₃ = D̄₁₃`. -/
theorem tripleDatum_conormalMap_add :
    Eq (α := tripleConormal Q₁ Q₂ Q₃ ⟶ targetG S)
      (HAdd.hAdd (α := tripleConormal Q₁ Q₂ Q₃ ⟶ targetG S)
        (β := tripleConormal Q₁ Q₂ Q₃ ⟶ targetG S) (γ := tripleConormal Q₁ Q₂ Q₃ ⟶ targetG S)
        (tripleDatum₁₂ Q₁ Q₂ Q₃).conormalMap (tripleDatum₂₃ Q₁ Q₂ Q₃).conormalMap)
      (tripleDatum₁₃ Q₁ Q₂ Q₃).conormalMap := by
  refine Stacks.Sites.Conormal.conormal_hom_ext (tripleDatum₁₃ Q₁ Q₂ Q₃).presentation
    (targetG S) (fun U x ↦ ?_)
  change ((tripleDatum₁₂ Q₁ Q₂ Q₃).conormalMap.val.app U) _ +
      ((tripleDatum₂₃ Q₁ Q₂ Q₃).conormalMap.val.app U) _ = _
  refine (congrArg₂ (fun a b : (targetG S).val.obj U ↦ a + b)
    (Stacks.Sites.Conormal.conormalDesc_toAssociatedModule _ _ _ U x)
    (Stacks.Sites.Conormal.conormalDesc_toAssociatedModule _ _ _ U x)).trans ?_
  exact (tripleDatum_descendedDifference_add Q₁ Q₂ Q₃ x).trans
    (Stacks.Sites.Conormal.conormalDesc_toAssociatedModule _ _ _ U x).symm

/-! ### The cocycle identity -/

variable [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)]

/-- `Ext¹_𝒪(NL(α), G)` for the presentation `α` of the fibre product of the three solutions. -/
noncomputable abbrev tripleExt : Type _ :=
  DerivedCategory.Ext (DerivedCategory.Q.obj
      (Stacks.SheafOfModules.presentationNaiveCotangentComplex.{v, u, max u v w, w} X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
        (tripleGenerators Q₁ Q₂ Q₃) (tripleMap Q₁ Q₂ Q₃)))
    ((DerivedCategory.singleFunctor _ 0).obj (targetG S)) 1

/-- `Ext¹_𝒪(NL_{𝒪/f⁻¹𝒪_B}, G)`, where the obstruction classes live. -/
noncomputable abbrev obstructionExt : Type _ :=
  DerivedCategory.Ext (DerivedCategory.Q.obj
      (Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, w} X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage))
    ((DerivedCategory.singleFunctor _ 0).obj (targetG S)) 1

/-- The classes in `Ext¹_𝒪(NL(α), G)` of the three difference maps add up. -/
theorem tripleDatum_extClass_add :
    Eq (α := tripleExt Q₁ Q₂ Q₃)
      (HAdd.hAdd (α := tripleExt Q₁ Q₂ Q₃) (β := tripleExt Q₁ Q₂ Q₃) (γ := tripleExt Q₁ Q₂ Q₃)
        (tripleDatum₁₂ Q₁ Q₂ Q₃).extClass (tripleDatum₂₃ Q₁ Q₂ Q₃).extClass)
      (tripleDatum₁₃ Q₁ Q₂ Q₃).extClass :=
  (Stacks.SheafOfModules.presentationConormalExtClass_add.{t, w, v, u} X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
    (tripleGenerators Q₁ Q₂ Q₃) (tripleMap Q₁ Q₂ Q₃) (targetG S)
    (tripleDatum₁₂ Q₁ Q₂ Q₃).conormalMap (tripleDatum₂₃ Q₁ Q₂ Q₃).conormalMap).symm.trans
    (congrArg (Stacks.SheafOfModules.presentationConormalExtClass.{v, u, w, t} X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
      (tripleGenerators Q₁ Q₂ Q₃) (tripleMap Q₁ Q₂ Q₃) (targetG S))
      (tripleDatum_conormalMap_add Q₁ Q₂ Q₃))

/-- The obstruction classes of the three pair data add up. -/
theorem tripleDatum_obstruction_add :
    Eq (α := obstructionExt (S := S))
      (HAdd.hAdd (α := obstructionExt (S := S)) (β := obstructionExt (S := S))
        (γ := obstructionExt (S := S))
        (tripleDatum₁₂ Q₁ Q₂ Q₃).obstruction (tripleDatum₂₃ Q₁ Q₂ Q₃).obstruction)
      (tripleDatum₁₃ Q₁ Q₂ Q₃).obstruction := by
  unfold PairDatum.obstruction
  rw [← Preadditive.comp_add, tripleDatum_extClass_add]

/-- **The obstruction class of two solutions is a cocycle**:
`o(𝒪'₁, 𝒪'₂) + o(𝒪'₂, 𝒪'₃) = o(𝒪'₁, 𝒪'₃)`. -/
theorem pairDatumObstruction_add :
    Eq (α := obstructionExt (S := S))
      (HAdd.hAdd (α := obstructionExt (S := S)) (β := obstructionExt (S := S))
        (γ := obstructionExt (S := S))
        (pairDatumObstruction Q₁ Q₂) (pairDatumObstruction Q₂ Q₃))
      (pairDatumObstruction Q₁ Q₃) := by
  rw [← (tripleDatum₁₂ Q₁ Q₂ Q₃).obstruction_eq_pairDatumObstruction,
    ← (tripleDatum₂₃ Q₁ Q₂ Q₃).obstruction_eq_pairDatumObstruction,
    ← (tripleDatum₁₃ Q₁ Q₂ Q₃).obstruction_eq_pairDatumObstruction]
  exact tripleDatum_obstruction_add Q₁ Q₂ Q₃

end CompatibleFirstOrderThickening

end Deformation.ToposThickening.RingedToposExtensionProblem

end
