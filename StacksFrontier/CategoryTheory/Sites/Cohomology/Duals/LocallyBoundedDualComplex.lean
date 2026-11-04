module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoproductSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.TermsOfADualComplexOfModules

/-!
# A complex of modules with a left dual is locally bounded

Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules admitting a left dual
in the monoidal category of complexes of `𝒪`-modules. Then `ℱ^•` is **locally bounded**: every
object of the site has a covering on whose members all but finitely many terms of `ℱ^•`
vanish.

The source argues that the coevaluation `η = ∑ ηₙ` is locally a finite sum, so that only
finitely many `ηₙ` survive on a small enough object, and that a term whose `ηₙ` vanishes is
itself zero. Both halves are available: the first is
`Stacks.SheafOfModules.CoproductSheafification.exists_finset_eq_zero_of_ι`, applied to the
degree-zero part of the graded tensor product, whose components are
`CategoryTheory.GradedObject.Monoidal.πTensorObj`; the second is the triangle identity, applied
after restricting to the covering member — restriction to a slice site being monoidal for the
tensor product of [Stacks, Tag 01CA].

## Main results

* `Stacks.SheafOfModules.Strict.isLocallyBounded_of_exactPairing`: the local boundedness of a
  complex of `𝒪`-modules with a left dual.

The finite set of surviving degrees depends on the member of the covering, not on the section
alone, because the preimage of the section under the objectwise coproduct varies. That is
enough: on a fixed member the vanishing propagates to every object over it by naturality of the
components, and the triangle identity is then run in the slice over that member.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject Opposite
open Stacks.SheafOfModules.CoproductSheafification

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})

/-- A complex of `𝒪`-modules with a left dual is locally bounded: every object `V` of the site
has a covering sieve on whose members all but finitely many terms of the complex restrict to
zero, the finite set of surviving degrees depending on the member.

This is one of the three assertions of [Stacks, Tag 0FPA]; the other two are that the terms are
locally direct summands of finite free modules and that the left dual is the complex of Example
0FP9. -/
theorem isLocallyBounded_of_exactPairing (K L : CochainComplex (Mod R) ℤ)
    (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) (V : C) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
      ∃ S : Finset ℤ, ∀ n ∉ S, IsZero ((K.X n).over W) := by
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  let : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  let : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  let : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  let := p
  let : ExactPairing (CochainComplex.toGradedObject K) (CochainComplex.toGradedObject L) :=
    CochainComplex.exactPairingX K L
  set θ : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R) ⟶
      GradedObject.Monoidal.tensorObj
        (CochainComplex.toGradedObject K) (CochainComplex.toGradedObject L) 0 :=
    GradedObject.Monoidal.tensorUnit₀.inv ≫
      (η_ (CochainComplex.toGradedObject K) (CochainComplex.toGradedObject L)) 0 with hθdef
  -- a morphism out of the unit sheaf is determined by its value at `1`, via restriction maps
  have hone : ∀ {X : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
      (φ : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R) ⟶ X) {W' W : C}
      (f : W' ⟶ W),
      (φ.val.app (op W')).hom (1 : (Stacks.SheafOfModules.Tensor.ringSheaf R).obj.obj (op W')) =
        (X.val.map f.op).hom ((φ.val.app (op W)).hom
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf R).obj.obj (op W))) :=
    fun {_} φ {_ _} f =>
    (congrArg (φ.val.app _).hom (map_one ((Stacks.SheafOfModules.Tensor.ringSheaf R).obj.map
      f.op).hom)).symm.trans (PresheafOfModules.naturality_apply φ.val f.op _)
  obtain ⟨T, hT, hmem⟩ :=
    exists_finset_eq_zero_of_ι (Stacks.SheafOfModules.Tensor.ringSheaf R)
      ((((mapBifunctor (curriedTensor (Mod R)) ℤ ℤ).obj (CochainComplex.toGradedObject K)).obj
        (CochainComplex.toGradedObject L)).mapObjFun (fun x : ℤ × ℤ => x.1 + x.2) (0 : ℤ))
      (fun idx => GradedObject.Monoidal.πTensorObj (CochainComplex.toGradedObject K)
        (CochainComplex.toGradedObject L) idx.1.1 idx.1.2 0 idx.2)
      (fun idx => GradedObject.Monoidal.ιTensorObj_πTensorObj_self
        (CochainComplex.toGradedObject K) (CochainComplex.toGradedObject L)
        idx.1.1 idx.1.2 0 idx.2)
      (fun idx jdx hne => GradedObject.Monoidal.ιTensorObj_πTensorObj_ne
        (CochainComplex.toGradedObject K) (CochainComplex.toGradedObject L)
        idx.1.1 idx.1.2 jdx.1.1 jdx.1.2 0 jdx.2 idx.2
        (fun hcon => hne (Subtype.ext (show (jdx : ℤ × ℤ) = (idx : ℤ × ℤ) from
          Prod.ext_iff.2 ⟨hcon.1, hcon.2⟩))))
      ((θ.val.app (op V)).hom (1 : (Stacks.SheafOfModules.Tensor.ringSheaf R).obj.obj (op V)))
  refine ⟨T, hT, fun {W} g hg => ?_⟩
  obtain ⟨S', hS'⟩ := hmem g hg
  refine ⟨S'.image (fun idx => idx.1.1), fun n hn => ?_⟩
  have hfib : ((n, -n) : ℤ × ℤ) ∈ (fun x : ℤ × ℤ => x.1 + x.2) ⁻¹' {(0 : ℤ)} := by simp
  have hidx : (⟨(n, -n), hfib⟩ :
      ((fun x : ℤ × ℤ => x.1 + x.2) ⁻¹' {(0 : ℤ)} : Set (ℤ × ℤ))) ∉ S' :=
    fun hm => hn (Finset.mem_image.2 ⟨_, hm, rfl⟩)
  have h0 := hS' _ hidx
  have h1 : ((GradedObject.Monoidal.coevApply (CochainComplex.toGradedObject K)
        (CochainComplex.toGradedObject L) n).val.app (op W)).hom
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf R).obj.obj (op W)) = 0 := by
    have e1 : GradedObject.Monoidal.coevApply (CochainComplex.toGradedObject K)
        (CochainComplex.toGradedObject L) n =
        θ ≫ GradedObject.Monoidal.πTensorObj (CochainComplex.toGradedObject K)
          (CochainComplex.toGradedObject L) n (-n) 0 (add_neg_cancel n) := by
      rw [hθdef]
      exact (Category.assoc _ _ _).symm
    refine (congrArg (fun f : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R) ⟶
        (CochainComplex.toGradedObject K) n ⊗ (CochainComplex.toGradedObject L) (-n) =>
      (f.val.app (op W)).hom
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf R).obj.obj (op W))) e1).trans ?_
    exact (congrArg (fun y => ((GradedObject.Monoidal.πTensorObj
      (CochainComplex.toGradedObject K) (CochainComplex.toGradedObject L) n (-n) 0
        (add_neg_cancel n)).val.app (op W)).hom y) (hone θ g)).trans h0
  -- the vanishing propagates to every object over `W`, by naturality: one member of the
  -- covering with its one finite set suffices
  have hres : ∀ (W' : C) (f : W' ⟶ W),
      ((GradedObject.Monoidal.coevApply (CochainComplex.toGradedObject K)
        (CochainComplex.toGradedObject L) n).val.app (op W')).hom
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf R).obj.obj (op W')) = 0 := by
    intro W' f
    exact (hone _ f).trans ((congrArg _ h1).trans (map_zero _))
  -- the monoidal structures on the ambient and the slice category
  let instSrc : MonoidalCategory (SheafOfModules.{max u v}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf R.obj
        (isSheaf_ringSheaf R))) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let instTgt : MonoidalCategory (SheafOfModules.{max u v}
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf R.obj
        (isSheaf_ringSheaf R) W)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory (R.over W).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (R.over W)).property
  let instMon : @Functor.Monoidal _ _ instSrc _ _ instTgt
      (Stacks.SheafOfModules.SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W) :=
    Stacks.SheafOfModules.SliceRestriction.overFunctorStrictMonoidal R.obj
      (isSheaf_ringSheaf R) W
  let instPre : @MonoidalPreadditive _ _ _ instTgt := monoidalPreadditiveRingSheaf (R.over W)
  let instTgt' : MonoidalCategory (SheafOfModules.{max u v}
      ((Stacks.SheafOfModules.Tensor.ringSheaf R).over W)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory (R.over W).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (R.over W)).property
  let instPre' : @MonoidalPreadditive _ _ _ instTgt' :=
    monoidalPreadditiveRingSheaf (R.over W)
  let instPair : @ExactPairing _ _ instSrc (K.X n) (L.X (-n)) :=
    CochainComplex.exactPairingXApply K L n
  let instMapped := @ExactPairing.map _ _ _ _ instSrc instTgt
    (Stacks.SheafOfModules.SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W)
    instMon (K.X n) (L.X (-n)) instPair
  have h2 : (Stacks.SheafOfModules.SliceRestriction.overFunctor R.obj
      (isSheaf_ringSheaf R) W).map
      (@ExactPairing.coevaluation _ _ instSrc (K.X n) (L.X (-n)) instPair) = 0 := by
    ext X
    refine Eq.trans ?_ rfl
    refine Eq.trans ?_ (hres X.unop.left X.unop.hom)
    exact congrArg (fun f : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf R) ⟶ _ =>
      (f.val.app (op X.unop.left)).hom
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf R).obj.obj (op X.unop.left)))
      (CochainComplex.exactPairingXApply_coevaluation K L n)
  have h3 : @ExactPairing.coevaluation _ _ instTgt
      ((Stacks.SheafOfModules.SliceRestriction.overFunctor R.obj
        (isSheaf_ringSheaf R) W).obj (K.X n))
      ((Stacks.SheafOfModules.SliceRestriction.overFunctor R.obj
        (isSheaf_ringSheaf R) W).obj (L.X (-n))) instMapped = 0 := by
    refine (ExactPairing.map_coevaluation (Stacks.SheafOfModules.SliceRestriction.overFunctor
      R.obj (isSheaf_ringSheaf R) W) (K.X n) (L.X (-n))).trans ?_
    rw [h2]
    simp
  exact @GradedObject.Monoidal.isZero_of_coevaluation_eq_zero _ _ instTgt _ instPre _ _
    instMapped h3

end Stacks.SheafOfModules.Strict

end

end
