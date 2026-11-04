module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.RestrictionMapHomologicalComplexKFlat
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# K-flat resolutions of complexes of diagrams of modules

Let `J` be a small category and `R` a commutative ring.  A diagram `J ⥤ R-Mod` is a presheaf of
`R̲`-modules on the chaotic site `Jᵒᵖ`, and the tensor product of two diagrams is computed
pointwise.  This file proves that **every complex of diagrams of `R`-modules receives a
quasi-isomorphism from a K-flat complex**, K-flatness being taken for the pointwise tensor
product.  This is Stacks 06YS for a chaotic site: the general statement for ringed sites is
proved in `StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution`, for sheaves of modules
and the sheafified tensor product, which is not the category of diagrams with its pointwise
tensor product on the nose.

The proof is that of Stacks 06Y4 for modules, run in the category of diagrams.  Diagrams have
enough projectives (`Stacks.CategoryHomology.diagramsEnoughProjectives`), so the canonical
truncations `τ_{≤ n}K` of a complex `K` are resolved compatibly by bounded above complexes of
projective diagrams (`CochainComplex.exists_sequence_quasiIso_truncLE`), and the colimit of that
ladder resolves `K`.  It is K-flat because K-flatness of a complex of diagrams is a pointwise
condition (`CochainComplex.KFlatBifunctor.kFlat_of_forall_evaluation`), evaluation commutes with
the colimit, each evaluation of a projective diagram is a projective module
(`Stacks.CategoryHomology.projective_obj_of_projective`), a bounded above complex of flat modules
is K-flat (Stacks 064K, `CochainComplex.KFlat.kFlat_of_flat`) and a filtered colimit of K-flat
complexes is K-flat (Stacks 06Y3, `CochainComplex.KFlat.kFlat_colimit`).

## Main results

* `Stacks.CategoryHomology.projective_obj_of_projective`: the values of a projective diagram of
  modules are projective modules.
* `Stacks.CategoryHomology.exists_kFlat_quasiIso_diagrams`: every complex of diagrams of
  `R`-modules receives a quasi-isomorphism from a K-flat one.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.CategoryHomology

variable {J : Type u} [SmallCategory J] {R : Type u} [CommRing R]

/-- A product of epimorphisms of modules is an epimorphism: surjectivity of the factors is
checked on the components of an element of the product. -/
lemma epi_pi_lift_comp {I : Type u} {X Y : ModuleCat.{u} R} (f : X ⟶ Y) [Epi f] :
    Epi (Pi.lift fun (g : I) ↦ Pi.π (fun _ ↦ X) g ≫ f) := by
  have hf : Function.Surjective f := (ModuleCat.epi_iff_surjective f).1 inferInstance
  have key : ∀ (Z : ModuleCat.{u} R) (z : (∏ᶜ fun _ : I => Z : ModuleCat.{u} R)) (g : I),
      (ModuleCat.piIsoPi (fun _ : I => Z)).hom z g = (Pi.π (fun _ : I => Z) g).hom z :=
    fun Z z g => congrArg (fun φ => φ.hom z) (ModuleCat.piIsoPi_hom_ker_subtype (fun _ => Z) g)
  have key' : ∀ (Z : ModuleCat.{u} R) (z : I → Z) (g : I),
      (Pi.π (fun _ : I => Z) g).hom ((ModuleCat.piIsoPi (fun _ : I => Z)).inv z) = z g :=
    fun Z z g => congrArg (fun φ => φ.hom z) (ModuleCat.piIsoPi_inv_kernel_ι (fun _ => Z) g)
  refine (ModuleCat.epi_iff_surjective _).2 fun y => ?_
  choose x hx using fun g => hf ((ModuleCat.piIsoPi (fun _ : I => Y)).hom y g)
  refine ⟨(ModuleCat.piIsoPi (fun _ : I => X)).inv x, ?_⟩
  apply (ModuleCat.piIsoPi (fun _ : I => Y)).toLinearEquiv.injective
  funext g
  change (ModuleCat.piIsoPi (fun _ : I => Y)).hom _ g =
    (ModuleCat.piIsoPi (fun _ : I => Y)).hom y g
  rw [key, ← hx g, ← key' X x g, ← ModuleCat.comp_apply, Pi.lift_π, ModuleCat.comp_apply]

/-- The right adjoint of evaluation at an object, `M ↦ (j ↦ ∏_{j ⟶ k} M)`, preserves
epimorphisms of modules, epimorphisms of diagrams being pointwise. -/
instance evaluationRightAdjoint_preservesEpimorphisms (k : J) :
    (evaluationRightAdjoint (ModuleCat.{u} R) k).PreservesEpimorphisms where
  preserves f _ := by
    rw [NatTrans.epi_iff_epi_app']
    exact fun _ => epi_pi_lift_comp f

/-- **The values of a projective diagram of modules are projective modules.**  Evaluation at an
object is left adjoint to `M ↦ (j ↦ ∏_{j ⟶ k} M)` (`CategoryTheory.evaluationAdjunctionLeft`),
whose right adjoint preserves epimorphisms, so evaluation preserves projective objects. -/
theorem projective_obj_of_projective (F : J ⥤ ModuleCat.{u} R) [Projective F] (k : J) :
    Projective (F.obj k) :=
  (evaluationAdjunctionLeft (ModuleCat.{u} R) k).map_projective F inferInstance

/-- **Stacks 06YS for a chaotic site: every complex of diagrams of modules receives a
quasi-isomorphism from a K-flat complex**, K-flatness being taken for the pointwise tensor
product of diagrams.

The compatible resolutions of the canonical truncations by bounded above complexes of projective
diagrams (`CochainComplex.exists_sequence_quasiIso_truncLE`) have a colimit which resolves the
complex (`StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE`).
Each evaluation of that colimit is the colimit of the evaluations, which are bounded above
complexes of projective, hence flat, modules; it is therefore K-flat by Stacks 064K and 06Y3, and
K-flatness of a complex of diagrams is checked pointwise. -/
theorem exists_kFlat_quasiIso_diagrams (G : CochainComplex (J ⥤ ModuleCat.{u} R) ℤ) :
    ∃ (P : CochainComplex (J ⥤ ModuleCat.{u} R) ℤ) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor (J ⥤ ModuleCat.{u} R)) P ∧
        QuasiIso f := by
  have : EnoughProjectives (J ⥤ ModuleCat.{u} R) :=
    diagramsEnoughProjectives J (ModuleCat.{u} R)
  let P : ObjectProperty (J ⥤ ModuleCat.{u} R) := fun X => Projective X
  have : P.ContainsZero := ⟨_, isZero_zero _, (isZero_zero (J ⥤ ModuleCat.{u} R)).projective⟩
  have hsum : ∀ X Y : J ⥤ ModuleCat.{u} R, P X → P Y → P (X ⊞ Y) :=
    fun X Y (_ : Projective X) (_ : Projective Y) => inferInstanceAs (Projective (X ⊞ Y))
  have hcover : ∀ X : J ⥤ ModuleCat.{u} R, ∃ (Y : J ⥤ ModuleCat.{u} R) (_ : P Y)
      (p : Y ⟶ X), Epi p :=
    fun X => ⟨Projective.over X, (inferInstance : Projective (Projective.over X)),
      Projective.π X, inferInstance⟩
  obtain ⟨Q, q, g, hq, -, hle, hproj, -, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P hsum hcover G
  let D := Functor.ofSequence g
  let c := colimit.cocone D
  have hc : IsColimit c := colimit.isColimit D
  let s : Cocone D := Cocone.mk G
    (NatTrans.ofSequence (fun n => q n ≫ G.ιTruncLE (n : ℤ)) (fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  let α : c.pt ⟶ G := hc.desc s
  refine ⟨c.pt, α, ?_,
    StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE
      q hq hc α fun n => hc.fac s n⟩
  refine CochainComplex.KFlatBifunctor.kFlat_of_forall_evaluation _ fun k => ?_
  let E : CochainComplex (J ⥤ ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
    ((evaluation J (ModuleCat.{u} R)).obj k).mapHomologicalComplex (ComplexShape.up ℤ)
  have hkQ : ∀ n, CochainComplex.KFlat (E.obj (Q n)) := by
    intro n
    have : (Q n).IsStrictlyLE (n : ℤ) := hle n
    have : CochainComplex.IsStrictlyLE (E.obj (Q n)) (n : ℤ) := by
      dsimp only [E]
      infer_instance
    have : ∀ i, Module.Flat R ((E.obj (Q n)).X i) := fun i => by
      have : Projective ((Q n).X i) := hproj n i
      have : Projective (((Q n).X i).obj k) := projective_obj_of_projective _ k
      have : Module.Projective R (((Q n).X i).obj k) :=
        ModuleCat.projective_of_module_projective _
      exact (Module.Flat.of_projective : Module.Flat R (((Q n).X i).obj k))
    exact CochainComplex.KFlat.kFlat_of_flat (E.obj (Q n)) n
  exact CochainComplex.KFlatBifunctor.KFlat.of_iso _
    (CochainComplex.KFlat.kFlat_colimit (D ⋙ E) hkQ) (preservesColimitIso E D).symm

end Stacks.CategoryHomology

end
