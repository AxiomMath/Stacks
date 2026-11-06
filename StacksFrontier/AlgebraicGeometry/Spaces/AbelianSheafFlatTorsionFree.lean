module

public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianSheafDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Homology.KFlat.BifunctorTruncationGE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A torsion-free abelian sheaf is flat

Let `(C, J)` be a site.  An abelian sheaf whose sections over every object of the site are a
torsion-free abelian group is flat for the tensor product of abelian sheaves: tensoring with it
is an exact endofunctor of `Sheaf J AddCommGrpCat`, and consequently the abelian sheaf placed in
a single degree is a K-flat cochain complex.

## Main results

* `AddCommGrpCat.mono_whiskerRight_of_isTorsionFree`: tensoring a monomorphism of abelian groups
  with a torsion-free abelian group gives a monomorphism.
* `Stacks.Cohomology.mono_whiskerRight_presheaf_of_isTorsionFree`: the same for presheaves of
  abelian groups, objectwise.
* `Stacks.Cohomology.mono_whiskerRight_abelianSheaf_of_isTorsionFree`: the same for abelian
  sheaves.
* `Stacks.Cohomology.preservesFiniteLimits_curriedTensor_flip_of_isTorsionFree`,
  `Stacks.Cohomology.exactFunctor_curriedTensor_flip_of_isTorsionFree`: a sectionwise
  torsion-free abelian sheaf is flat, that is, tensoring with it is exact.
* `Stacks.Cohomology.kFlat_single_of_isTorsionFree`: a sectionwise torsion-free abelian sheaf
  placed in a single degree is K-flat.
* `Stacks.Cohomology.kFlat_single_of_mono_of_isTorsionFree`: a subsheaf of a sectionwise
  torsion-free abelian sheaf, placed in a single degree, is K-flat.
* `Stacks.Cohomology.hF_curriedTensor_abelianSheaves`,
  `Stacks.Cohomology.hexact_abelianSheaves`: tensoring with a fixed abelian sheaf commutes with
  sequential colimits, and sequential colimits of acyclic complexes of abelian sheaves are
  acyclic.
* `Stacks.Cohomology.kFlat_truncGE_of_isTorsionFree_terms`: the canonical truncation of a K-flat
  complex of abelian sheaves with sectionwise torsion-free terms, whose cohomology vanishes in the
  degrees it truncates away, is K-flat.

## References

* [Stacks Project, Tag 06YI](https://stacks.math.columbia.edu/tag/06YI)
* [Stacks Project, Tag 0FME](https://stacks.math.columbia.edu/tag/0FME)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonoidalClosed.FunctorCategory

universe u v

namespace AddCommGrpCat

attribute [local instance] monoidalCategory uliftIntEquivalenceInverseMonoidal
  uliftIntEquivalenceFunctorMonoidal

/-- A universe-lifted copy of `ℤ` is a principal ideal ring. -/
local instance isPrincipalIdealRing_uliftInt : IsPrincipalIdealRing (ULiftInt.{v}) :=
  IsPrincipalIdealRing.of_surjective (ULift.ringEquiv : ULiftInt.{v} ≃+* ℤ).symm.toRingHom
    (ULift.ringEquiv : ULiftInt.{v} ≃+* ℤ).symm.surjective

/-- A module over a universe-lifted copy of `ℤ` which is torsion-free as an abelian group is
flat. -/
@[ega "0 6.3.4" "converse for A = ℤ", sga "1 IV 1.3" "(ii), special case"]
lemma flat_of_isTorsionFree_uliftInt (X : ModuleCat.{v} (ULiftInt.{v}))
    (hX : Module.IsTorsionFree ℤ X) : Module.Flat (ULiftInt.{v}) X := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  refine Module.IsTorsionFree.comap ULift.down (fun r hr => ?_) (fun r m => ?_)
  · rw [isRegular_iff_ne_zero] at hr ⊢
    simpa [ULift.ext_iff] using hr
  · exact (Int.cast_smul_eq_zsmul (ULiftInt.{v}) r.down m).symm

/-- **Tensoring a monomorphism of abelian groups with a torsion-free abelian group gives a
monomorphism.** -/
@[ega "0 6.3.4" "converse for A = ℤ", sga "1 IV 1.3" "(ii), special case"]
lemma mono_whiskerRight_of_isTorsionFree (A : AddCommGrpCat.{v})
    (hA : Module.IsTorsionFree ℤ A) {B B' : AddCommGrpCat.{v}} (f : B ⟶ B') (hf : Mono f) :
    Mono (f ▷ A) := by
  have : Module.IsTorsionFree ℤ (uliftIntEquivalence.{v}.inverse.obj A) :=
    have : Module.IsTorsionFree ℤ ((𝟭 AddCommGrpCat.{v}).obj A) := hA
    Function.Injective.moduleIsTorsionFree (uliftIntEquivalence.{v}.counitIso.app A).hom
      ((mono_iff_injective _).mp inferInstance) (map_zsmul _)
  have : Module.Flat (ULiftInt.{v}) (uliftIntEquivalence.{v}.inverse.obj A) :=
    flat_of_isTorsionFree_uliftInt _ this
  have : Mono (uliftIntEquivalence.{v}.inverse.map f ▷ uliftIntEquivalence.{v}.inverse.obj A) :=
    (MonoidalCategory.tensorRight (uliftIntEquivalence.{v}.inverse.obj A)).map_mono _
  change Mono (uliftIntEquivalence.{v}.functor.map
    (uliftIntEquivalence.{v}.inverse.map f ▷ uliftIntEquivalence.{v}.inverse.obj A))
  infer_instance

end AddCommGrpCat

namespace Stacks.Cohomology

attribute [local instance] AddCommGrpCat.monoidalCategory
  AddCommGrpCat.uliftIntEquivalenceInverseMonoidal
  AddCommGrpCat.uliftIntEquivalenceFunctorMonoidal
  AddCommGrpCat.symmetricCategoryTransported
  AddCommGrpCat.monoidalClosed MonoidalClosed.enrichedOrdinaryCategorySelf

section Presheaf

variable {C : Type u} [SmallCategory.{u} C]

/-- **Tensoring a monomorphism of presheaves of abelian groups with a sectionwise torsion-free
presheaf gives a monomorphism.** -/
lemma mono_whiskerRight_presheaf_of_isTorsionFree (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (hF : ∀ V, Module.IsTorsionFree ℤ (F.obj V))
    {G G' : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (g : G ⟶ G') (hg : Mono g) : Mono (g ▷ F) := by
  have : ∀ V, Mono ((g ▷ F).app V) := fun V =>
    AddCommGrpCat.mono_whiskerRight_of_isTorsionFree (F.obj V) (hF V) (g.app V) inferInstance
  exact NatTrans.mono_of_mono_app _

end Presheaf

section Site

variable {C : Type u} [SmallCategory.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

/-- **Tensoring a monomorphism of abelian sheaves with a sectionwise torsion-free abelian sheaf
gives a monomorphism.** -/
lemma mono_whiskerRight_abelianSheaf_of_isTorsionFree (M : Sheaf J AddCommGrpCat.{u})
    (hM : ∀ V, Module.IsTorsionFree ℤ (M.obj.obj V))
    {X Y : Sheaf J AddCommGrpCat.{u}} (i : X ⟶ Y) (hi : Mono i) : Mono (i ▷ M) := by
  have h₁ : Mono ((presheafToSheaf J AddCommGrpCat.{u}).map (i.hom ▷ M.obj)) := by
    have := mono_whiskerRight_presheaf_of_isTorsionFree M.obj hM i.hom inferInstance
    infer_instance
  have : Mono (((presheafToSheaf J AddCommGrpCat.{u}).map i.hom ▷
      (presheafToSheaf J AddCommGrpCat.{u}).obj M.obj) ≫
      Functor.LaxMonoidal.μ (presheafToSheaf J AddCommGrpCat.{u}) Y.obj M.obj) := by
    rw [Functor.LaxMonoidal.μ_natural_left]
    have hμ : IsIso (Functor.LaxMonoidal.μ (presheafToSheaf J AddCommGrpCat.{u}) X.obj M.obj) :=
      (Functor.Monoidal.μIso (presheafToSheaf J AddCommGrpCat.{u}) X.obj M.obj).isIso_hom
    exact @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ hμ) _ h₁
  have : Mono ((presheafToSheaf J AddCommGrpCat.{u}).map i.hom ▷
      (presheafToSheaf J AddCommGrpCat.{u}).obj M.obj) :=
    mono_of_mono _ (Functor.LaxMonoidal.μ (presheafToSheaf J AddCommGrpCat.{u}) Y.obj M.obj)
  have hex : ((presheafToSheaf J AddCommGrpCat.{u}).obj X.obj) ◁
        ((sheafificationAdjunction J AddCommGrpCat.{u}).counit.app M) ≫
        ((presheafToSheaf J AddCommGrpCat.{u}).map i.hom ▷ M) =
      ((presheafToSheaf J AddCommGrpCat.{u}).map i.hom ▷
        ((presheafToSheaf J AddCommGrpCat.{u}).obj M.obj)) ≫
        (((presheafToSheaf J AddCommGrpCat.{u}).obj Y.obj) ◁
          ((sheafificationAdjunction J AddCommGrpCat.{u}).counit.app M)) :=
    MonoidalCategory.whisker_exchange _ _
  have : Mono (((presheafToSheaf J AddCommGrpCat.{u}).obj X.obj) ◁
      ((sheafificationAdjunction J AddCommGrpCat.{u}).counit.app M) ≫
      ((presheafToSheaf J AddCommGrpCat.{u}).map i.hom ▷ M)) := by
    rw [hex]
    infer_instance
  have h₂ : Mono ((presheafToSheaf J AddCommGrpCat.{u}).map i.hom ▷ M) :=
    (mono_comp_iff_of_isIso _ _).mp this
  have hnat : (presheafToSheaf J AddCommGrpCat.{u}).map i.hom ≫
      (sheafificationAdjunction J AddCommGrpCat.{u}).counit.app Y =
      (sheafificationAdjunction J AddCommGrpCat.{u}).counit.app X ≫ i :=
    (sheafificationAdjunction J AddCommGrpCat.{u}).counit.naturality i
  have : Mono (((sheafificationAdjunction J AddCommGrpCat.{u}).counit.app X ▷ M) ≫ (i ▷ M)) := by
    rw [← MonoidalCategory.comp_whiskerRight, ← hnat, MonoidalCategory.comp_whiskerRight]
    have hc : IsIso ((sheafificationAdjunction J AddCommGrpCat.{u}).counit.app Y ▷ M) :=
      MonoidalCategory.whiskerRight_isIso _ _
    exact @mono_comp _ _ _ _ _ _ h₂ _ (@IsIso.mono_of_iso _ _ _ _ _ hc)
  exact (mono_comp_iff_of_isIso _ _).mp this

/-- **A sectionwise torsion-free abelian sheaf is flat: tensoring with it preserves finite
limits.** -/
lemma preservesFiniteLimits_curriedTensor_flip_of_isTorsionFree
    (M : Sheaf J AddCommGrpCat.{u})
    (hM : ∀ V, Module.IsTorsionFree ℤ (M.obj.obj V)) :
    PreservesFiniteLimits ((curriedTensor (Sheaf J AddCommGrpCat.{u})).flip.obj M) :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun S hS ↦
    ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      ((curriedTensor (Sheaf J AddCommGrpCat.{u})).flip.obj M)).1 inferInstance S hS).1,
    mono_whiskerRight_abelianSheaf_of_isTorsionFree J M hM S.f hS.mono_f⟩

/-- **A sectionwise torsion-free abelian sheaf is flat**, in the form "tensoring with it is an
exact endofunctor of the abelian sheaves". -/
lemma exactFunctor_curriedTensor_flip_of_isTorsionFree (M : Sheaf J AddCommGrpCat.{u})
    (hM : ∀ V, Module.IsTorsionFree ℤ (M.obj.obj V)) :
    exactFunctor (Sheaf J AddCommGrpCat.{u}) _
      ((curriedTensor (Sheaf J AddCommGrpCat.{u})).flip.obj M) :=
  (exactFunctor_iff _).2
    ⟨preservesFiniteLimits_curriedTensor_flip_of_isTorsionFree J M hM, inferInstance⟩

/-- **A sectionwise torsion-free abelian sheaf placed in a single degree is a K-flat cochain
complex.** -/
theorem kFlat_single_of_isTorsionFree (M : Sheaf J AddCommGrpCat.{u})
    (hM : ∀ V, Module.IsTorsionFree ℤ (M.obj.obj V)) (q : ℤ) :
    CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Sheaf J AddCommGrpCat.{u}))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M) := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).1 (exactFunctor_curriedTensor_flip_of_isTorsionFree J M hM)
  exact CochainComplex.KFlatBifunctor.kFlat_single_of_exact _ M q fun G hG ↦
    HomologicalComplex.Acyclic.map ((curriedTensor (Sheaf J AddCommGrpCat.{u})).flip.obj M) hG

/-- **A subsheaf of a sectionwise torsion-free abelian sheaf, placed in a single degree, is a
K-flat cochain complex.** -/
theorem kFlat_single_of_mono_of_isTorsionFree (N : Sheaf J AddCommGrpCat.{u})
    (hN : ∀ V, Module.IsTorsionFree ℤ (N.obj.obj V)) (q : ℤ)
    (M : Sheaf J AddCommGrpCat.{u}) (i : M ⟶ N) (hi : Mono i) :
    CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Sheaf J AddCommGrpCat.{u}))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M) :=
  kFlat_single_of_isTorsionFree J M
    (fun V => ModuleSheafCohomology.isTorsionFree_of_mono J i hN V) q

/-! ### The canonical truncation of a K-flat complex with torsion-free terms -/

omit [HasSheafify J AddCommGrpCat.{u}] in
/-- **Tensoring with a fixed abelian sheaf commutes with sequential colimits.** -/
lemma hF_curriedTensor_abelianSheaves :
    ∀ X : Sheaf J AddCommGrpCat.{u},
      PreservesColimitsOfShape ℕ ((curriedTensor (Sheaf J AddCommGrpCat.{u})).obj X) :=
  fun _ => ⟨fun {_} => inferInstance⟩

/-- **A sequential colimit of acyclic complexes of abelian sheaves is acyclic**, stated at an
arbitrary colimit cocone. -/
lemma hexact_abelianSheaves :
    ∀ (E : ℕ ⥤ CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (s : Cocone E), IsColimit s →
      (∀ i, (E.obj i).Acyclic) → s.pt.Acyclic := by
  have hAb : HasExactColimitsOfShape ℕ AddCommGrpCat.{u} :=
    have : AB5OfSize.{0, 0} AddCommGrpCat.{u} := AB5OfSize_shrink _
    AB5OfSize.ofShape ℕ
  have hSh : HasExactColimitsOfShape ℕ (Sheaf J AddCommGrpCat.{u}) :=
    (sheafificationAdjunction J AddCommGrpCat.{u}).hasExactColimitsOfShape ℕ
  intro E s hs hE n
  exact (CochainComplex.KFlat.acyclic_colimit E hE n).of_iso
    ((colimit.isColimit E).coconePointUniqueUpToIso hs)

/-- **The canonical truncation `τ^{≥m}P` of a K-flat complex of abelian sheaves whose cohomology
vanishes in degrees `≤ m` is K-flat**, as soon as the terms of `P` in the degrees `≤ m + 1` are
sectionwise torsion-free. -/
theorem kFlat_truncGE_of_isTorsionFree_terms (m : ℤ)
    (P : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (curriedTensor (Sheaf J AddCommGrpCat.{u})) P)
    (hGE : P.IsGE (m + 1))
    (hterms : ∀ q : ℤ, q ≤ m + 1 → ∀ V, Module.IsTorsionFree ℤ ((P.X q).obj.obj V)) :
    CochainComplex.KFlatBifunctor.KFlat
      (curriedTensor (Sheaf J AddCommGrpCat.{u})) (P.truncGE m) :=
  CochainComplex.KFlatBifunctor.kFlat_truncGE_of_isGE _ P m
    (hF_curriedTensor_abelianSheaves J) (hexact_abelianSheaves J) hP hGE
    (fun q hq => kFlat_single_of_isTorsionFree J (P.X q) (hterms q (by omega)) q)
    (fun N j hj => kFlat_single_of_mono_of_isTorsionFree J (P.X (m + 1))
      (hterms (m + 1) le_rfl) m N j hj)

end Site

end Stacks.Cohomology

end
