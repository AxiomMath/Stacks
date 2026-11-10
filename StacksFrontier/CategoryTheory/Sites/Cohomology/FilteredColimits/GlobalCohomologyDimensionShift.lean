module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SmallSiteAbelianInstances
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# The dimension-shift step for filtered colimits of global cohomology

Stacks 0GN3 asserts that, for a site carrying a set `S` of quasi-compact sheaves of sets with
enough covers, products and equalizers, the canonical map
`colim_λ H^p(C, F_λ) ⟶ H^p(C, colim_λ F_λ)` is an isomorphism for every filtered diagram of
abelian sheaves and every `p ≥ 0`. Its proof is an induction on `p`, and the induction *step* is
formal: it uses nothing about `S` beyond what the previous degree already gives. This file
isolates that step.

The step is the standard Grothendieck dévissage. Given a filtered diagram `F`, embed it in a
diagram `G` of *pointwise injective* objects, so that `0 → F → G → G/F → 0` is a short exact
sequence of diagrams. A δ-functor turns this into a long exact sequence, and in the commutative
ladder comparing the colimit of the long exact sequences with the long exact sequence of the
colimit, the two left-hand columns are isomorphisms by the previous degree while both rows are
exact and end in an epimorphism, because degree `n + 1` vanishes on the pointwise injective
middle term and — by hypothesis — on its colimit. The remaining column is therefore an
isomorphism too. Transporting this along the identification of the right derived functors of
global sections with `Ext` out of the constant sheaf `ℤ` gives the step for `H^{n+1}`.

So the content extracted here is: `(Vₙ)` plus "degree `n + 1` vanishes on filtered colimits of
pointwise injective diagrams" implies `(Vₙ₊₁)`. In the induction of Stacks 0GN3 the vanishing
hypothesis is what the set `S` is used to supply.

## Main results

* `Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_deltaFunctor_succ`: the dévissage
  for an arbitrary δ-functor between abelian categories with exact colimits of the given shape.
* `Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_ext_succ`: its specialisation to
  `Ext^•(X, -)` on a Grothendieck abelian category.
* `Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections_succ`:
  the induction step of Stacks 0GN3 itself, for the right derived functors of
  `CategoryTheory.Sheaf.Γ`.

## Implementation notes

`globalSectionsRightDerivedIsoFunctorH` is the identification of the right derived functors of
global sections with the sheaf cohomology functor `CategoryTheory.Sheaf.functorH`, obtained from
the corepresentability of global sections by the constant sheaf on `ℤ`
(`ModuleSheafCohomology.globalSectionsRepresentation`).

`functorHIsoExtFunctorObj` records that `CategoryTheory.Sheaf.functorH` and the corresponding
`Abelian.extFunctorObj` are the *same* functor: it is `Iso.refl`, the two spellings being
definitionally but not reducibly equal.

The site, the coefficients and the diagram all live in one universe `u`, which is what makes global
sections corepresentable by a sheaf in the same universe.

## References

* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.ColimitsOfCohomology

attribute [local instance] ColimitsOfCohomology.enoughInjectives_sheaf_ab
  ColimitsOfCohomology.additive_globalSections_ab





/-- A short complex of functors is exact as soon as each of its evaluations is. -/
public lemma shortComplex_exact_of_exact_evaluation
    {I A : Type*} [Category* I] [Category* A] [Abelian A]
    (S : ShortComplex (I ⥤ A))
    (h : ∀ i, (S.map ((evaluation I A).obj i)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology, Functor.isZero_iff]
  intro i
  exact (((S.map ((evaluation I A).obj i)).exact_iff_isZero_homology).1 (h i)).of_iso
    (S.mapHomologyIso ((evaluation I A).obj i)).symm

/-- A map of exact short complexes with epimorphic second maps which is an isomorphism on the
first two terms is an isomorphism on the third. -/
public lemma shortComplex_isIso_τ₃_of_exact
    {A : Type*} [Category* A] [Abelian A]
    {S T : ShortComplex A} (f : S ⟶ T) (hS : S.Exact) (hT : T.Exact)
    [Epi S.g] [Epi T.g] [IsIso f.τ₁] [IsIso f.τ₂] : IsIso f.τ₃ := by
  let e := CokernelCofork.mapIsoOfIsColimit hS.gIsCokernel hT.gIsCokernel
    (Arrow.isoMk (asIso f.τ₁) (asIso f.τ₂) f.comm₁₂)
  have h : e.hom = f.τ₃ := by
    apply (cancel_epi S.g).1
    calc
      S.g ≫ e.hom = f.τ₂ ≫ T.g :=
        CokernelCofork.π_mapOfIsColimit hS.gIsCokernel
          (CokernelCofork.ofπ T.g T.zero) (Arrow.homMk f.τ₁ f.τ₂ f.comm₁₂)
      _ = S.g ≫ f.τ₃ := f.comm₂₃
  rw [← h]
  infer_instance

/-- **Dimension shift for a δ-functor against colimits.** Let `S` be a short exact sequence of
diagrams of shape `I`, let `D` be a δ-functor, and suppose that `D` in degree `n` commutes with
the colimit on the middle and the right term of `S`. If `D` in degree `n + 1` vanishes on each
value of the middle term and on its colimit, then `D` in degree `n + 1` commutes with the
colimit on the left term of `S`. -/
public lemma isIso_colimit_post_deltaFunctor_succ
    {I A B : Type*} [Category* I] [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasColimitsOfShape I A] [HasColimitsOfShape I B]
    [HasExactColimitsOfShape I A] [HasExactColimitsOfShape I B]
    (D : DeltaFunctor A B) (S : ShortComplex (I ⥤ A)) (hS : S.ShortExact) (n : ℕ)
    (hi : ∀ i, IsZero ((D.functor (n + 1)).obj (S.X₂.obj i)))
    (hc : IsZero ((D.functor (n + 1)).obj (colimit S.X₂)))
    [IsIso (colimit.post S.X₂ (D.functor n))]
    [IsIso (colimit.post S.X₃ (D.functor n))] :
    IsIso (colimit.post S.X₁ (D.functor (n + 1))) := by
  let Se (i : I) := S.map ((evaluation I A).obj i)
  have hSe (i : I) : (Se i).ShortExact := hS.map_of_exact _
  let δ : S.X₃ ⋙ D.functor n ⟶ S.X₁ ⋙ D.functor (n + 1) :=
    { app i := D.δ (hSe i) n
      naturality i j f := D.δ_naturality (hSe i) (hSe j)
        { τ₁ := S.X₁.map f
          τ₂ := S.X₂.map f
          τ₃ := S.X₃.map f
          comm₁₂ := S.f.naturality f
          comm₂₃ := S.g.naturality f } n }
  let T : ShortComplex (I ⥤ B) :=
    ShortComplex.mk (Functor.whiskerRight S.g (D.functor n)) δ (by
      ext i
      exact D.map_g_δ (hSe i) n)
  have hT : T.Exact :=
    shortComplex_exact_of_exact_evaluation T (fun i => D.exact_δ₁ (hSe i) n)
  have hδi (i : I) : Epi (δ.app i) :=
    D.epi_δ_of_map_f_eq_zero (hSe i) n ((hi i).eq_of_tgt _ _)
  have hδ : Epi T.g := NatTrans.epi_of_epi_app δ
  let Sc := S.map (colim : (I ⥤ A) ⥤ A)
  have hSc : Sc.ShortExact := hS.map_of_exact _
  let Tc := D.scδ₁ hSc n
  have hTc : Tc.Exact := D.exact_δ₁ hSc n
  have hδc : Epi Tc.g := D.epi_δ_of_map_f_eq_zero hSc n (hc.eq_of_tgt _ _)
  let φ : T.map (colim : (I ⥤ B) ⥤ B) ⟶ Tc :=
    { τ₁ := colimit.post S.X₂ (D.functor n)
      τ₂ := colimit.post S.X₃ (D.functor n)
      τ₃ := colimit.post S.X₁ (D.functor (n + 1))
      comm₁₂ := by
        change colimit.post S.X₂ (D.functor n) ≫ (D.functor n).map (colim.map S.g) =
          colim.map (Functor.whiskerRight S.g (D.functor n)) ≫ colimit.post S.X₃ (D.functor n)
        apply colimit.hom_ext
        intro i
        simp only [colimit.ι_post_assoc, colimit.ι_map_assoc, Functor.whiskerRight_app,
          colimit.ι_post]
        rw [← Functor.map_comp, ← Functor.map_comp, colimit.ι_map]
      comm₂₃ := by
        change colimit.post S.X₃ (D.functor n) ≫ D.δ hSc n =
          colim.map δ ≫ colimit.post S.X₁ (D.functor (n + 1))
        apply colimit.hom_ext
        intro i
        simp only [colimit.ι_map_assoc, colimit.ι_post_assoc, colimit.ι_post]
        exact (D.δ_naturality (hSe i) hSc
          { τ₁ := colimit.ι S.X₁ i
            τ₂ := colimit.ι S.X₂ i
            τ₃ := colimit.ι S.X₃ i
            comm₁₂ := colimit.ι_map S.f i
            comm₂₃ := colimit.ι_map S.g i } n) }
  have : Epi (T.map (colim : (I ⥤ B) ⥤ B)).g :=
    inferInstanceAs (Epi (colim.map T.g))
  have : IsIso φ.τ₁ := inferInstanceAs (IsIso (colimit.post S.X₂ (D.functor n)))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (colimit.post S.X₃ (D.functor n)))
  exact shortComplex_isIso_τ₃_of_exact φ (hT.map _) hTc

open scoped ZeroObject in
/-- Every diagram in an abelian category with functorial mono-injective factorizations embeds
monomorphically in a diagram all of whose values are injective. -/
public lemma exists_mono_pointwise_injective
    {A I : Type*} [Category* A] [Abelian A] [Category* I]
    [MorphismProperty.HasFunctorialFactorization
      (MorphismProperty.monomorphisms A) (MorphismProperty.monomorphisms A).rlp]
    (F : I ⥤ A) :
    ∃ (G : I ⥤ A) (f : F ⟶ G), Mono f ∧ ∀ i, Injective (G.obj i) := by
  let data := MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms A) (MorphismProperty.monomorphisms A).rlp
  let factor := (data.functorCategory I).factorizationData (0 : F ⟶ (Functor.const I).obj (0 : A))
  have hf (i : I) : Mono (factor.i.app i) := factor.hi i
  refine ⟨factor.Z, factor.i, NatTrans.mono_of_mono_app _, fun i => ?_⟩
  rw [injective_iff_rlp_monomorphisms_zero]
  have heq : factor.p.app i = (0 : factor.Z.obj i ⟶ 0) := (isZero_zero A).eq_of_tgt _ _
  exact heq ▸ factor.hp i

/-- The right derived functors of global sections are the sheaf cohomology functors. -/
public noncomputable def globalSectionsRightDerivedIsoFunctorH
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (n : ℕ) :
    (Sheaf.Γ J Ab.{u}).rightDerived n ≅ Sheaf.functorH J n := by
  let Z := (constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let e : Sheaf.Γ J Ab.{u} ≅ preadditiveCoyoneda.obj (op Z) :=
    ModuleSheafCohomology.globalSectionsRepresentation J
  change (Sheaf.Γ J Ab.{u}).rightDerived n ≅ Abelian.extFunctorObj Z n
  cases n with
  | zero => exact (Sheaf.Γ J Ab.{u}).rightDerivedZeroIsoSelf ≪≫ e ≪≫
      (ModuleSheafCohomology.extZeroIsoCoyoneda Z).symm
  | succ n => exact ModuleSheafCohomology.rightDerivedIso e (n + 1) ≪≫
      ModuleSheafCohomology.rightDerivedCoyonedaSuccIso Z n

/-- Sheaf cohomology in degree `n` *is* `Ext^n` out of the constant sheaf on `ℤ`; the two sides are
definitionally equal. -/
public noncomputable def functorHIsoExtFunctorObj {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (n : ℕ) :
    Abelian.extFunctorObj.{u}
        ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) n ≅
      Sheaf.functorH J n :=
  Iso.refl _

/-- Commuting with a colimit transports along an isomorphism of functors. -/
public lemma isIso_colimit_post_of_iso
    {I A B : Type*} [Category* I] [Category* A] [Category* B]
    (F : I ⥤ A) [HasColimit F] [HasColimitsOfShape I B]
    {G H : A ⥤ B} (e : G ≅ H) [IsIso (colimit.post F G)] :
    IsIso (colimit.post F H) := by
  have := preservesColimit_of_isIso_post G F
  have := preservesColimit_of_natIso F e
  infer_instance

/-- **Dimension shift for `Ext` against filtered colimits.** On a Grothendieck abelian category,
if `Ext^n(X, -)` commutes with all filtered colimits of shape `I` and `Ext^{n+1}(X, -)` vanishes
on filtered colimits of pointwise injective diagrams, then `Ext^{n+1}(X, -)` commutes with all
filtered colimits of shape `I`. -/
public lemma isIso_colimit_post_ext_succ
    {A : Type*} [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    [HasExt.{u} A] {I : Type u} [SmallCategory I] [IsFiltered I]
    (X : A) (n : ℕ)
    (hprev : ∀ F : I ⥤ A, IsIso (colimit.post F (Abelian.extFunctorObj.{u} X n)))
    (hacyclic : ∀ F : I ⥤ A, (∀ i, Injective (F.obj i)) →
      IsZero ((Abelian.extFunctorObj.{u} X (n + 1)).obj (colimit F))) (F : I ⥤ A) :
    IsIso (colimit.post F (Abelian.extFunctorObj.{u} X (n + 1))) := by
  obtain ⟨G, f, hf, hG⟩ := exists_mono_pointwise_injective F
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel f) hf inferInstance
  let D := ModuleSheafCohomology.extDeltaFunctor (𝟭 A) X
  have hi (i : I) : IsZero ((D.functor (n + 1)).obj (G.obj i)) := by
    have := hG i
    have : Subsingleton (Abelian.Ext.{u} X (G.obj i) (n + 1)) :=
      Abelian.Ext.subsingleton_of_injective X (G.obj i) n
    change IsZero (AddCommGrpCat.of (Abelian.Ext.{u} X (G.obj i) (n + 1)))
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hpost (G : I ⥤ A) : IsIso (colimit.post G (D.functor n)) :=
    have := hprev G
    isIso_colimit_post_of_iso G (Functor.leftUnitor (Abelian.extFunctorObj.{u} X n)).symm
  have := hpost S.X₂
  have := hpost S.X₃
  have : IsIso (colimit.post F (𝟭 A ⋙ Abelian.extFunctorObj.{u} X (n + 1))) :=
    isIso_colimit_post_deltaFunctor_succ D S hS n hi (hacyclic G hG)
  exact isIso_colimit_post_of_iso F (Functor.leftUnitor (Abelian.extFunctorObj.{u} X (n + 1)))

/-- **The induction step of Stacks 0GN3.** Suppose degree-`n` cohomology of a site commutes with
all filtered colimits of abelian sheaves of shape `I`, and that degree-`n + 1` cohomology
vanishes on the colimit of every pointwise injective such diagram. Then degree-`n + 1`
cohomology commutes with all filtered colimits of shape `I`. -/
public lemma isIso_colimit_post_rightDerived_globalSections_succ
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {I : Type u} [SmallCategory I] [IsFiltered I] (n : ℕ)
    (hprev : ∀ F : I ⥤ Sheaf J Ab.{u},
      IsIso (colimit.post F ((Sheaf.Γ J Ab.{u}).rightDerived n)))
    (hacyclic : ∀ F : I ⥤ Sheaf J Ab.{u}, (∀ i, Injective (F.obj i)) →
      IsZero (((Sheaf.Γ J Ab.{u}).rightDerived (n + 1)).obj (colimit F)))
    (F : I ⥤ Sheaf J Ab.{u}) :
    IsIso (colimit.post F ((Sheaf.Γ J Ab.{u}).rightDerived (n + 1))) := by
  let X := (constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  have hp (G : I ⥤ Sheaf J Ab.{u}) : IsIso (colimit.post G (Abelian.extFunctorObj.{u} X n)) :=
    have := hprev G
    isIso_colimit_post_of_iso G (globalSectionsRightDerivedIsoFunctorH J n)
  have ha (G : I ⥤ Sheaf J Ab.{u}) (hG : ∀ i, Injective (G.obj i)) :
      IsZero ((Abelian.extFunctorObj.{u} X (n + 1)).obj (colimit G)) :=
    (hacyclic G hG).of_iso ((globalSectionsRightDerivedIsoFunctorH J (n + 1)).app (colimit G)).symm
  have h₁ : IsIso (colimit.post F (Abelian.extFunctorObj.{u} X (n + 1))) :=
    isIso_colimit_post_ext_succ (A := Sheaf J Ab.{u}) (I := I) X n hp ha F
  have h₂ : IsIso (colimit.post F (Sheaf.functorH J (n + 1))) :=
    isIso_colimit_post_of_iso F (functorHIsoExtFunctorObj J (n + 1))
  exact isIso_colimit_post_of_iso F (globalSectionsRightDerivedIsoFunctorH J (n + 1)).symm

end Stacks.Cohomology.ColimitsOfCohomology

end
