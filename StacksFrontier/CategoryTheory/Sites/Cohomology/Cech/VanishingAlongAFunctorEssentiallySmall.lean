module

public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveModuleVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectivePresheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing along a functor of sites, with the morphism universe free

Let `u : C ⥤ D` be a continuous functor of sites and let `g : Sh(C) → Sh(D)` be the
corresponding morphism of topoi, so that `g⁻¹` is restriction along `u` — this is Sites, Lemma
00XR. Stacks 0D6X asserts that for an injective module `I` on `D` the pullback `g⁻¹I` has no
higher cohomology on any object of `C`.

This file proves that statement at a universe convention which does not identify the morphism
universe of `C` with the coefficient universe: the coefficients lie in a universe containing
the *object* universes of `C` and `D` as well as their morphism universes and the
covering-index universe, and no smallness hypothesis is imposed. The sites that occur in the
theory of algebraic stacks — the lisse-étale and flat-fppf sites of Stacks 0787 and their
slices — are of that shape: their objects live one universe above their morphisms, they are not
small, and their coefficients live in the universe of their objects.

Cohomology over an object is `Ext` out of the free abelian sheaf on the representable presheaf
of that object, lifted to the coefficient universe. At the universe convention of
`Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor` that sheaf is Mathlib's
`CategoryTheory.Sheaf.H'`; here the lift is necessary, because `Sheaf.H'` is only defined when
the coefficients lie in the morphism universe of the site.

## Main results

* `Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero`: **Stacks 03F9** with the
  morphism universe of the site free and `Small` dropped — vanishing of higher cohomology over
  the objects of a cofinal system of coverings, from vanishing of the higher Čech cohomology on
  that system.
* `Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero_of_functor`: the transfer of that
  criterion along `u`, as in Stacks 0D6X.
* `Stacks.CechSite.injective_sheaf_subsingleton_ext_of_functor`: the case of an injective
  abelian sheaf.
* `Stacks.CechSite.injective_module_subsingleton_ext_of_functor`: **Stacks 0D6X**, for an
  injective module over an arbitrary sheaf of rings on `D`.
* `Stacks.CechSite.freeSheafIsoConstantSheaf`: the free abelian sheaf on a terminal object of a
  site is the constant sheaf `ℤ`, so that cohomology over a terminal object is the global
  cohomology `CategoryTheory.Sheaf.H` of the site.
* `Stacks.CechSite.injective_sheaf_subsingleton_sheafH_of_functor`: **Stacks 0D6X** at a
  terminal object, stated for global cohomology.

## Implementation notes

The proof is the proof of the source, and the two files it is assembled from are the ones used
by `Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor`. What changes is the
input supplying the vanishing of the higher Čech cohomology of an injective abelian *presheaf*,
and the input supplying enough injective abelian sheaves.

* The library's Stacks 03F9 reproves Čech vanishing for an injective presheaf with the coefficient
  universe equal to the morphism universe, which costs a universe-lifting comparison of Čech
  complexes; with the coefficients containing the object universe the statement of Stacks 03OR,
  `Stacks.CechSite.injective_presheaf_cechCohomology_isZero`, applies directly.
* Enough injective abelian sheaves comes from
  `Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp`, which holds for an
  arbitrary site in any universe containing it, in place of a small model of the site.

The remaining ingredients — Stacks 03F8 on surjectivity of sections, Stacks 03AW and 03FC on
the Čech cohomology of an injective sheaf and of an injective module, and the comparison of
Čech complexes along `u` — are already stated with independent universes and are used
unchanged.

The identification of cohomology over a terminal object with global cohomology is the
identification of the two objects corepresenting sections over that object: the free abelian
sheaf on its representable presheaf, and the constant sheaf `ℤ`. It rests on
`Stacks.CechSite.freePUnitIsoInt`, the free abelian group on a one-point type being `ℤ`, which
is proved from the corepresentability of the forgetful functor by either of them.

## References

* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
* [Stacks Project, Tag 03OR](https://stacks.math.columbia.edu/tag/03OR)
* [Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
* [Stacks Project, Tag 03FC](https://stacks.math.columbia.edu/tag/03FC)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public section

universe x a t w v u u₂ v₂ r

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

private lemma cechComplexFunctor_preservesFiniteLimitsAux
    {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
    {A : Type u₂} [Category.{v₂} A] [HasProducts.{w} A] [Preadditive A] [HasFiniteLimits A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    PreservesFiniteLimits (cechComplexFunctor (A := A) E) := by
  have : PreservesFiniteLimits (FormalCoproduct.evalOp.{w} (Over X) A) :=
    preservesFiniteLimits_of_evaluation _ fun T ↦
      preservesFiniteLimits_of_natIso (evalOpCompEvaluationIso T.unop).symm
  have : PreservesFiniteLimits (AlgebraicTopology.alternatingCofaceMapComplex A) :=
    ⟨fun J _ _ ↦ by
      apply HomologicalComplex.preservesLimitsOfShape_of_eval
      intro n
      show PreservesLimitsOfShape J ((evaluation SimplexCategory A).obj (SimplexCategory.mk n))
      infer_instance⟩
  unfold cechComplexFunctor FormalCoproduct.cochainComplexFunctor
    FormalCoproduct.cosimplicialObjectFunctor
  infer_instance

private lemma epi_piMapAux {ι : Type w} (A B : ι → AddCommGrpCat.{max a w})
    [HasProducts.{w} AddCommGrpCat.{max a w}]
    (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, Function.Surjective (ConcreteCategory.hom (f i))) :
    Epi (Limits.Pi.map f) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  classical
  choose x hx using fun i => hf i ((Concrete.productEquiv B) y i)
  refine ⟨(Concrete.productEquiv A).symm x, ?_⟩
  apply (Concrete.productEquiv B).injective
  ext i
  calc
    (Concrete.productEquiv B) (Limits.Pi.map f ((Concrete.productEquiv A).symm x)) i =
        (Limits.Pi.π B i).hom (Limits.Pi.map f ((Concrete.productEquiv A).symm x)) := by simp
    _ = (f i).hom ((Limits.Pi.π A i).hom ((Concrete.productEquiv A).symm x)) :=
      congrArg (fun g => g.hom ((Concrete.productEquiv A).symm x)) (Limits.Pi.map_π f i)
    _ = (f i).hom (x i) := by simp
    _ = (Concrete.productEquiv B) y i := hx i

section Cofinal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max a u v w}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max a u v w})]
  (B : Set C)
  (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
  (hProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))))

/-- **Stacks Project, Tag 03F9, with the morphism universe of the site free.** If a cofinal
collection of coverings of a collection of objects has all its nonempty finite fibre products in
that collection, then vanishing of positive-degree Čech cohomology on those coverings implies
vanishing of positive-degree cohomology over every object in the collection.

Cohomology over `U` is `Ext` out of the sheafification of the free abelian presheaf on the
representable presheaf of `U`, lifted to the coefficient universe. The coefficient universe
contains the object universe of the site, which is what makes Stacks 03OR available for an
injective abelian presheaf and what replaces the hypothesis that the site be small. -/
@[stacks 03F9 "the coefficient universe contains the objects of the site, which replaces the \
hypothesis that the site be small with morphisms in the coefficient universe"]
theorem subsingleton_ext_of_cechCohomology_isZero
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (F : Sheaf J AddCommGrpCat.{max a u v w})
    (hCech : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ), 0 < p →
        letI : ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (i a))) := hProducts E hE
        IsZero (cechCohomology E.1 F.obj p))
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Ext ((presheafToSheaf J AddCommGrpCat.{max a u v w}).obj
      (uliftYoneda.{max a u v w}.obj U ⋙ AddCommGrpCat.free)) F p) := by
  let : EnoughInjectives (Sheaf J AddCommGrpCat.{max a u v w}) :=
    Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u, v, max a w}
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max a u v w} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, v, max a w}
  let Vanishes := fun (G : Sheaf J AddCommGrpCat.{max a u v w}) =>
    ∀ {V : C} (E : { E : PreZeroHypercover.{w} V // E.sieve₀ ∈ J V }) (hE : E ∈ Cov V)
      (n : ℕ), 0 < n →
        let := hProducts E hE
        IsZero (cechCohomology E.1 G.obj n)
  have main : ∀ (n : ℕ), 0 < n → ∀ (G : Sheaf J AddCommGrpCat.{max a u v w}), Vanishes G →
      ∀ V ∈ B, Subsingleton (Ext ((presheafToSheaf J AddCommGrpCat.{max a u v w}).obj
        (uliftYoneda.{max a u v w}.obj V ⋙ AddCommGrpCat.free)) G n) := by
    intro n hn
    induction n using Nat.case_strong_induction_on with
    | hz => simp at hn
    | hi n ih =>
      intro G hG V hV
      let ⟨ip⟩ := EnoughInjectives.presentation G
      let I := ip.J
      let f : G ⟶ I := ip.f
      let Qcoker := cokernel f
      let S : ShortComplex (Sheaf J AddCommGrpCat.{max a u v w}) :=
        ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
      have hsurj (T : C) (hT : T ∈ B) : Function.Surjective
          (((sheafToPresheaf J (AddCommGrpCat.{max a u v w})).map S.g).app (Opposite.op T)) := by
        let Cov' : Set (PreZeroHypercover.{w} T) :=
          { E | ∃ h : E.sieve₀ ∈ J T,
            (⟨E, h⟩ : { E : PreZeroHypercover.{w} T // E.sieve₀ ∈ J T }) ∈ Cov T }
        refine surjective_on_sections_of_isZero_cechCohomology.{w, v, u, max a u v}
          (J := J) (S := S) hS (U := T) (Cov := Cov') ?_ ?_ ?_ ?_
        · intro E hE
          exact hE.choose
        · intro R hR
          obtain ⟨E, hE, hER⟩ := hCovCofinal T hT R hR
          exact ⟨E.1, ⟨E.2, hE⟩, hER⟩
        · intro E hE q i
          obtain ⟨hcov, hECov⟩ := hE
          exact hProducts ⟨E, hcov⟩ hECov q i
        · intro E hE
          obtain ⟨hcov, hECov⟩ := hE
          exact hG ⟨E, hcov⟩ hECov 1 one_pos
      have hQ : Vanishes Qcoker := by
        intro T E hE k hk
        let := hProducts E hE
        let Fcech := sheafToPresheaf J (AddCommGrpCat.{max a u v w}) ⋙ cechComplexFunctor E.1
        let : PreservesFiniteLimits (cechComplexFunctor E.1) :=
          cechComplexFunctor_preservesFiniteLimitsAux
            (A := AddCommGrpCat.{max a u v w}) E.1
        let : PreservesFiniteLimits Fcech := by dsimp [Fcech]; infer_instance
        let SC := S.map Fcech
        let : Mono S.f := hS.mono_f
        let : Mono SC.f := Functor.map_mono Fcech S.f
        have hSC : SC.ShortExact :=
          HomologicalComplex.shortExact_of_degreewise_shortExact SC fun m => by
          have hm := hCovObjects E hE
          let : Epi ((SC.map (HomologicalComplex.eval _ _ m)).g) := by
            let W := fun i : Fin (m + 1) → E.1.I₀ =>
              (∏ᶜ fun a ↦ Over.mk (E.1.f (i a))).left
            show Epi (Limits.Pi.map fun i : Fin (m + 1) → E.1.I₀ =>
              ((sheafToPresheaf J (AddCommGrpCat.{max a u v w})).map S.g).app (op (W i)))
            exact epi_piMapAux _ _ _ fun i ↦ hsurj (W i) (hm.2.2 m i)
          let Eval := Fcech ⋙ HomologicalComplex.eval _ _ m
          let : PreservesFiniteLimits Eval := by dsimp [Eval]; infer_instance
          let : Mono ((S.map Eval).f) := Functor.map_mono Eval S.f
          let : Mono ((SC.map (HomologicalComplex.eval _ _ m)).f) :=
            Functor.map_mono (HomologicalComplex.eval _ _ m) SC.f
          exact ShortComplex.ShortExact.mk
            (hS.exact.map_of_mono_of_preservesKernel Eval hS.mono_f inferInstance)
        have hI : IsZero (SC.X₂.homology k) := by
          have : Injective I.obj := I.injective_obj
          exact injective_presheaf_cechCohomology_isZero.{w, v, u, a} E.1 I.obj k hk
        have hF : IsZero (SC.X₁.homology (k + 1)) :=
          hG E hE (k + 1) (Nat.zero_lt_succ k)
        exact (hSC.homology_exact₃ k (k + 1) (by simp)).isZero_X₂
          (hI.eq_of_src _ _) (hF.eq_of_tgt _ _)
      by_cases hn0 : n = 0
      · subst n
        have hs := hsurj V hV
        refine subsingleton_of_forall_eq 0 (fun z => ?_)
        let sectionEquiv : ∀ A' : Sheaf J AddCommGrpCat.{max a u v w},
            ((presheafToSheaf J AddCommGrpCat.{max a u v w}).obj
              (uliftYoneda.{max a u v w}.obj V ⋙ AddCommGrpCat.free) ⟶ A') ≃
              (((sheafToPresheaf J AddCommGrpCat.{max a u v w}).obj A').obj (op V)) :=
          fun A' =>
            ((sheafificationAdjunction J AddCommGrpCat.{max a u v w}).homEquiv _ A').trans
              (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv
                (uliftYoneda.{max a u v w}.obj V) A'.obj).trans uliftYonedaEquiv)
        let eQ := sectionEquiv S.X₃
        let eI := sectionEquiv S.X₂
        obtain ⟨q, rfl⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₁
          ((presheafToSheaf J AddCommGrpCat.{max a u v w}).obj
            (uliftYoneda.{max a u v w}.obj V ⋙ AddCommGrpCat.free)) hS z
          (Ext.eq_zero_of_injective _) rfl
        obtain ⟨i, hi⟩ := hs (eQ (Ext.addEquiv₀ q))
        have hcompat : eQ (eI.symm i ≫ S.g) = eQ (Ext.addEquiv₀ q) := by
          calc
            eQ (eI.symm i ≫ S.g) =
                ((sheafToPresheaf J AddCommGrpCat.{max a u v w}).map S.g).app (op V)
                  (eI (eI.symm i)) := by
              dsimp only [eQ, eI, sectionEquiv]
              simp only [Equiv.trans_apply, Equiv.symm_trans_apply]
              rw [(sheafificationAdjunction J
                AddCommGrpCat.{max a u v w}).homEquiv_naturality_right]
              rw [(AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_right]
              rw [uliftYonedaEquiv_comp]
              rfl
            _ = eQ (Ext.addEquiv₀ q) := by
              rw [Equiv.apply_symm_apply]
              exact hi
        have hlift : eI.symm i ≫ S.g = Ext.addEquiv₀ q := eQ.injective hcompat
        have hq : q = Ext.mk₀ (eI.symm i ≫ S.g) := by
          have := congrArg (Ext.mk₀ (X := (presheafToSheaf J AddCommGrpCat.{max a u v w}).obj
            (uliftYoneda.{max a u v w}.obj V ⋙ AddCommGrpCat.free)) (Y := S.X₃)) hlift.symm
          simpa using this
        rw [hq, ← Ext.mk₀_comp_mk₀_assoc]
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hQ' := ih n (le_refl n) hnpos Qcoker hQ V hV
        refine subsingleton_of_forall_eq 0 (fun z => ?_)
        let : Injective I := ip.injective
        have hker : z.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 :=
          Ext.eq_zero_of_injective _
        obtain ⟨q, hq⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₁
          ((presheafToSheaf J AddCommGrpCat.{max a u v w}).obj
            (uliftYoneda.{max a u v w}.obj V ⋙ AddCommGrpCat.free)) hS z hker rfl
        have hq0 : q = 0 := hQ'.elim _ _
        rw [hq0] at hq
        simpa only [Ext.zero_comp] using hq.symm
  exact main p hp F hCech U hU

end Cofinal

section Functor

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max a u v u₂ v₂ w}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max a u v u₂ v₂ w})]
  (u : C ⥤ D) [u.IsContinuous J K]
  (B : Set C)
  (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
  (hProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
  (hImageProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → (E.1.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.1.map u).f (i a))))

/-- **Stacks 03F9 transported along a functor of sites, with the morphism universes free.** If
the higher Čech cohomology of a sheaf `F` on `D` vanishes on the image of every covering in a
cofinal system of coverings of `C`, and `u` preserves the iterated fibre products of those
coverings, then the higher cohomology of the restriction of `F` along `u` vanishes over every
object of the system. -/
theorem subsingleton_ext_of_cechCohomology_isZero_of_functor
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsIso (cechProductMapOfFunctor u E.1 p i))
    (F : Sheaf K AddCommGrpCat.{max a u v u₂ v₂ w})
    (hCech : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ), 0 < p →
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsZero (cechCohomology (E.1.map u) F.obj p))
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Ext ((presheafToSheaf J AddCommGrpCat.{max a u v u₂ v₂ w}).obj
      (uliftYoneda.{max a u v u₂ v₂ w}.obj U ⋙ AddCommGrpCat.free))
      ((u.sheafPushforwardContinuous AddCommGrpCat.{max a u v u₂ v₂ w} J K).obj F) p) := by
  refine subsingleton_ext_of_cechCohomology_isZero.{x, max a u₂ v₂} J B Cov hProducts
    hCovObjects hCovCofinal
    ((u.sheafPushforwardContinuous AddCommGrpCat.{max a u v u₂ v₂ w} J K).obj F) ?_ U hU p hp
  intro V E hE q hq
  let := hProducts E hE
  let := hImageProducts E hE
  exact cechCohomology_isZero_of_isZero_of_functor u E.1 F.obj
    (fun n i ↦ hComparison E hE n i) q (hCech E hE q hq)

/-- **Stacks Project, Tag 0D6X for an injective abelian sheaf, with the morphism universes
free.** Let `u : C ⥤ D` be a continuous functor of sites and let `g : Sh(C) → Sh(D)` be the
corresponding morphism of topoi, so that `g⁻¹` is restriction along `u` by Sites, Lemma 00XR. If
`I` is an injective abelian sheaf on `D` then `H^p(U, g⁻¹I) = 0` for all `p > 0` and every
object `U` of the cofinal system of coverings, in particular for every object of `C` when the
system is cofinal everywhere.

This is the case `O_D = ℤ` of Stacks 0D6X, proved for an arbitrary structure sheaf in
`Stacks.CechSite.injective_module_subsingleton_ext_of_functor`; it is stated separately because
an injective object of `Ab(D)` is not, in the formalization, an injective module over the
constant sheaf of rings `ℤ`. -/
theorem injective_sheaf_subsingleton_ext_of_functor
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsIso (cechProductMapOfFunctor u E.1 p i))
    (I : Sheaf K AddCommGrpCat.{max a u v u₂ v₂ w}) [Injective I]
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Ext ((presheafToSheaf J AddCommGrpCat.{max a u v u₂ v₂ w}).obj
      (uliftYoneda.{max a u v u₂ v₂ w}.obj U ⋙ AddCommGrpCat.free))
      ((u.sheafPushforwardContinuous AddCommGrpCat.{max a u v u₂ v₂ w} J K).obj I) p) :=
  subsingleton_ext_of_cechCohomology_isZero_of_functor.{x, a} J K u B Cov hProducts
    hImageProducts hCovObjects hCovCofinal hComparison I
    (fun E hE q hq ↦
      let := hImageProducts E hE
      injective_sheaf_cechCohomology_isZero.{max a u v, w, v₂, u₂} (E.1.map u) I q hq)
    U hU p hp

end Functor

section Modules

variable {C : Type u} [Category.{v} C] (Y : AlgebraicGeometry.RingedSite.{u₂, v₂, r})
  (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max a u v u₂ v₂ r w}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max a u v u₂ v₂ r w})]
  (u : C ⥤ Y.C) [u.IsContinuous J Y.J]
  (B : Set C)
  (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
  (hProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
  (hImageProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → (E.1.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.1.map u).f (i a))))

/-- **Stacks Project, Tag 0D6X, with the morphism universes free.** Let `u : C ⥤ D` be a
continuous functor of sites and let `g : Sh(C) → Sh(D)` be the corresponding morphism of topoi,
so that `g⁻¹` is restriction along `u` by Sites, Lemma 00XR. Let `O_D` be a sheaf of rings on
`D` and let `I` be an injective `O_D`-module. Then `H^p(U, g⁻¹I) = 0` for all `p > 0` and every
object `U` of the cofinal system of coverings, in particular for every object of `C` when the
system is cofinal everywhere. As in the source, the cohomology of a module is that of its
underlying abelian sheaf.

Neither site is assumed small, and the morphism universes of the two sites are unrelated to the
coefficient universe, which need only contain them and the objects. -/
@[stacks 0D6X "the morphism universes of the two sites are free and the sites are not assumed \
small; the coefficient universe contains their objects, and cohomology over an object is `Ext` \
out of the free abelian sheaf on the lifted representable"]
theorem injective_module_subsingleton_ext_of_functor
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsIso (cechProductMapOfFunctor u E.1 p i))
    (I : SheafOfModules.{max a u v u₂ v₂ r w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [Injective I]
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Ext ((presheafToSheaf J AddCommGrpCat.{max a u v u₂ v₂ r w}).obj
      (uliftYoneda.{max a u v u₂ v₂ r w}.obj U ⋙ AddCommGrpCat.free))
      ((u.sheafPushforwardContinuous AddCommGrpCat.{max a u v u₂ v₂ r w} J Y.J).obj
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj I)) p) :=
  subsingleton_ext_of_cechCohomology_isZero_of_functor.{x, max a r} J Y.J u B Cov hProducts
    hImageProducts hCovObjects hCovCofinal hComparison
    ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj I)
    (fun E hE q hq ↦
      let := hImageProducts E hE
      injective_moduleCechCohomology_isZero.{max a u v, w, u₂, v₂, r} Y (E.1.map u) I q hq)
    U hU p hp

end Modules

/-! ### Coefficients in a sheaf of rings, not assumed commutative

The same vanishing for an arbitrary site `(D, K)` with a sheaf of rings `O : Sheaf K RingCat`,
not assumed commutative; a ringed site is the case
`O = Stacks.SheafOfModules.Tensor.ringSheaf Y.O`. -/

section ModulesSheafOfRings

variable {C : Type u} [Category.{v} C]
  {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (O : Sheaf K RingCat.{r})
  (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max a u v u₂ v₂ r w}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max a u v u₂ v₂ r w})]
  (u : C ⥤ D) [u.IsContinuous J K]
  (B : Set C)
  (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
  (hProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
  (hImageProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → (E.1.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.1.map u).f (i a))))

/-- **Stacks Project, Tag 0D6X, with the morphism universes free.** Let `u : C ⥤ D` be a
continuous functor of sites and let `g : Sh(C) → Sh(D)` be the corresponding morphism of topoi,
so that `g⁻¹` is restriction along `u` by Sites, Lemma 00XR. Let `O_D` be a sheaf of rings on
`D` and let `I` be an injective `O_D`-module. Then `H^p(U, g⁻¹I) = 0` for all `p > 0` and every
object `U` of the cofinal system of coverings, in particular for every object of `C` when the
system is cofinal everywhere. As in the source, the cohomology of a module is that of its
underlying abelian sheaf.

Neither site is assumed small, and the morphism universes of the two sites are unrelated to the
coefficient universe, which need only contain them and the objects. -/
@[stacks 0D6X "the morphism universes of the two sites are free and the sites are not assumed \
small; the coefficient universe contains their objects, and cohomology over an object is `Ext` \
out of the free abelian sheaf on the lifted representable"]
theorem injective_module_subsingleton_ext_of_functor_sheafOfRings
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsIso (cechProductMapOfFunctor u E.1 p i))
    (I : SheafOfModules.{max a u v u₂ v₂ r w} O) [Injective I]
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Ext ((presheafToSheaf J AddCommGrpCat.{max a u v u₂ v₂ r w}).obj
      (uliftYoneda.{max a u v u₂ v₂ r w}.obj U ⋙ AddCommGrpCat.free))
      ((u.sheafPushforwardContinuous AddCommGrpCat.{max a u v u₂ v₂ r w} J K).obj
        ((SheafOfModules.toSheaf O).obj I)) p) :=
  subsingleton_ext_of_cechCohomology_isZero_of_functor.{x, max a r} J K u B Cov hProducts
    hImageProducts hCovObjects hCovCofinal hComparison
    ((SheafOfModules.toSheaf O).obj I)
    (fun E hE q hq ↦
      let := hImageProducts E hE
      injective_moduleCechCohomology_isZero_sheafOfRings.{max a u v, w, u₂, v₂, r} K O
        (E.1.map u) I q hq)
    U hU p hp

end ModulesSheafOfRings

section Terminal

/-- The forgetful functor on abelian groups is corepresented by the free abelian group on a
one-point type: a homomorphism out of it is one element of the target. -/
noncomputable def forgetCorepresentableByFreePUnit :
    (forget AddCommGrpCat.{t}).CorepresentableBy
      (AddCommGrpCat.free.obj (ULift.{t} PUnit.{1})) where
  homEquiv {Y} := (AddCommGrpCat.adj.homEquiv (ULift.{t} PUnit.{1}) Y).trans
    (TypeCat.homEquiv.trans
      (Equiv.funUnique (ULift.{t} PUnit.{1}) ((forget AddCommGrpCat.{t}).obj Y)))
  homEquiv_comp {Y Y'} g f := by
    dsimp only [Equiv.trans_apply]
    rw [AddCommGrpCat.adj.homEquiv_naturality_right]
    rfl

/-- The free abelian group on a one-point type is `ℤ`: both corepresent the forgetful
functor. -/
noncomputable def freePUnitIsoInt :
    AddCommGrpCat.free.obj (ULift.{t} PUnit.{1}) ≅ AddCommGrpCat.of (ULift.{t} ℤ) :=
  Functor.CorepresentableBy.uniqueUpToIso forgetCorepresentableByFreePUnit
    ((Functor.CorepresentableBy.coyoneda (op (AddCommGrpCat.of (ULift.{t} ℤ)))).ofIso
      AddCommGrpCat.coyonedaObjIsoForget)

/-- The representable presheaf of a terminal object of a category is the one-point presheaf. -/
def uliftYonedaObjIsoConst {C : Type u} [Category.{v} C] {e : C} (he : IsTerminal e) :
    uliftYoneda.{t}.obj e ≅ (Functor.const Cᵒᵖ).obj (ULift.{max t v} PUnit.{1}) :=
  NatIso.ofComponents
    (fun Y ↦
      letI : Unique (Y.unop ⟶ e) := ⟨⟨he.from _⟩, fun g ↦ he.hom_ext g _⟩
      letI : Unique ((uliftYoneda.{t}.obj e).obj Y) :=
        inferInstanceAs (Unique (ULift.{t} (Y.unop ⟶ e)))
      letI : Unique (((Functor.const Cᵒᵖ).obj (ULift.{max t v} PUnit.{1})).obj Y) :=
        inferInstanceAs (Unique (ULift.{max t v} PUnit.{1}))
      Equiv.toIso (Equiv.ofUnique _ _))
    (fun _ ↦ by
      apply TypeCat.homEquiv.injective
      funext s
      apply Subsingleton.elim (α := ULift.{max t v} PUnit.{1}))

/-- **The free abelian sheaf on a terminal object of a site is the constant sheaf `ℤ`.**
Cohomology over a terminal object is therefore the global cohomology of the site,
`CategoryTheory.Sheaf.H`. -/
noncomputable def freeSheafIsoConstantSheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{max t v}]
    {e : C} (he : IsTerminal e) :
    (presheafToSheaf J AddCommGrpCat.{max t v}).obj
        (uliftYoneda.{t}.obj e ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{max t v}).obj (AddCommGrpCat.of (ULift.{max t v} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{max t v}).mapIso
    (Functor.isoWhiskerRight (uliftYonedaObjIsoConst.{t} he) AddCommGrpCat.free ≪≫
      Functor.constComp _ _ _ ≪≫ (Functor.const Cᵒᵖ).mapIso freePUnitIsoInt)

/-- Cohomology over a terminal object is global cohomology, so vanishing of the former gives
vanishing of the latter. -/
private theorem subsingleton_sheafH_of_subsingleton_ext {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max t v}]
    [HasExt.{x} (Sheaf J AddCommGrpCat.{max t v})] {e : C} (he : IsTerminal e)
    (F : Sheaf J AddCommGrpCat.{max t v}) (p : ℕ)
    (h : Subsingleton (Ext ((presheafToSheaf J AddCommGrpCat.{max t v}).obj
      (uliftYoneda.{t}.obj e ⋙ AddCommGrpCat.free)) F p)) :
    Subsingleton (Sheaf.H F p) :=
  (((Abelian.extFunctor p).mapIso
    (freeSheafIsoConstantSheaf.{t} J he).op).app F).addCommGroupIsoToAddEquiv.subsingleton_congr.mpr
      h

/-- **Stacks Project, Tag 03F9 at a terminal object: global cohomology from Čech vanishing.**
Let `(C, J)` be a site, let `B` be a collection of objects of `C` and let `Cov` be a collection
of coverings whose members and whose nonempty finite fibre products again lie in `B`, cofinal
among the coverings of the objects of `B`. If the positive-degree Čech cohomology of an abelian
sheaf `F` vanishes on every covering in `Cov`, and `B` contains a terminal object of `C`, then
the global cohomology `CategoryTheory.Sheaf.H` of `F` vanishes in positive degrees.

This is `Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero` read at a terminal object:
the free abelian sheaf there is the constant sheaf `ℤ`, by
`Stacks.CechSite.freeSheafIsoConstantSheaf`, so cohomology over it is the cohomology of the site.

Its point is that *ordinary* coverings suffice for a global statement. Global cohomology is `Ext`
out of the constant sheaf, and the direct route to it — resolving the constant sheaf by free
abelian sheaves on representables — asks for a hypercovering of the terminal sheaf in every
degree. Here no resolution of the terminal sheaf is constructed: the terminal object is an object
of the site like any other, and the Čech complexes of the coverings in `Cov` are the only
complexes involved. -/
theorem subsingleton_sheafH_of_cechCohomology_isZero {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max a u v w}]
    [HasExt.{x} (Sheaf J AddCommGrpCat.{max a u v w})]
    (B : Set C)
    (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
    (hProducts : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
      E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (F : Sheaf J AddCommGrpCat.{max a u v w})
    (hCech : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ), 0 < p →
        letI : ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (i a))) := hProducts E hE
        IsZero (cechCohomology E.1 F.obj p))
    {e : C} (he : IsTerminal e) (heB : e ∈ B) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H F p) := by
  exact subsingleton_sheafH_of_subsingleton_ext.{x, max a u v w} J he F p
    (subsingleton_ext_of_cechCohomology_isZero.{x, a} J B Cov hProducts
      hCovObjects hCovCofinal F hCech e heB p hp)

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max a u v u₂ v₂ w}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max a u v u₂ v₂ w})]
  (u : C ⥤ D) [u.IsContinuous J K]
  (B : Set C)
  (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
  (hProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
  (hImageProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → (E.1.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.1.map u).f (i a))))

/-- **Stacks Project, Tag 0D6X for the global cohomology of the source site.** Let
`u : C ⥤ D` be a continuous functor of sites, let `g : Sh(C) → Sh(D)` be the corresponding
morphism of topoi and let `e` be a terminal object of `C` belonging to the cofinal system of
coverings. If `I` is an injective abelian sheaf on `D` then the global cohomology
`H^p(C, g⁻¹I)` vanishes for `p > 0`.

This is the form in which the acyclicity hypothesis of Stacks 07AK is stated: the cohomology
over an object of a site is the global cohomology of the slice at that object, and the slice
has a terminal object. -/
@[stacks 0D6X "global cohomology of the source site, at a terminal object; the morphism \
universes of the two sites are free and the sites are not assumed small"]
theorem injective_sheaf_subsingleton_sheafH_of_functor
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsIso (cechProductMapOfFunctor u E.1 p i))
    (I : Sheaf K AddCommGrpCat.{max a u v u₂ v₂ w}) [Injective I]
    {e : C} (he : IsTerminal e) (heB : e ∈ B) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H
      ((u.sheafPushforwardContinuous AddCommGrpCat.{max a u v u₂ v₂ w} J K).obj I) p) := by
  exact subsingleton_sheafH_of_subsingleton_ext.{x, max a u v u₂ v₂ w} J he _ p
    (injective_sheaf_subsingleton_ext_of_functor.{x, a} J K u B Cov hProducts
      hImageProducts hCovObjects hCovCofinal hComparison I e heB p hp)

end Terminal

end Stacks.CechSite

end
