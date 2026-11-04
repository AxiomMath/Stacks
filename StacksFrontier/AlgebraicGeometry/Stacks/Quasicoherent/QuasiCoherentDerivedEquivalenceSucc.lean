module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KernelColocalizationCharacterization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsSheafFlatBaseChange

/-!
# Towards Stacks 0H16: `Q_𝒳 = 𝒜` inside `D(𝒳_{fppf}, 𝒪)` at module universe `u + 1`

Let `𝒳` be an algebraic stack. The proof of **Stacks 0H16** views `QC(𝒳)` as a full subcategory
`Q_𝒳` of `D(𝒳_{fppf}, 𝒪)` (Stacks 0H0X and 0H0C,
`AlgebraicGeometry.Stack.FlatFppf.quasiCoherentDerivedFppfSucc`) and `D_QCoh(𝒪_𝒳)` as the left
orthogonal `𝒜` of `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` in `D_{LQCoh^fbc}(𝒪_𝒳)` (Stacks 07BA, 0H11),
and shows `Q_𝒳 = 𝒜`. This file proves every step of that argument except the two inputs it takes
from Stacks 0H15: the "RΓ bridge" (membership in `Q_𝒳` is the base change property
`AlgebraicGeometry.Stack.FlatFppf.HasAffineDerivedSectionsBaseChange`, by the footnote of
Stacks 0GZS) and Stacks 0H15 itself.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isTriangulated_quasiCoherentDerivedFppfSucc`: `Q_𝒳` is a
  triangulated subcategory (the preimage of `QC(𝒳)`, Stacks 0GYW, under `Rε_* ∘ Φ`).
* `AlgebraicGeometry.Stack.FlatFppf.isCoveringFamily_isAffine_hom_flatAffine`: the affine objects
  admitting a morphism to a flat affine object cover `𝒳_{fppf}`.
* `AlgebraicGeometry.Stack.FlatFppf.isZero_of_derivedInter_of_hasAffineDerivedSectionsBaseChange`:
  an object of `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` with the base change property is zero. This
  replaces **Step 2** of the source (which computes `RΓ(x, R𝓗om(K, P))` by Stacks 08JA and 0H0T):
  applied to the cone of `Lg_! g^* K ⟶ K` it gives `Q_𝒳 ⊂ 𝒜`.
* `AlgebraicGeometry.Stack.FlatFppf.quasiCoherentDerivedFppfSucc_eq_interLeftOrthogonal_of`:
  `Q_𝒳 = 𝒜` from the bridge and Stacks 0H15 (**Steps 1–3**), and
  `AlgebraicGeometry.Stack.FlatFppf.quasiCoherentDerivedEquivalenceOfEqInterLeftOrthogonal`:
  `QC(𝒳) ≌ D_QCoh(𝒪_𝒳)` from `Q_𝒳 = 𝒜`.

**Step 1** (the base change property forces `K ∈ D_{LQCoh^fbc}(𝒪_𝒳)`,
`derivedCategoryB_sheafFlatBaseChangeModulesSucc_of_hasAffineDerivedSectionsBaseChange`) lives in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsSheafFlatBaseChange`,
below the proof of Stacks 0H15, which also uses it.

## References

* [Stacks Project, Tag 0H16](https://stacks.math.columbia.edu/tag/0H16)
* [Stacks Project, Tag 0H15](https://stacks.math.columbia.edu/tag/0H15)
* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v w t r m i

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-! ### `Q_𝒳` is triangulated -/

section AnyModel

variable [HasDerivedCategory.{t} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))]

/-- `Q_𝒳` is closed under isomorphisms in `D(𝒳_{fppf}, 𝒪)`. -/
instance isClosedUnderIsomorphisms_quasiCoherentDerivedFppfSucc :
    (quasiCoherentDerivedFppfSucc B S hS 𝒳).IsClosedUnderIsomorphisms :=
  ⟨fun e hX => (Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderIsomorphisms
      (affineBaseChangeData.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p)).of_iso
    ((Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonPushforward.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)).mapIso
        ((affineFppfDerivedRestrictionSucc B S hS 𝒳).mapIso e)) hX⟩

/-- **`Q_𝒳` is a triangulated subcategory of `D(𝒳_{fppf}, 𝒪)`**: it is the preimage of the
triangulated subcategory `QC(𝒳)` (Stacks 0GYW) under `Rε_*`, a right derived functor, composed
with the exact equivalence `Φ` of Stacks 0H0C. -/
instance isTriangulated_quasiCoherentDerivedFppfSucc :
    (quasiCoherentDerivedFppfSucc B S hS 𝒳).IsTriangulated := by
  have : ObjectProperty.IsTriangulated (C := DerivedCategory (PresheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O).obj))
      (IsQuasiCoherentObject.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p) :=
    Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isTriangulated
      (affineBaseChangeData.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p)
  have : ObjectProperty.IsClosedUnderIsomorphisms (C := DerivedCategory (PresheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O).obj))
      (IsQuasiCoherentObject.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p) :=
    Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderIsomorphisms
      (affineBaseChangeData.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p)
  have : (Stacks.ModulesOnACategory.ChaoticComparison.pushforwardProperty.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)
      (IsQuasiCoherentObject.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p)).IsTriangulated :=
    ObjectProperty.isTriangulated_inverseImage_of_commShift
      (Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonPushforward.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O))
      (Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonPushforwardCommShift.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O))
      (Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonPushforward_isTriangulated.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O))
      (IsQuasiCoherentObject.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p)
  have : (Stacks.ModulesOnACategory.ChaoticComparison.pushforwardProperty.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)
      (IsQuasiCoherentObject.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p)).IsClosedUnderIsomorphisms :=
    ⟨fun e hX => (Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderIsomorphisms
      (affineBaseChangeData.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p)).of_iso
      ((Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonPushforward.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineFppfRingedSite B S hS 𝒳).O)).mapIso e) hX⟩
  exact ObjectProperty.isTriangulated_inverseImage_of_commShift
    (affineFppfDerivedRestrictionSucc B S hS 𝒳) inferInstance inferInstance _

end AnyModel

/-! ### A covering family of the fppf site of `𝒳` -/

/-- **The objects of `𝒳` lying over an affine scheme and admitting a morphism to a flat object
lying over an affine scheme form a covering family of the fppf site of `𝒳`.**

By `AlgebraicGeometry.Stack.coversTop_flatObject_of_local` (a smooth atlas and Stacks 06QA) every
object is covered by objects admitting a morphism to a flat object lying over an affine scheme;
the affine open coverings of those objects
(`AlgebraicGeometry.Stack.exists_isAffine_covering_of_object`) refine this to a covering by
objects lying over affine schemes. -/
theorem isCoveringFamily_isAffine_hom_flatAffine :
    (fppfTopology B S hS 𝒳).IsCoveringFamily (fun y =>
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) ∧
        ∃ x' : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x' ∧
          IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x')) ∧
            Nonempty (y ⟶ x')) := by
  -- an object is covered by objects lying over affine schemes, over flat morphisms
  have cover : ∀ w (T : Sieve w),
      (∀ y (g : y ⟶ w),
        IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) →
          Flat (B.inclusion.map (𝒳.val.val.p.map g).left) → T g) →
      T ∈ fppfTopology B S hS 𝒳 w := fun w T hT => by
    obtain ⟨I, y, f, hy, haff, hflat⟩ := exists_isAffine_covering_of_object B S hS 𝒳.val w
    refine (fppfTopology B S hS 𝒳).superset_covering ?_ hy
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact hT _ _ (haff i) (hflat i)
  have hcov := coversTop_flatObject_of_local B S hS 𝒳
    (fun x => IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x))) (fun x hx =>
      cover x _ fun y g hy hg => (Sieve.mem_ofObjects_iff _ _).2
        ⟨⟨y, flatObject_of_flat B S hS 𝒳 g hg hx, hy⟩, ⟨𝟙 _⟩⟩)
  intro z
  refine ⟨_, ?_, fun _ _ h => h⟩
  refine (fppfTopology B S hS 𝒳).transitive (hcov z) _ fun w g hg => ?_
  obtain ⟨⟨x', hx'flat, hx'aff⟩, ⟨m⟩⟩ := (Sieve.mem_ofObjects_iff _ _).1 hg
  exact cover w _ fun y f hy _ => Sieve.le_generate _ _ _ ⟨hy, x', hx'flat, hx'aff, ⟨f ≫ m⟩⟩

/-! ### An object of `Q_𝒳` with parasitic cohomology is zero -/

section ParasiticVanishing

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasSheafify_fppfTopology_largeSections
  wEqualsLocallyBijective_fppfTopology_largeSections

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

open Stacks.Cohomology.HypercohomologyEdge
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

attribute [local instance] isGrothendieckAbelian_ambientModulesSucc

-- the small-Hom model of the derived category of presheaves of modules has a free universe,
-- which instance search cannot solve; the edge morphism is read at the standard model
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- **An object of `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` whose derived sections satisfy the base change
property of Stacks 0H15 is zero.**

Over a flat object `x'` lying over an affine scheme, `H^q(RΓ(x', C)) = Γ(x', H^q C)` (Stacks 0BKZ
for `LQCoh^fbc`, `isIso_hypercohomologyEdge_app_of_sheafFlatBaseChange`) vanishes, `H^q C` being
parasitic; so `RΓ(x', C) = 0`. For an affine object `y` with a morphism `y ⟶ x'`, the base change
property gives `RΓ(y, C) = RΓ(x', C) ⊗^L 𝒪(y) = 0`, hence `Γ(y, H^q C) = 0`. Such objects `y`
cover the fppf site (`isCoveringFamily_isAffine_hom_flatAffine`), so every `H^q C` vanishes.

This replaces the second step of the source's proof of Stacks 0H16 (which computes
`RΓ(x, R𝓗om(K, P))` by Stacks 08JA and 0H0T): there, it is applied to the cone of
`Lg_! g^* K ⟶ K`. -/
theorem isZero_of_derivedInter_of_hasAffineDerivedSectionsBaseChange
    (C : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hC : DerivedCategory.KernelColocalization.derivedInter (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) C)
    (hbc : HasAffineDerivedSectionsBaseChange B S hS 𝒳 C) :
    IsZero C := by
  have : IsGrothendieckAbelian.{u + 1}
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE.{u + 1} _
  have hL : DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) C :=
    fun n => (hC n).2
  -- the sections of the cohomology sheaves over an affine object are the cohomology of `RΓ`
  have edge : ∀ (y : 𝒳.val.val.obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) → ∀ q : ℤ,
      ((DerivedCategory.homologyFunctor _ q).obj
          ((derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) y).obj
            C)) ≅
        (SheafOfModules.evaluation (ambientRingStructureSheaf B S hS 𝒳) (op y)).obj
          ((DerivedCategory.homologyFunctor _ q).obj C) := fun y hy q =>
    have := isIso_hypercohomologyEdge_app_of_sheafFlatBaseChange B S hS 𝒳 E h C hL y hy q
    asIso ((hypercohomologyEdge.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) y
      q).app C)
  -- `RΓ(x', C) = 0` over a flat object lying over an affine scheme
  have hflat : ∀ x' : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x' →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x')) →
      IsZero ((derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳)
        x').obj C) := fun x' hx' haff => by
    refine (DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun q => ?_
    refine IsZero.of_iso ?_ (edge x' haff q)
    exact @ModuleCat.isZero_of_subsingleton _ _ _ ((hC q).1 x' hx')
  -- `Γ(y, H^q C) = 0` for the members of the covering family
  have hsec : ∀ (q : ℤ) (y : 𝒳.val.val.obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) ∧
      (∃ x' : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x' ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x')) ∧
          Nonempty (y ⟶ x')) →
      Subsingleton ((SheafOfModules.evaluation (ambientRingStructureSheaf B S hS 𝒳) (op y)).obj
          ((DerivedCategory.homologyFunctor _ q).obj C)) := by
    rintro q y ⟨hy, x', hx', hx'aff, ⟨a⟩⟩
    have := hbc a hy hx'aff
    have := (dBaseChangeAdj.{u, u + 1} ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 y)).isLeftAdjoint
    have hy0 : IsZero ((derivedSections.{_, _, _, u + 1, u + 1}
        (ambientRingStructureSheaf B S hS 𝒳) y).obj C) :=
      (Functor.map_isZero _ (hflat x' hx' hx'aff)).of_iso
        (asIso (derivedSectionsBaseChange B S hS 𝒳 a C)).symm
    exact ModuleCat.isZero_iff_subsingleton.1
      (((DerivedCategory.homologyFunctor _ q).map_isZero hy0).of_iso (edge y hy q).symm)
  refine (DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun q => ?_
  -- a sheaf of modules with no sections over a covering family is zero
  have hz : IsZero ((SheafOfModules.toSheaf (ambientRingStructureSheaf B S hS 𝒳)).obj
      ((DerivedCategory.homologyFunctor _ q).obj C)) :=
    Sheaf.isZero_of_isCoveringFamily _ (isCoveringFamily_isAffine_hom_flatAffine B S hS 𝒳)
      fun y hy => @AddCommGrpCat.isZero_of_subsingleton _ (hsec q y hy)
  exact (IsZero.iff_id_eq_zero _).2
    ((SheafOfModules.toSheaf (ambientRingStructureSheaf B S hS 𝒳)).map_injective (hz.eq_of_src _ _))

/-- **`QC(𝒳) ≌ D_QCoh(𝒪_𝒳)` at module universe `u + 1`, once `Q_𝒳 = 𝒜`**: `QC(𝒳) ≌ Q_𝒳` (Stacks
0H0X and 0H0C, `quasiCoherentDerivedEquivalenceFppfSucc`), `Q_𝒳 = 𝒜`, and `𝒜 ≌ D_QCoh(𝒪_𝒳)` (Stacks
0H11, `interLeftOrthogonalToClass_parasiticModulesSucc_comp_isEquivalence`), `D_QCoh(𝒪_𝒳)` being
the Verdier quotient `D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of Stacks 07B6. -/
def quasiCoherentDerivedEquivalenceOfEqInterLeftOrthogonal
    (hQA : quasiCoherentDerivedFppfSucc B S hS 𝒳 =
      DerivedCategory.KernelColocalization.interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)) :
    quasiCoherentDerived.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p ≌
      DerivedCategory.KernelColocalization.quotient (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) :=
  haveI := interLeftOrthogonalToClass_parasiticModulesSucc_comp_isEquivalence B E h S hS 𝒳
  haveI : (DerivedCategory.KernelColocalization.interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsClosedUnderIsomorphisms :=
    (interLeftOrthogonal_parasiticModulesSucc_isSaturated B E h S hS 𝒳).1
  (quasiCoherentDerivedEquivalenceFppfSucc B S hS 𝒳).trans
    (((CategoryTheory.Equivalence.refl (C := DerivedCategory (SheafOfModules.{u + 1}
        (ambientRingStructureSheaf B S hS 𝒳)))).congrFullSubcategory hQA.symm).trans
      (DerivedCategory.KernelColocalization.interLeftOrthogonalToClass
          (parasiticModulesSucc B S hS 𝒳) (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) ⋙
        DerivedCategory.KernelColocalization.toQuotient (parasiticModulesSucc B S hS 𝒳)
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).asEquivalence)

/-! ### `Q_𝒳 = 𝒜`, from the RΓ bridge and Stacks 0H15 -/

/-- **`Q_𝒳 = 𝒜` inside `D(𝒳_{fppf}, 𝒪)`, from two inputs**: the RΓ bridge (an object lies in
`Q_𝒳` exactly when it has the base change property of Stacks 0H15) and Stacks 0H15 itself (`Lg_!`
of an object of `D_QCoh(𝒪_{𝒳_{flat,fppf}})` has that property).

Step 1 of the source's proof, `Q_𝒳 ⊂ D_{LQCoh^fbc}(𝒪_𝒳)`, is
`derivedCategoryB_sheafFlatBaseChangeModulesSucc_of_hasAffineDerivedSectionsBaseChange`; for `K`
in `D_{LQCoh^fbc}(𝒪_𝒳)`, `g^* K` lies in `D_QCoh(𝒪_{𝒳_{flat,fppf}})` (Stacks 07B9 (2)(a)), so
`Lg_! g^* K ∈ Q_𝒳`; and an object of `Q_𝒳 ∩ D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is zero
(`isZero_of_derivedInter_of_hasAffineDerivedSectionsBaseChange`). The canonical triangle of
Stacks 07BA then gives `Q_𝒳 = 𝒜`
(`DerivedCategory.KernelColocalization.eq_interLeftOrthogonal_of_isZero_of_derivedInter`). -/
theorem quasiCoherentDerivedFppfSucc_eq_interLeftOrthogonal_of
    (hbridge : ∀ K, quasiCoherentDerivedFppfSucc B S hS 𝒳 K ↔
      HasAffineDerivedSectionsBaseChange B S hS 𝒳 K)
    (hshriek : ∀ H : DerivedCategory (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)),
      DerivedCategoryB.derivedCategoryB (flatQuasicoherentModulesSucc B S hS 𝒳) H →
        HasAffineDerivedSectionsBaseChange B S hS 𝒳
          ((derivedModuleLowerShriekSucc B S hS 𝒳).obj H)) :
    quasiCoherentDerivedFppfSucc B S hS 𝒳 =
      DerivedCategory.KernelColocalization.interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) :=
  DerivedCategory.KernelColocalization.eq_interLeftOrthogonal_of_isZero_of_derivedInter _ _
    (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳)
    (isZero_moduleInverseImage_mapDerivedCategory_iff_forall_isParasitic B S hS 𝒳)
    (isIso_derivedModuleLowerShriekSuccAdjunction_unit B S hS 𝒳)
    (derivedCategoryB_derivedModuleLowerShriekSucc_moduleInverseImage_sheafFlatBaseChange
      B E h S hS 𝒳) _
    (fun K hK =>
      derivedCategoryB_sheafFlatBaseChangeModulesSucc_of_hasAffineDerivedSectionsBaseChange
        B S hS 𝒳 E h K ((hbridge K).1 hK))
    (fun K hK => (hbridge _).2 (hshriek _
      (derivedCategoryB_moduleInverseImage_mapDerivedCategory B S hS 𝒳 _
        (fun F hF => isQuasicoherentOnSite_moduleInverseImage_of_sheafFlatBaseChangeModulesSucc
          B E h S hS 𝒳 F hF) K hK)))
    fun K hK hP =>
      isZero_of_derivedInter_of_hasAffineDerivedSectionsBaseChange B S hS 𝒳 E h K hP
        ((hbridge K).1 hK)

end ParasiticVanishing

end AlgebraicGeometry.Stack.FlatFppf

end
