module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Module.FinitePresentation
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafify
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkCriterionPartOneReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkOfAFreeModule

/-!
# Finitely presented modules over a stalk ring are retracts of stalks

Let `(C, O)` be a ringed site and `Φ` a point of `C`.  Every finitely presented module `N` over
the stalk ring `O_Φ` is a **retract** of the stalk at `Φ` of a sheaf of `O`-modules.

The construction is the source's, with the realization weakened to a retract.  A finitely
presented `N` sits in a right exact sequence `O_Φ^m --G--> O_Φ^n --> N --> 0`.  The `m · n`
entries of `G` are elements of the stalk `O_Φ = colim_{(V, y)} O(V)`, and the category of
neighbourhoods of `Φ` is cofiltered, so finitely many of them are germs of sections over one
neighbourhood `(U, x₀)`: there is a matrix `A` of sections of `O` over `U` whose matrix of germs
at `(U, x₀)` is `G`.  That matrix defines a morphism `j_{U!}O_U^m ⟶ j_{U!}O_U^n` of presheaves
of `O`-modules whose cokernel `F` has `N` as a retract of its stalk: the stalk functor is exact,
so it carries the cokernel to the cokernel of the matrix of germs, and the `(U, x₀)`-summand of
the stalk of `j_{U!}O_U^k` is a retract of that stalk compatibly with the matrix.  Finally the
stalk does not see sheafification, so the sheafification of `F` serves as the sheaf of modules
the statement asks for.

Discharging this closes the last obligation in the chain that proves **part (1) of Stacks
0DEN**: a K-flat complex of `O`-modules has K-flat stalk complex at every point of the site.

## Main results

* `Stacks.Sheaves.FreeModuleStalk.exists_germHom_matrix`: a finite matrix of elements of the
  stalk ring is the matrix of germs, at one neighbourhood of `Φ`, of a matrix of sections of
  `O`.
* `Stacks.Sheaves.FreeModuleStalk.germMatrix_apply_eq`: such a matrix of germs *is* the linear
  map it descends.
* `Stacks.Sheaves.KFlatStalkCriterion.stalkRetractFinitelyPresented`: the statement above, which
  is `Stacks.Sheaves.KFlatStalkCriterion.StalkRetractFinitelyPresented`.
* `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat_unconditional`: **part (1) of
  Stacks 0DEN**, with no hypothesis beyond those of the source.

## Implementation notes

**Why a retract and not an isomorphism.**  The source replaces the site `C` by the slice `C/U`
and obtains an `O_U`-module on `C/U` whose stalk is `N` on the nose.  Over `C` itself that is
not available: the stalk of the extension by zero `j_{U!}G` at `Φ` is a direct sum of copies of
the stalks of `G`, one for each element of the fibre of `Φ` at `U` (Stacks 04H4), so what `C`
supplies is a module containing `N` as a summand.  A retract is what the consumer
`Stacks.Sheaves.KFlatStalkCriterion.stalkKFlatOfAcyclic_of_retract` needs, and the single
summand is what `Stacks.Sheaves.FreeModuleStalk.incl_proj` builds; the full decomposition of
Stacks 04H4 is not used.

**No descent of modules is needed, only of sections.**  Stacks 05N7 — a finitely presented
module over a filtered colimit of rings descends to a stage — is not invoked, and neither is
Stacks 0E8K, which the source reaches it through and which has no declaration in this
development.  What is used instead is that finitely many *elements* of the stalk come from one
neighbourhood, `Stacks.exists_toPresheafFiber_fin`, which is cofilteredness of the category of
neighbourhoods and nothing more.  The presentation itself is Mathlib's
`Module.FinitePresentation.exists_fin'`, whose shape is exactly the one
`Stacks.Sheaves.FreeModuleStalk.retract_cokernel` consumes.

**Exactness and sheafification.**  Two properties of the stalk functor on presheaves of modules
carry the argument: it preserves finite colimits
(`Stacks.instPreservesFiniteColimitsPresheafModuleFiber` together with
`Stacks.preservesFiniteColimits_restrictScalars`), which moves the cokernel across it; and it
does not see sheafification, which is Stacks 04EQ part (3) in the form
`Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.sheafifyStalkIso`.  The
decidability instance on the fibre of `Φ` at `U`, which the coefficient map of the retract needs,
is supplied classically and pinned once, so that the two intertwining squares are stated at the
same instance.

**Universes.** Everything is at a single universe `u`, with `Category.{u} C`.  This is the
narrowing `Stacks.Sheaves.KFlatStalkCriterion` and `Stacks.Sheaves.FreeModuleStalk` already
carry down the chain from `Stacks.SheafOfModules.Tensor.ringSheaf`; it is not decided here.

## References

* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
* [Stacks Project, Tag 04H4](https://stacks.math.columbia.edu/tag/04H4)
* [Stacks Project, Tag 0E8F](https://stacks.math.columbia.edu/tag/0E8F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace Stacks.Sheaves.FreeModuleStalk

open _root_.Stacks.Sheaves.KFlatStalkCriterion (structureStalk)

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u})
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (Φ : J.Point.{u})

/-! ### Finitely many elements of the stalk ring come from one neighbourhood -/

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Finitely many elements of the stalk ring `O_Φ` are simultaneously germs of sections of `O`
over one neighbourhood of `Φ`.  This is `Stacks.exists_toPresheafFiber_fin`, read through the
comparison of the `RingCat`-valued and `CommRingCat`-valued stalks of `O`. -/
lemma exists_germHom_fin {l : ℕ} (a : Fin l → structureStalk O Φ) :
    ∃ (V : C) (y : Φ.fiber.obj V) (s : Fin l → (ringPresheaf O).obj (op V)),
      ∀ i, germHom O Φ V y (s i) = a i := by
  obtain ⟨V, y, s, hs⟩ := Stacks.exists_toPresheafFiber_fin Φ (ringPresheaf O)
    (fun i ↦ (Stacks.commRingSheafFiberIso Φ O).inv.hom (a i))
  exact ⟨V, y, s, fun i ↦
    (congrArg (Stacks.commRingSheafFiberIso Φ O).hom.hom (hs i)).trans (by simp)⟩

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A finite matrix of elements of the stalk ring `O_Φ` is the matrix of germs, at one
neighbourhood `(U, x₀)` of `Φ`, of a matrix of sections of `O` over `U`.

The rows are descended one at a time by `exists_germHom_fin` and the neighbourhoods so produced
are merged by `Stacks.exists_common_neighbourhood`, which is cofilteredness of the category of
neighbourhoods of `Φ`. -/
lemma exists_germHom_matrix {n : ℕ} :
    ∀ {m : ℕ} (a : Fin m → Fin n → structureStalk O Φ),
      ∃ (U : C) (x₀ : Φ.fiber.obj U) (A : Fin m → Fin n → (ringPresheaf O).obj (op U)),
        ∀ j i, germHom O Φ U x₀ (A j i) = a j i := by
  intro m
  induction m with
  | zero =>
      intro _
      obtain ⟨E⟩ := (IsCofiltered.nonempty : Nonempty Φ.fiber.Elements)
      exact ⟨E.1, E.2, fun j ↦ j.elim0, fun j ↦ j.elim0⟩
  | succ m ih =>
      intro a
      obtain ⟨U, x, A, hA⟩ := ih (fun j ↦ a j.succ)
      obtain ⟨V, y, b, hb⟩ := exists_germHom_fin O Φ (a 0)
      obtain ⟨W, z, g₁, g₂, hg₁, hg₂⟩ := Stacks.exists_common_neighbourhood Φ x y
      refine ⟨W, z, Fin.cons (fun i ↦ (ringPresheaf O).map g₂.op (b i))
        (fun j i ↦ (ringPresheaf O).map g₁.op (A j i)), ?_⟩
      intro j i
      induction j using Fin.cases with
      | zero =>
          simp only [Fin.cons_zero]
          rw [germHom_restrict O Φ g₂ z (b i), hg₂, hb i]
      | succ k =>
          simp only [Fin.cons_succ]
          rw [germHom_restrict O Φ g₁ z (A k i), hg₁, hA k i]

/-! ### The matrix of germs of a descended matrix -/

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A matrix of germs is the linear map it descends.**  If the germs at `(U, x₀)` of a matrix
`A` of sections of `O` over `U` are the matrix entries of an `O_Φ`-linear map `g`, then
`germMatrix` of `A` agrees with `g`.  Both sides are linear, so it is enough to compare them on
the standard basis, which is what the hypothesis says. -/
lemma germMatrix_apply_eq {U : C} {n m : ℕ} (x₀ : Φ.fiber.obj U)
    (A : Fin m → Fin n → (ringPresheaf O).obj (op U))
    (g : (Fin m → structureStalk O Φ) →ₗ[structureStalk O Φ]
      (Fin n → structureStalk O Φ))
    (hA : ∀ j i, germHom O Φ U x₀ (A j i) = g (Pi.single j 1) i)
    (w : Fin m → structureStalk O Φ) (i : Fin n) :
    germMatrix O Φ U n x₀ m A w i = g w i := by
  rw [germMatrix_apply]
  conv_rhs => rw [← Finset.univ_sum_single w]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  have hs : (Pi.single j (w j) : Fin m → structureStalk O Φ) = w j • Pi.single j 1 := by
    funext k
    by_cases hk : j = k
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne (Ne.symm hk)]
  rw [hs, map_smul, Pi.smul_apply, smul_eq_mul, hA j i]

end Stacks.Sheaves.FreeModuleStalk

namespace Stacks.Sheaves.KFlatStalkCriterion

open Stacks.Sheaves.FreeModuleStalk

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u})
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-! ### The retract obligation, discharged -/

/-- **Every finitely presented module over the stalk ring is a retract of a stalk.**  For a
point `Φ` of the site and a finitely presented `O_Φ`-module `N`, there is a sheaf `F` of
`O`-modules and maps `N ⟶ F_Φ ⟶ N` composing to the identity.

The sheaf is the sheafification of the cokernel of the morphism `j_{U!}O_U^m ⟶ j_{U!}O_U^n` of
presheaves of `O`-modules attached to a matrix of sections of `O` over a neighbourhood `(U, x₀)`
of `Φ` whose germs are a presentation matrix of `N`. -/
theorem stalkRetractFinitelyPresented (Φ : J.Point.{u}) :
    StalkRetractFinitelyPresented O Φ := by
  intro N hN
  have := hN
  obtain ⟨n, m, f, g, hf, hgf⟩ :=
    Module.FinitePresentation.exists_fin' (structureStalk O Φ : Type u) (N : Type u)
  obtain ⟨U, x₀, A, hA⟩ := exists_germHom_matrix O Φ (fun j i ↦ g (Pi.single j 1) i)
  let _ : DecidableEq (Φ.fiber.obj U) := Classical.decEq _
  let : PreservesFiniteColimits (stalkPres O Φ) :=
    @comp_preservesFiniteColimits _ _ _ _ _ _
      (Stacks.presheafModuleFiber Φ (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
      (ModuleCat.restrictScalars.{u} (Stacks.commRingSheafFiberIso Φ O).inv.hom)
      (Stacks.instPreservesFiniteColimitsPresheafModuleFiber Φ
        (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
      (Stacks.preservesFiniteColimits_restrictScalars (Stacks.commRingSheafFiberIso Φ O).inv)
  have hGhom : (germMatrix O Φ U n x₀ m A).hom = g :=
    LinearMap.ext fun w ↦ funext fun i ↦ germMatrix_apply_eq O Φ x₀ A g hA w i
  have hExact : Function.Exact (germMatrix O Φ U n x₀ m A).hom f := by rwa [hGhom]
  have hret := retract_cokernel ((stalkPres O Φ).map (matrixHom O U n m A))
    (incl O Φ U n x₀) (proj O Φ U n x₀) (incl O Φ U m x₀) (proj O Φ U m x₀)
    (germMatrix O Φ U n x₀ m A) (incl_proj O Φ U n x₀)
    (incl_comp_stalkMap O Φ U n x₀ m A) (stalkMap_comp_proj O Φ U n x₀ m A) f hf hExact
  have hret₂ := retract_of_iso
    (PreservesCokernel.iso (stalkPres O Φ) (matrixHom O U n m A)).symm hret
  exact ⟨(PresheafOfModules.sheafification
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj (cokernel (matrixHom O U n m A)),
    retract_of_iso
      (Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.sheafifyStalkIso Φ O
        (cokernel (matrixHom O U n m A))) hret₂⟩

/-! ### Part (1) of Stacks 0DEN -/

section Tensor

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).Additive]
  [∀ X, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).obj X).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor O) (ComplexShape.up ℤ)]

/-- **Stacks 0DEN, part (1).**  On a ringed site, a K-flat complex of `O`-modules has K-flat
stalk complex at every point of the site.

This is `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat_of_stalkRetract` with its one
remaining obligation discharged by `stalkRetractFinitelyPresented`, so the hypotheses are
exactly those of the source.  Part (2), the converse under the hypothesis that the site has
enough points, is `Stacks.SheafOfModules.SitePointStalkSheafify.kFlat_of_stalks`. -/
@[stacks 0DEN "part (1)"]
theorem kFlatStalk_of_kFlat_unconditional (Φ : J.Point.{u})
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat O K) :
    CochainComplex.KFlat.{u, u} (stalkComplex O Φ K) :=
  kFlatStalk_of_kFlat_of_stalkRetract O (stalkRetractFinitelyPresented O Φ) K hK

end Tensor

end Stacks.Sheaves.KFlatStalkCriterion

end

end
