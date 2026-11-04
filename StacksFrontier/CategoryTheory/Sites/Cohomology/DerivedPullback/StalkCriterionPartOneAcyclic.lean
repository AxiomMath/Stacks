module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkCriterionPartOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafify
public import StacksFrontier.Homology.KFlat.AcyclicKFlat
public import StacksFrontier.Homology.KFlat.FinitelyPresented
public import StacksFrontier.Homology.TensorComplex.Monoidal
import StacksCore.Tactic.StacksAttribute

/-!
# The acyclic case of part (1) of the stalk criterion for K-flatness

`Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat` reduces part (1) of Stacks 0DEN — a
K-flat complex of `O`-modules on a ringed site has K-flat stalks — to two obligations: flatness
of the stalk of
a direct sum of extensions by zero, and the *acyclic case*
`Stacks.Sheaves.KFlatStalkCriterion.StalkKFlatOfAcyclic`, that a complex which is both K-flat and
  acyclic has K-flat
stalk.  This file proves the acyclic case, from the single remaining obligation that every
finitely presented module over the stalk ring is a **retract** of the stalk of a sheaf of
`O`-modules.

## Main definitions

* `Stacks.Sheaves.KFlatStalkCriterion.StalkRetractFinitelyPresented`: every finitely presented
  `O_Φ`-module is a
  retract of the stalk at `Φ` of some sheaf of `O`-modules.

## Main results

* `Stacks.Sheaves.KFlatStalkCriterion.stalkKFlatOfAcyclic_of_retract`: **the acyclic case of part
  (1)**, granted
  `StalkRetractFinitelyPresented`.
* `Stacks.Sheaves.KFlatStalkCriterion.stalkRetract_of_stalkRealizes`: the obligation of this file
  is weaker than
  `Stacks.Sheaves.KFlatStalkCriterion.StalkRealizesFinitelyPresented`, the realization obligation
  recorded alongside `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat`; an isomorphism is
  in particular a retract.
* `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat_of_retract`: **part (1) of Stacks 0DEN**
  on the two
  obligations `StalkFlatOfSumExtensionByZero` and `StalkRetractFinitelyPresented`.
  The other of the two, flatness of the stalk of a direct sum of extensions by zero, is proved
  unconditionally as `Stacks.Sheaves.KFlatStalkCriterion.stalkFlatOfSumExtensionByZero`, and
  `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat_of_stalkRetract` composes the two.

## Implementation notes

The source's proof of the acyclic case is: by Stacks 0E8F it suffices that `K_Φ ⊗_{O_Φ} N` be
acyclic for every finitely presented `O_Φ`-module `N`; realize `N` as the stalk of a sheaf `F`
of `O`-modules; `K ⊗_O F` is acyclic because `K` is K-flat and acyclic; and taking stalks is
exact, so `K_Φ ⊗_{O_Φ} N` is acyclic.  Each of the four steps is available here:

* Stacks 0E8F is `CochainComplex.KFlat.kFlat_of_tensor_finitelyPresented_acyclic`;
* `K ⊗_O F` acyclic is `Stacks.DerivedTensor.RingedSite.acyclic_tensorComplex_of_kFlat_of_acyclic`,
  which needs no
  hypothesis at all on the second argument;
* the stalk of a tensor product is the tensor product of the stalks — Stacks 03EL — is
  `Stacks.SheafOfModules.SitePointStalkSheafify.stalkTensorData`, carried through totalisation by
  `Stacks.Sheaves.KFlatStalkCriterion.totalStalkIso`;
* exactness of the stalk functor on complexes is
  `Stacks.acyclic_map_sheafModuleFiberOfCommRing`.

**The realization step is weakened to a retract, and that is not cosmetic.**  What the source
reaches is not an `O`-module on `C` with stalk `N`: its argument produces a finitely presented
`O(U)`-module on a neighbourhood `(U, x)` of `Φ` and then *replaces the site* `C` by the slice
`C/U` (Stacks 05N7 followed by Stacks 0E8K).  An `O`-module on `C` whose stalk at `Φ` is `N` on
the nose need not exist: the stalk of the extension by zero `j_{U!}G` at `Φ` is a direct sum of
copies of the stalks of `G`, one for each element of the fibre of `Φ` at `U`, so what `C` itself
supplies is a module containing `N` as a summand — the fibre is nonempty because `(U, x)` is a
neighbourhood.  A retract is enough: the functor `K_Φ ⊗ -` carries a retract to a retract, and a
retract of an acyclic complex is acyclic (`Stacks.Sheaves.KFlatStalkCriterion.acyclic_of_retract`),
  because the
identity of its homology factors through a zero object.

Two orientations meet in the middle and the braiding is what reconciles them.  K-flatness puts
the complex in the *second* argument of the tensor product — `CochainComplex.KFlat K` quantifies
over `Tot(G ⊗ K)` — while the hypothesis of Stacks 0E8F puts it in the *first*,
`Tot(K ⊗ N)`.  The symmetry used is
`TotalTensorComplex.cochainComplex_symmetricMonoidalCategory`, the Koszul-signed braiding of
cochain complexes of modules over a commutative ring, which is the same route
`StacksFrontier/Homology/KFlat/FinitelyPresented.lean` takes internally.

**Universes.** Everything is at a single universe `u`, with `Category.{u} C`, as in
`Stacks.Sheaves.KFlatStalkCriterion` and `Stacks.SheafOfModules.SitePointStalkSheafify`; the
narrowing comes down the chain from `Stacks.SheafOfModules.Tensor.ringSheaf` and is not decided
here.

**No tag is placed in this file.**  Nothing here states part (1) under the hypotheses of
Stacks 0DEN: `kFlatStalk_of_kFlat_of_retract` carries `StalkRetractFinitelyPresented`, a
`Prop`-valued `def` with no inhabitant in this development, so a tag would be a weakening.

## References

* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
* [Stacks Project, Tag 0E8F](https://stacks.math.columbia.edu/tag/0E8F)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

universe u

namespace Stacks.Sheaves.KFlatStalkCriterion

/-! ### A retract of an acyclic complex is acyclic -/

/-- **A retract of an acyclic complex is acyclic.**  The identity of the homology of the retract
factors through the homology of the acyclic complex, which is a zero object, so that identity is
zero. -/
theorem acyclic_of_retract {E : Type*} [Category E] [Abelian E]
    {X Y : CochainComplex E ℤ} (i : X ⟶ Y) (p : Y ⟶ X) (hip : i ≫ p = 𝟙 X)
    (hY : Y.Acyclic) : X.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have hid : HomologicalComplex.homologyMap i n ≫ HomologicalComplex.homologyMap p n
      = 𝟙 (X.homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, hip, HomologicalComplex.homologyMap_id]
  have hzero : IsZero (Y.homology n) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hY n
  rw [← hid, hzero.eq_zero_of_src (HomologicalComplex.homologyMap p n), comp_zero]

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u})
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-! ### The obligation -/

/-- **Every finitely presented `O_Φ`-module is a retract of a stalk.**

This is the source's "we may assume there exists an `O`-module `F` such that `N ≅ F_Φ`", weakened
from an isomorphism to a retract — which is what the site `C` itself supplies, and all that the
argument needs.  See the implementation notes: the source reaches the isomorphism only after
replacing `C` by a slice `C/U`, which is Stacks 0E8K and has no declaration in this tree, whereas
a retract comes from the extension by zero of a presentation over a neighbourhood of `Φ`,
together with Stacks 05N7. -/
def StalkRetractFinitelyPresented (Φ : J.Point.{u}) : Prop :=
  ∀ N : ModuleCat.{u} (structureStalk O Φ),
    Module.FinitePresentation (structureStalk O Φ) N →
      ∃ (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (i : N ⟶ (Stacks.sheafModuleFiberOfCommRing Φ O).obj F)
        (p : (Stacks.sheafModuleFiberOfCommRing Φ O).obj F ⟶ N), i ≫ p = 𝟙 N

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `StalkRealizesFinitelyPresented` implies the obligation of this file: an isomorphism of
modules is in particular a retract. -/
theorem stalkRetract_of_stalkRealizes {Φ : J.Point.{u}}
    (h : StalkRealizesFinitelyPresented O Φ) : StalkRetractFinitelyPresented O Φ := by
  intro N hN
  obtain ⟨F, ⟨e⟩⟩ := h N hN
  exact ⟨F, e.hom, e.inv, e.hom_inv_id⟩

/-! ### The acyclic case -/

section Tensor

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).Additive]
  [∀ X, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).obj X).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor O) (ComplexShape.up ℤ)]

/-- **The acyclic case of part (1) of Stacks 0DEN**: the stalk of a complex of `O`-modules which
is both K-flat and acyclic is a K-flat complex of `O_Φ`-modules, granted that every finitely
presented `O_Φ`-module is a retract of a stalk.

This discharges `Stacks.Sheaves.KFlatStalkCriterion.StalkKFlatOfAcyclic`, the second of the two
  obligations of
`Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat`. -/
theorem stalkKFlatOfAcyclic_of_retract {Φ : J.Point.{u}}
    (hret : StalkRetractFinitelyPresented O Φ) : StalkKFlatOfAcyclic O Φ := by
  intro M hM hMac
  -- The sheaf-level and stalk-level "module in degree zero" functors.
  set Ssh := HomologicalComplex.single
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (ComplexShape.up ℤ) 0 with hSsh
  set Sst := HomologicalComplex.single
    (ModuleCat.{u} (structureStalk O Φ)) (ComplexShape.up ℤ) 0 with hSst
  refine CochainComplex.KFlat.kFlat_of_tensor_finitelyPresented_acyclic
    (stalkComplex O Φ M) ?_
  intro N hN
  obtain ⟨F, i, p, hip⟩ := hret N hN
  -- `K ⊗_O F[0]` is acyclic: `M` is K-flat and acyclic, and nothing is asked of `F[0]`.
  have h1 := Stacks.DerivedTensor.RingedSite.acyclic_tensorComplex_of_kFlat_of_acyclic O hM hMac
    (Ssh.obj F)
  -- Taking stalks is exact.
  have h2 := Stacks.acyclic_map_sheafModuleFiberOfCommRing O Φ h1
  -- Stacks 03EL carried through totalisation.
  have h3 := HomologicalComplex.Acyclic.of_iso
    (Stacks.Sheaves.KFlatStalkCriterion.totalStalkIso O Φ
      (Stacks.SheafOfModules.SitePointStalkSheafify.stalkTensorData Φ O) (Ssh.obj F) M) h2
  have h3' : (stalkComplex O Φ (Ssh.obj F) ⊗ stalkComplex O Φ M).Acyclic := h3
  -- The stalk of `F[0]` is `F_Φ[0]`, the stalk functor being additive.
  have e1 : stalkComplex O Φ (Ssh.obj F) ≅
      Sst.obj ((Stacks.sheafModuleFiberOfCommRing Φ O).obj F) :=
    (HomologicalComplex.singleMapHomologicalComplex
      (Stacks.sheafModuleFiberOfCommRing Φ O) (ComplexShape.up ℤ) 0).app F
  have h4 := HomologicalComplex.Acyclic.of_iso
    (MonoidalCategory.whiskerRightIso e1 (stalkComplex O Φ M)) h3'
  -- Swap the two factors by the Koszul-signed braiding.
  obtain ⟨s, -⟩ := TotalTensorComplex.cochainComplex_symmetricMonoidalCategory
    (structureStalk O Φ : Type u)
  have h5 := HomologicalComplex.Acyclic.of_iso
    (s.toBraidedCategory.braiding
      (Sst.obj ((Stacks.sheafModuleFiberOfCommRing Φ O).obj F)) (stalkComplex O Φ M)) h4
  -- `N[0]` is a retract of `F_Φ[0]`, hence `K_Φ ⊗ N[0]` is a retract of `K_Φ ⊗ F_Φ[0]`.
  refine acyclic_of_retract (stalkComplex O Φ M ◁ Sst.map i)
    (stalkComplex O Φ M ◁ Sst.map p) ?_ h5
  rw [← MonoidalCategory.whiskerLeft_comp, ← CategoryTheory.Functor.map_comp, hip,
    CategoryTheory.Functor.map_id, MonoidalCategory.whiskerLeft_id]

/-- **Part (1) of Stacks 0DEN on two obligations.**  A K-flat complex of `O`-modules has K-flat
stalk at every point of the site, granted that the stalk of a direct sum of extensions by zero
is flat and that every finitely presented module over the stalk ring is a retract of a stalk.

This is `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat` with its acyclic-case obligation
  discharged by
`stalkKFlatOfAcyclic_of_retract`. -/
theorem kFlatStalk_of_kFlat_of_retract {Φ : J.Point.{u}}
    (hflat : StalkFlatOfSumExtensionByZero O Φ)
    (hret : StalkRetractFinitelyPresented O Φ)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat O K) :
    CochainComplex.KFlat.{u, u} (stalkComplex O Φ K) :=
  kFlatStalk_of_kFlat O hflat (stalkKFlatOfAcyclic_of_retract O hret) K hK

end Tensor

end Stacks.Sheaves.KFlatStalkCriterion

end

end
