module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOfComplex
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingComplexUniqueness
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedConnected
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatHomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing complex is not unique, and the dualizing module is unique up to a twist

The second warning of [Stacks, Section 48.22] (the section tag [Stacks, Tag 0AWH]) is that "the
dualizing complex isn't unique; the dualizing module is only unique up to tensoring by an
invertible module". This file proves both halves for `Stacks.Duality.IsDualizingModuleOf`.

* *Non-uniqueness of the complex.* A shift `K⟦k⟧` of a dualizing complex is a dualizing complex,
  not isomorphic to `K` when `k ≠ 0`, and its dualizing module is the dualizing module of `K`,
  realized in degree `n - k`: `Stacks.Duality.IsDualizingModuleOf.shift`.
* *Uniqueness of the module up to a twist.* On a connected locally Noetherian scheme, any two
  dualizing modules `ω` (of `K`) and `ω'` (of `K'`) satisfy `ω' ≅ ω ⊗_{𝒪_X} ℒ` for an invertible
  `𝒪_X`-module `ℒ`: `Stacks.Duality.IsDualizingModuleOf.exists_isInvertibleModule_iso_sheafTensor`.
  Given the complex, the module is determined outright:
  `Stacks.Duality.IsDualizingModuleOf.unique`.

## The proof

By [Stacks, Tag 0ATP] (`Stacks.Duality.exists_isInvertible_tensor_iso_of_isDualizingComplex`)
`K' ≅ K ⊗^𝐋 L` for an invertible object `L` of `D(𝒪_X)`. The stalks of `𝒪_X` are local rings, so
by [Stacks, Tag 0FPG] and connectedness `L ≅ ℒ[-m]` for one integer `m` and one invertible module
`ℒ` (`Stacks.Cohomology.InvertibleDerived.exists_isInvertibleModule_iso_singleFunctor`). The
shift passes out of the derived tensor product, and `ℒ[0]` is K-flat, so
`H^j(K') ≅ H^{j-m}(K) ⊗ ℒ` (`Stacks.Duality.homologyTensorSingleIso`). Tensoring by `ℒ` is an
equivalence, so it reflects the zero object; the least nonvanishing degrees therefore satisfy
`n' = n + m`, and in that degree the comparison is `ω' ≅ ω ⊗ ℒ`.

## Why `X` is connected

The source states the warning for a Noetherian scheme, and as a statement about two arbitrary
dualizing modules it needs `X` connected. On `X = Spec k ⊔ Spec k`, with `K = 𝒪_X` and `K'` equal
to `𝒪_X` on the first point and to `𝒪_X[1]` on the second, both are dualizing complexes; the least
nonvanishing degree of `K` is `0` with `ω = 𝒪_X`, and that of `K'` is `-1` with `ω'` the structure
sheaf of the second point alone, which is not `ω ⊗ ℒ = ℒ` for any invertible `ℒ`, since `ℒ` has
full support. The source's own Tag 0AWK, on the coherence and support of `ω_X`, also takes `X`
connected.

## Models of the derived category

`Stacks.Duality.IsDualizingModuleOf` takes `D(𝒪_X)` as an instance argument, while [Stacks, Tag
0ATP] is stated at `HasDerivedCategory.standard`. The two are compared through a representative
complex: `Stacks.Duality.isDualizingComplex_Q_of_isDualizingComplex_Q` shows that being a
dualizing complex does not depend on the model, and the cohomology sheaves of the same complex are
the same in both, so the main statement holds at every model.

## References

* [Stacks Project, Tag 0AWH](https://stacks.math.columbia.edu/tag/0AWH)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u w w'

namespace Stacks.Duality

section Model

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The image of `Q E` under restriction to an open `U`, in any model of the derived category,
is the image of the restricted complex. -/
private def restrictMapDerivedCategoryQIso.{v} (h : HasDerivedCategory.{v} X.Modules)
    (U : X.Opens) [HasDerivedCategory U.toScheme.Modules] (E : CochainComplex X.Modules ℤ) :
    (@Functor.mapDerivedCategory _ _ _ h _ _ _ _ (Scheme.Modules.restrictFunctor U.ι)
        _ _ _).obj ((@DerivedCategory.Q _ _ _ h).obj E) ≅
      DerivedCategory.Q.obj (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E) :=
  let := h
  (Functor.mapDerivedCategoryFactors (Scheme.Modules.restrictFunctor U.ι)).app E

/-- **Being a dualizing complex does not depend on the model of `D(𝒪_X)`.** If a complex `E`
of `𝒪_X`-modules is a dualizing complex in one model of the derived category, it is one in any
other: the restriction to an affine open of its image is, in both models, the image of the
restricted complex. -/
theorem isDualizingComplex_Q_of_isDualizingComplex_Q (h₁ : HasDerivedCategory.{w} X.Modules)
    (h₂ : HasDerivedCategory.{w'} X.Modules) (E : CochainComplex X.Modules ℤ)
    (hE : @IsDualizingComplex X _ h₁ ((@DerivedCategory.Q _ _ _ h₁).obj E)) :
    @IsDualizingComplex X _ h₂ ((@DerivedCategory.Q _ _ _ h₂).obj E) := by
  intro U hU
  obtain ⟨ω, hω, ⟨e⟩⟩ := hE U hU
  let := HasDerivedCategory.standard U.toScheme.Modules
  refine ⟨ω, hω, ⟨?_ ≪≫ e⟩⟩
  exact restrictMapDerivedCategoryQIso h₂ U E ≪≫ (restrictMapDerivedCategoryQIso h₁ U E).symm

end Model

section Twist

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

open Stacks.DerivedTensor.RingedSite in
/-- **The cohomology of a twist by a shifted invertible module.** For an object `K` of `D(𝒪_X)`
and an invertible `𝒪_X`-module `ℒ` placed in degree `m`,
`H^j(K ⊗^𝐋 ℒ[-m]) ≅ H^{j - m}(K) ⊗_{𝒪_X} ℒ`. The shift passes out of the derived tensor
product, and `ℒ[0]` is K-flat, so the twist is computed termwise and commutes with cohomology. -/
def homologyTensorSingleIso (K : DerivedCategory X.Modules) (ℒ : X.Modules)
    (hℒ : Stacks.SheafOfModules.Tensor.IsInvertibleModule X.sheaf ℒ) (m j : ℤ) :
    letI := Scheme.Modules.derivedMonoidal X
    (DerivedCategory.homologyFunctor X.Modules j).obj
        (K ⊗ (DerivedCategory.singleFunctor X.Modules m).obj ℒ) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
        ((DerivedCategory.homologyFunctor X.Modules (-m + j)).obj K)).obj ℒ :=
  let := Scheme.Modules.derivedMonoidal X
  let P := DerivedCategory.Q.objPreimage K
  let eP : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hflat := Stacks.SheafOfModules.isFlat_of_isInvertible_ringedSite X.sheaf _ ℒ hℒ
  let := (canonicalDerivedTensorProduct X.sheaf).commShift_right K
  (DerivedCategory.homologyFunctor X.Modules j).mapIso
      ((((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.sheaf
        (canonicalDerivedTensorProduct X.sheaf)).app K).app
        _) ≪≫
      ((canonicalDerivedTensorProduct X.sheaf).tensor.obj K).mapIso
        (((DerivedCategory.singleFunctors X.Modules).shiftIso (-m) m 0 (by omega)).app ℒ).symm ≪≫
      (((canonicalDerivedTensorProduct X.sheaf).tensor.obj K).commShiftIso (-m)).app _) ≪≫
    ((DerivedCategory.homologyFunctor X.Modules 0).shiftIso (-m) j (-m + j) rfl).app _ ≪≫
    (DerivedCategory.homologyFunctor X.Modules (-m + j)).mapIso
      (((canonicalDerivedTensorProduct X.sheaf).tensor.mapIso eP.symm).app _) ≪≫
    homologyTensorFlatIso X.sheaf ℒ hflat P (-m + j) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).mapIso
      (((DerivedCategory.homologyFunctorFactors X.Modules (-m + j)).app P).symm ≪≫
        (DerivedCategory.homologyFunctor X.Modules (-m + j)).mapIso eP)).app ℒ

/-- **Tensoring by an invertible module reflects the zero object**: it is an equivalence of
`X.Modules` ([Stacks, Tag 01CS]). -/
theorem isZero_sheafTensor_obj_obj_iff (A ℒ : X.Modules)
    (hℒ : Stacks.SheafOfModules.Tensor.IsInvertibleModule X.sheaf ℒ) :
    IsZero (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).obj ℒ) ↔ IsZero A := by
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj ℒ
  have : F.IsEquivalence :=
    (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ ℒ).mp hℒ
  have e : ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).obj ℒ ≅ F.obj A :=
    (Stacks.SheafOfModules.sheafTensorRightIsoTensorLeftFunctor X.sheaf _ ℒ).app A
  rw [e.isZero_iff]
  exact ⟨fun h => (F.inv.map_isZero h).of_iso (F.asEquivalence.unitIso.app A), F.map_isZero⟩

/-- **Two dualizing complexes on a connected locally Noetherian scheme have cohomology sheaves
differing by one shift and one invertible twist.** By [Stacks, Tag 0ATP], `K' ≅ K ⊗^𝐋 L` for an
invertible object `L` of `D(𝒪_X)`; on a connected scheme `L ≅ ℒ[-m]` for an invertible module
`ℒ` ([Stacks, Tag 0FPG]); and then `H^j(K') ≅ H^{j - m}(K) ⊗ ℒ`. -/
theorem exists_isInvertibleModule_homology_iso_of_isDualizingComplex [IsLocallyNoetherian X]
    [ConnectedSpace X] (K K' : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (hK' : IsDualizingComplex K') :
    ∃ (m : ℤ) (ℒ : X.Modules), Stacks.SheafOfModules.Tensor.IsInvertibleModule X.sheaf ℒ ∧
      ∀ j : ℤ, Nonempty ((DerivedCategory.homologyFunctor X.Modules j).obj K' ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
          ((DerivedCategory.homologyFunctor X.Modules (-m + j)).obj K)).obj ℒ) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_isInvertible_tensor_iso_of_isDualizingComplex K K' hK hK'
  have : ConnectedSpace X.toRingedSpace.carrier := inferInstanceAs (ConnectedSpace X)
  obtain ⟨m, ℒ, hℒ, ⟨eL⟩⟩ :=
    Stacks.Cohomology.InvertibleDerived.exists_isInvertibleModule_iso_singleFunctor
      (X := X.toRingedSpace) (fun x => (inferInstance : IsLocalRing (X.presheaf.stalk x))) L hL
  let := Scheme.Modules.derivedMonoidal X
  exact ⟨m, ℒ, hℒ, fun j => ⟨(DerivedCategory.homologyFunctor X.Modules j).mapIso
    (e ≪≫ MonoidalCategory.whiskerLeftIso K eL) ≪≫ homologyTensorSingleIso K ℒ hℒ m j⟩⟩

end Twist

section Uniqueness

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The cohomology of `K` in a model of `D(𝒪_X)` is the cohomology of the same complex in the
standard model. -/
def homologyIsoStandard [h : HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules)
    (i : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules i).obj K ≅
      (@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) i).obj
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj
          (DerivedCategory.Q.objPreimage K)) :=
  (DerivedCategory.homologyFunctor X.Modules i).mapIso
      (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    (DerivedCategory.homologyFunctorFactors X.Modules i).app _ ≪≫
    ((@DerivedCategory.homologyFunctorFactors X.Modules _ _ (HasDerivedCategory.standard _)
      i).app _).symm

/-- **A dualizing module is determined by its dualizing complex**: two dualizing modules of the
same complex are realized in the same degree and are equal. -/
theorem IsDualizingModuleOf.unique [HasDerivedCategory.{w} X.Modules] {ω ω' : X.Modules}
    {K : DerivedCategory X.Modules} {n n' : ℤ} (h : IsDualizingModuleOf ω K n)
    (h' : IsDualizingModuleOf ω' K n') : n = n' ∧ ω = ω' := by
  have hn : n = n' := by
    rcases lt_trichotomy n n' with hlt | heq | hgt
    · exact absurd (h'.isZero_of_lt n hlt) h.nonzero
    · exact heq
    · exact absurd (h.isZero_of_lt n' hgt) h'.nonzero
  exact ⟨hn, by rw [h.eq_homology, h'.eq_homology, hn]⟩

/-- A shift of a dualizing complex on a locally Noetherian scheme is a dualizing complex, for any
model of the derived category. `Stacks.Duality.isDualizingComplex_shift` is the same statement at
`HasDerivedCategory.standard`. -/
theorem IsDualizingComplex.shift [HasDerivedCategory.{w} X.Modules]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) (k : ℤ) :
    IsDualizingComplex (K⟦k⟧) := by
  intro U hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, ⟨e⟩⟩ := hK U hU
  exact ⟨ω⟦k⟧, Dualizing.isDualizingComplex_shift ω hω k,
    ⟨((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.commShiftIso k).app K ≪≫
      (shiftFunctor _ k).mapIso e ≪≫
      (((tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom)
        |>.mapDerivedCategory.commShiftIso k).app ω).symm⟩⟩

/-- **Stacks Project, Tag 0AWH.** The dualizing complex is not unique. If `ω` is a dualizing
module of the dualizing complex `K`, realized in degree `n`, then for every integer `k` the
shifted complex `K⟦k⟧` is again a dualizing complex, its dualizing module is realized in degree
`n - k` and is isomorphic to `ω`, and for `k ≠ 0` the complex `K⟦k⟧` is not isomorphic to `K`. -/
@[stacks 0AWH "the first half of the section's second warning: the dualizing complex is not \
unique. A shift of a dualizing complex is a dualizing complex, not isomorphic to it for a nonzero \
shift, with the same dualizing module in the shifted degree"]
theorem IsDualizingModuleOf.shift [HasDerivedCategory.{w} X.Modules] {ω : X.Modules}
    {K : DerivedCategory X.Modules} {n : ℤ} (h : IsDualizingModuleOf ω K n) (k : ℤ) :
    IsDualizingModuleOf ((DerivedCategory.homologyFunctor X.Modules (n - k)).obj (K⟦k⟧))
        (K⟦k⟧) (n - k) ∧
      Nonempty ((DerivedCategory.homologyFunctor X.Modules (n - k)).obj (K⟦k⟧) ≅ ω) ∧
      (k ≠ 0 → IsEmpty (K⟦k⟧ ≅ K)) := by
  have e : ∀ i : ℤ, (DerivedCategory.homologyFunctor X.Modules i).obj (K⟦k⟧) ≅
      (DerivedCategory.homologyFunctor X.Modules (k + i)).obj K := fun i =>
    ((DerivedCategory.homologyFunctor X.Modules 0).shiftIso k i (k + i) rfl).app K
  have hd : IsDualizingModuleOf ((DerivedCategory.homologyFunctor X.Modules (n - k)).obj (K⟦k⟧))
      (K⟦k⟧) (n - k) :=
    { isDualizingComplex := h.isDualizingComplex.shift k
      nonzero := fun hz => h.nonzero
        ((hz.of_iso (e (n - k)).symm).of_iso (eqToIso (by congr 2; ring)))
      isZero_of_lt := fun i hi => (h.isZero_of_lt (k + i) (by omega)).of_iso (e i)
      eq_homology := rfl }
  refine ⟨hd, ⟨e (n - k) ≪≫ eqToIso (by rw [h.eq_homology]; congr 2; ring)⟩,
    fun hk => ⟨fun f => ?_⟩⟩
  have hK : IsDualizingModuleOf ((DerivedCategory.homologyFunctor X.Modules (n - k)).obj K) K
      (n - k) :=
    { isDualizingComplex := h.isDualizingComplex
      nonzero := fun hz => hd.nonzero (hz.of_iso ((DerivedCategory.homologyFunctor X.Modules
        (n - k)).mapIso f))
      isZero_of_lt := fun i hi => (hd.isZero_of_lt i hi).of_iso
        ((DerivedCategory.homologyFunctor X.Modules i).mapIso f.symm)
      eq_homology := rfl }
  have := (h.unique hK).1
  exact hk (by omega)

/-- **Stacks Project, Tag 0AWH.** On a connected locally Noetherian scheme the dualizing module
is unique up to tensoring by an invertible module: if `ω` is a dualizing module of the dualizing
complex `K` and `ω'` one of the dualizing complex `K'`, there is an invertible `𝒪_X`-module `ℒ`
with `ω' ≅ ω ⊗_{𝒪_X} ℒ`. -/
@[stacks 0AWH "the second half of the section's second warning: the dualizing module is unique \
up to tensoring by an invertible module. Stated for a connected locally Noetherian scheme: on a \
disconnected one two dualizing complexes can shift by different amounts on different components \
and their dualizing modules then need not differ by a twist (counterexample Spec k disjoint union \
Spec k in the module documentation). The relation between the two complexes is proved, from Tag \
0ATP and Tag 0FPG, not assumed"]
theorem IsDualizingModuleOf.exists_isInvertibleModule_iso_sheafTensor [ConnectedSpace X]
    [HasDerivedCategory.{w} X.Modules] {ω ω' : X.Modules} {K K' : DerivedCategory X.Modules}
    {n n' : ℤ} (h : IsDualizingModuleOf ω K n) (h' : IsDualizingModuleOf ω' K' n') :
    ∃ ℒ : X.Modules, Stacks.SheafOfModules.Tensor.IsInvertibleModule X.sheaf ℒ ∧
      Nonempty (ω' ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj ω).obj ℒ) := by
  have hd : ∀ {K : DerivedCategory X.Modules}, IsDualizingComplex K →
      @IsDualizingComplex X _ (HasDerivedCategory.standard _)
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj
        (DerivedCategory.Q.objPreimage K)) := fun {K} hK =>
    isDualizingComplex_Q_of_isDualizingComplex_Q _ (HasDerivedCategory.standard _) _
      (isDualizingComplex_of_iso (DerivedCategory.Q.objObjPreimageIso K).symm hK)
  obtain ⟨m, ℒ, hℒ, hiso⟩ :=
    exists_isInvertibleModule_homology_iso_of_isDualizingComplex _ _
      (hd h.isDualizingComplex) (hd h'.isDualizingComplex)
  have key : ∀ j : ℤ, Nonempty ((DerivedCategory.homologyFunctor X.Modules j).obj K' ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
        ((DerivedCategory.homologyFunctor X.Modules (-m + j)).obj K)).obj ℒ) := fun j =>
    ⟨homologyIsoStandard K' j ≪≫ (hiso j).some ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).mapIso
        (homologyIsoStandard K (-m + j)).symm).app ℒ⟩
  have hz : ∀ j : ℤ, IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj K') ↔
      IsZero ((DerivedCategory.homologyFunctor X.Modules (-m + j)).obj K) := fun j =>
    ((key j).some.isZero_iff).trans (isZero_sheafTensor_obj_obj_iff _ ℒ hℒ)
  have hge : n ≤ -m + n' := by
    by_contra hlt
    exact h'.nonzero ((hz n').mpr (h.isZero_of_lt _ (by omega)))
  have hle : n' ≤ n + m := by
    by_contra hlt
    refine h.nonzero ?_
    have := (hz (n + m)).mp (h'.isZero_of_lt _ (by omega))
    rwa [show -m + (n + m) = n by ring] at this
  have hdeg : -m + n' = n := by omega
  exact ⟨ℒ, hℒ, ⟨eqToIso h'.eq_homology ≪≫ (key n').some ≪≫
    eqToIso (by rw [hdeg, h.eq_homology])⟩⟩

end Uniqueness

end Stacks.Duality

end
