module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Limits.Shapes.CombinedProducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitSections
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits

/-!
# Existence of the unbounded left derived lower-shriek functor

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `O_D` be a sheaf of rings
on `D` and let `O_C = g^{-1} O_D` be its restriction along `u`. The lower-shriek functor
`g_! : Mod(O_C) ⥤ Mod(O_D)` is Mathlib's `SheafOfModules.pullback` for the identity map of
`O_C`, the left adjoint of restriction of modules. Stacks 07AC asserts that `g_!` has an
unbounded left derived functor `Lg_! : D(O_C) ⥤ D(O_D)`.

Here `Lg_!` is shown to exist, by the criterion
`CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex` of
[Stacks, Tag 0794] with `P` the class of direct sums of the extensions by zero `j_{U!} O_U` of
the structure sheaves of the slice sites, under the hypothesis that `g_!` carries a bounded above
acyclic complex with terms in `P` to an acyclic complex.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnit`: `j_{U!} O_U`, the extension by
  zero of the structure sheaf of the site localized at an object.
* `Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnits`: the class `P` of direct
  sums of the `j_{U!} O_U`.
* `Stacks.Cohomology.DerivedLowerShriek.inverseImageRing`: `O_C = g^{-1} O_D`.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.exists_epi_isSumOfExtensionByZeroUnits`: every sheaf of
  modules is a quotient of a direct sum of extensions by zero of the structure sheaves of the
  slices, i.e. `P` generates.
* `Stacks.Cohomology.DerivedLowerShriek.isSumOfExtensionByZeroUnits_biprod` and the
  `ObjectProperty.ContainsZero` instance: `P` contains a zero object and is closed under binary
  direct sums.
* `Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedLowerShriek_of_acyclic`: `g_!` has
  an unbounded left derived functor, under the acyclicity hypothesis above.
* `Stacks.Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat`,
  `Stacks.Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat_presheafOfModules` and
  `Stacks.Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat_addCommGrpCat`:
  `ℕ`-indexed colimits are exact in sheaves of modules, in presheaves of modules, and in
  abelian groups, for a site and a sections universe that are unrelated.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek

/-- `ℕ`-indexed colimits of abelian groups are exact. -/
theorem hasExactColimitsOfShape_nat_addCommGrpCat :
    HasExactColimitsOfShape ℕ AddCommGrpCat.{w} :=
  have : AB5OfSize.{0, 0} AddCommGrpCat.{w} := AB5OfSize_shrink _
  AB5OfSize.ofShape ℕ

/-- `ℕ`-indexed colimits of presheaves of modules are exact. -/
theorem hasExactColimitsOfShape_nat_presheafOfModules {C : Type u₁} [Category.{v₁} C]
    (S : Cᵒᵖ ⥤ RingCat.{w}) : HasExactColimitsOfShape ℕ (PresheafOfModules.{w} S) :=
  have := hasExactColimitsOfShape_nat_addCommGrpCat.{w}
  ⟨⟨fun _ _ _ => ⟨fun {F} =>
    have : PreservesLimit F (colim (J := ℕ) ⋙ PresheafOfModules.toPresheaf S) :=
      preservesLimit_of_natIso _ (preservesColimitNatIso (PresheafOfModules.toPresheaf S)).symm
    preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf S)⟩⟩⟩

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).IsRightAdjoint]

/- Instance search for coproducts of sheaves of modules times out since the Lean v4.35.0 bump;
these local instances give the direct route. -/
local instance (priority := high) hasColimitsOfShape_discrete_presheafOfModules (K : Type w) :
    HasColimitsOfShape (Discrete K) (PresheafOfModules.{w} R.obj) :=
  PresheafOfModules.hasColimitsOfShape R.obj (Discrete K)

local instance (priority := high) hasCoproducts_sheafOfModules :
    HasCoproducts.{w} (SheafOfModules.{w} R) := fun K =>
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf R
    (Discrete K)

/-- `j_{U!} O_U`. -/
abbrev extensionByZeroUnit (U : C) : SheafOfModules.{w} R :=
  (SheafOfModules.pullback.{w} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj (SheafOfModules.unit (R.over U))

/-- The class of direct sums of `j_{U!} O_U`. -/
def IsSumOfExtensionByZeroUnits : ObjectProperty (SheafOfModules.{w} R) := fun M =>
  ∃ (ι : Type w) (U : ι → C), Nonempty ((∐ fun i : ι => extensionByZeroUnit R (U i)) ≅ M)

/-- The class of direct sums of extensions by zero of the structure sheaves of the slices
contains a zero object. -/
instance containsZero_isSumOfExtensionByZeroUnits :
    (IsSumOfExtensionByZeroUnits R).ContainsZero := by
  let U₀ : PEmpty.{w + 1} → C := fun i => nomatch i
  let E : PEmpty.{w + 1} → SheafOfModules.{w} R := fun i => extensionByZeroUnit R (U₀ i)
  exact ⟨∐ E, (IsInitial.ofUniqueHom (fun Y => Sigma.desc (fun i => isEmptyElim i))
    (fun Y m => Sigma.hom_ext _ _ (fun i => isEmptyElim i))).isZero,
    ⟨PEmpty.{w + 1}, U₀, ⟨Iso.refl _⟩⟩⟩

/-- The class of direct sums of extensions by zero of the structure sheaves of the slices is
closed under binary direct sums. -/
lemma isSumOfExtensionByZeroUnits_biprod {M N : SheafOfModules.{w} R}
    (hM : IsSumOfExtensionByZeroUnits R M) (hN : IsSumOfExtensionByZeroUnits R N) :
    IsSumOfExtensionByZeroUnits R (M ⊞ N) := by
  obtain ⟨ι, U, ⟨eM⟩⟩ := hM
  obtain ⟨κ, V, ⟨eN⟩⟩ := hN
  refine ⟨ι ⊕ κ, Sum.elim U V, ?_⟩
  let F : ι → SheafOfModules.{w} R := fun i => extensionByZeroUnit R (U i)
  let H : κ → SheafOfModules.{w} R := fun j => extensionByZeroUnit R (V j)
  have hFH : (fun i : ι ⊕ κ => extensionByZeroUnit R (Sum.elim U V i)) = Sum.elim F H := by
    funext i
    cases i <;> rfl
  let e : Discrete.functor (fun i : ι ⊕ κ => extensionByZeroUnit R (Sum.elim U V i)) ≅
      Discrete.functor (Sum.elim F H) :=
    Discrete.natIso fun i => eqToIso (congrFun hFH i.as)
  exact ⟨HasColimit.isoOfNatIso e ≪≫
    (coproductIsCoproduct (Sum.elim F H)).coconePointUniqueUpToIso
      (Cofan.combPairIsColimit (coproductIsCoproduct F) (coproductIsCoproduct H)
        (coprodIsCoprod (∐ F) (∐ H))) ≪≫
    (biprod.isoCoprod (∐ F) (∐ H)).symm ≪≫ biprod.mapIso eM eN⟩

/-- For an arbitrary sheaf of rings on a site, every sheaf of modules receives an epimorphism from
a direct sum of extensions by zero of the structure sheaves of the slices. -/
theorem exists_epi_isSumOfExtensionByZeroUnits [Small.{w} C] (M : SheafOfModules.{w} R) :
    ∃ (N : SheafOfModules.{w} R) (_ : IsSumOfExtensionByZeroUnits R N) (p : N ⟶ M), Epi p := by
  classical
  let σ : Type max u₁ w := Σ V : C, (M.val.obj (op V) : Type w)
  let ι : Type w := Shrink.{w} σ
  let ev : ι ≃ σ := (equivShrink σ).symm
  let U : ι → C := fun i => (ev i).1
  refine ⟨∐ fun i : ι => extensionByZeroUnit R (U i), ⟨ι, U, ⟨Iso.refl _⟩⟩,
    Sigma.desc fun i =>
      (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R (U i) M).symm (ev i).2, ⟨?_⟩⟩
  intro N f g h
  have key (i : ι) :
      f.val.app (op (ev i).1) (ev i).2 = g.val.app (op (ev i).1) (ev i).2 := by
    have hh := congrArg (fun k => Sigma.ι
      (fun i : ι => extensionByZeroUnit R (U i)) i ≫ k) h
    simp only [← Category.assoc, Sigma.ι_comp_desc] at hh
    have he := congrArg
      (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R (U i) N) hh
    rwa [Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality,
      Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality,
      Equiv.apply_symm_apply] at he
  have hs (s : σ) : f.val.app (op s.1) s.2 = g.val.app (op s.1) s.2 := by
    have := key (ev.symm s)
    rwa [ev.apply_symm_apply] at this
  refine (SheafOfModules.toSheaf R).map_injective
    (Sheaf.hom_ext (NatTrans.ext (funext fun Y => ?_)))
  ext x
  exact hs ⟨Y.unop, x⟩

section LowerShriek

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{w})

/-- `O_C = g^{-1} O_D`: the restriction of the structure sheaf of the target site along the
functor of sites. -/
abbrev inverseImageRing : Sheaf J RingCat.{w} :=
  (f.sheafPushforwardContinuous RingCat.{w} J K).obj O

/-- The identity map of `g^{-1} O_D`. -/
abbrev idRingMap : inverseImageRing J K f O ⟶ inverseImageRing J K f O := 𝟙 _

/-- On a small site, restriction of presheaves of modules along the functor of sites, with
structure map `idRingMap`, has a left adjoint. -/
instance isRightAdjoint_presheafPushforward {C D : Type u₁} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D) [f.IsContinuous J K]
    (O : Sheaf K RingCat.{u₁}) :
    (PresheafOfModules.pushforward.{u₁} (F := f) (idRingMap J K f O).hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

/-- On a small site, restriction of sheaves of modules along the functor of sites has a left
adjoint, namely the lower-shriek functor. -/
instance isRightAdjoint_pushforward {C D : Type u₁} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D) [f.IsContinuous J K]
    (O : Sheaf K RingCat.{u₁}) :
    (SheafOfModules.pushforward.{u₁} (F := f) (idRingMap J K f O)).IsRightAdjoint :=
  SheafOfModules.instIsRightAdjointPushforward _

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := f) (idRingMap J K f O)).IsRightAdjoint]

/-- The lower-shriek functor is additive. -/
instance additive_lowerShriek :
    (SheafOfModules.pullback.{w} (idRingMap J K f O)).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (SheafOfModules.pullback.{w} (idRingMap J K f O))
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Colimits of `ℕ`-indexed systems of sheaves of modules are exact. -/
lemma hasExactColimitsOfShape_nat {E : Type u₁} [Category.{v₁} E]
    {L : GrothendieckTopology E} (T : Sheaf L RingCat.{w})
    [HasWeakSheafify L AddCommGrpCat.{w}] [L.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify L AddCommGrpCat.{w}] :
    HasExactColimitsOfShape ℕ (SheafOfModules.{w} T) :=
  have := hasExactColimitsOfShape_nat_presheafOfModules (C := E) T.obj
  (PresheafOfModules.sheafificationAdjunction (𝟙 T.obj)).hasExactColimitsOfShape ℕ

end LowerShriek

section CardStatement

attribute [local instance] HasDerivedCategory.standard

/-- If the lower-shriek functor carries every bounded above acyclic complex whose terms are direct
sums of extensions by zero of the structure sheaves of the slices to an acyclic complex, then it
has an unbounded left derived functor. -/
theorem hasPointwiseLeftDerivedLowerShriek_of_acyclic
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (O : Sheaf K RingCat.{w})
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}] [Small.{w} C]
    [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
      (𝟙 ((inverseImageRing J K f O).over U) :
        (inverseImageRing J K f O).over U ⟶ (inverseImageRing J K f O).over U)).IsRightAdjoint]
    [(SheafOfModules.pushforward.{w} (F := f) (idRingMap J K f O)).IsRightAdjoint]
    (hFP : ∀ (a : ℤ) (L : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f O)) ℤ),
      L.IsStrictlyLE a →
      (∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) (L.X n)) → L.Acyclic →
      (((SheafOfModules.pullback.{w} (idRingMap J K f O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).Acyclic) :
    let S := (f.sheafPushforwardContinuous RingCat.{w} J K).obj O
    let φ : S ⟶ S := 𝟙 S
    let F := SheafOfModules.pullback.{w} φ
    let : F.Additive := by
      let _ := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
      exact Functor.additive_of_preservesBinaryBiproducts F
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} S) (ComplexShape.up ℤ)) := by
  intro S φ F _
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{w} S) := hasExactColimitsOfShape_nat _
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{w} O) := hasExactColimitsOfShape_nat _
  exact CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex F
    (IsSumOfExtensionByZeroUnits S) (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
    (exists_epi_isSumOfExtensionByZeroUnits _) hFP

end CardStatement

end Stacks.Cohomology.DerivedLowerShriek

end
