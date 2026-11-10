module

public import StacksFrontier.AlgebraicGeometry.Quot.InvertibleTwistPowerEuler
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Twisting by invertible modules is exact, and additivity of twisted Euler characteristics

Let `X` be an algebraic space and `L` an invertible `𝒪_X`-module. Tensoring with an integer
power `L^{⊗ m}` is an autoequivalence of the category of `𝒪_X`-modules (Tag 01CU), hence an exact
functor; so is twisting by a finite family `L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r}`, and so is the universe
lift of the module sections that the Euler characteristic is taken after. A short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of `𝒪_X`-modules therefore stays short exact after twisting.

On a proper algebraic space over a field this gives the additivity of the twisted Euler
characteristics, `χ(X, F₂ ⊗ L^{⊗ n}) = χ(X, F₁ ⊗ L^{⊗ n}) + χ(X, F₃ ⊗ L^{⊗ n})`, under the
hypotheses that the cohomology of the twisted outer modules is finite dimensional over `k` and
vanishes in large degrees.

## Main definitions

* `AlgebraicGeometry.Space.twistFunctor`: the functor `M ↦ M ⊗ L^{⊗ m}`.
* `AlgebraicGeometry.Space.twistedModuleFunctor`: the functor
  `M ↦ M ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r}`.

## Main results

* `AlgebraicGeometry.Space.twistFunctor_obj`: its value is the twisting step
  `AlgebraicGeometry.Space.twistStep`.
* `AlgebraicGeometry.Space.twistedModuleFunctor_obj`: its value is
  `AlgebraicGeometry.Space.twistedModule`.
* `AlgebraicGeometry.Space.shortExact_map_twistedModuleFunctor` and
  `AlgebraicGeometry.Space.shortExact_map_twistedModuleUliftFunctor`: twisting, with or without
  the universe lift, preserves short exact sequences.
* `AlgebraicGeometry.Space.hasAdditiveTwistedEuler_of_shortExact`: additivity of the twisted
  Euler characteristics along a short exact sequence.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0DN2](https://stacks.math.columbia.edu/tag/0DN2)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace AlgebraicGeometry.Space

section Twist

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Tensoring with the integer power `L^{⊗ m}` of an invertible module, as a functor. -/
def twistFunctor (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property L]
    (m : ℤ) : Modules.{u, u} B S hS F hF ⥤ Modules.{u, u} B S hS F hF :=
  (Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS F hF).O).flip.obj
    (invertibleTensorPower B S hS F hF L m)

/-- The value of `AlgebraicGeometry.Space.twistFunctor` is the twisting step. -/
theorem twistFunctor_obj (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property L]
    (m : ℤ) (M : Modules.{u, u} B S hS F hF) :
    (twistFunctor B S hS F hF L m).obj M = twistStep B S hS F hF L m M :=
  rfl

/-- Tensoring with an integer power of an invertible module is an autoequivalence. -/
instance isEquivalence_twistFunctor (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property L]
    (m : ℤ) : (twistFunctor B S hS F hF L m).IsEquivalence :=
  @Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible.{u, u + 1, u}
    (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
    (structurePresheaf B S hS F)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property _ _
    (invertibleTensorPower B S hS F hF L m)
    (isInvertible_invertibleTensorPower B S hS F hF L m)

/-- Twisting by a finite family of integer powers of invertible modules, as a functor: the
composite of the twisting functors, in the order of `Fin d`. -/
def twistedModuleFunctor {d : ℕ} (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) : Modules.{u, u} B S hS F hF ⥤ Modules.{u, u} B S hS F hF :=
  (List.finRange d).foldl (fun G j => G ⋙ twistFunctor B S hS F hF (L j) (n j)) (𝟭 _)

private theorem foldl_comp_obj {C : Type*} [Category C] {ι : Type*} (T : ι → C ⥤ C) :
    ∀ (l : List ι) (G : C ⥤ C) (M : C),
      (l.foldl (fun G j => G ⋙ T j) G).obj M = l.foldl (fun N j => (T j).obj N) (G.obj M)
  | [], _, _ => rfl
  | j :: l, G, M => foldl_comp_obj T l (G ⋙ T j) M

private theorem foldl_comp_isEquivalence {C : Type*} [Category C] {ι : Type*} (T : ι → C ⥤ C)
    [∀ j, (T j).IsEquivalence] :
    ∀ (l : List ι) (G : C ⥤ C), G.IsEquivalence →
      (l.foldl (fun G j => G ⋙ T j) G).IsEquivalence
  | [], _, hG => hG
  | j :: l, G, _ => foldl_comp_isEquivalence T l (G ⋙ T j) inferInstance

/-- The value of `AlgebraicGeometry.Space.twistedModuleFunctor` is the twist
`AlgebraicGeometry.Space.twistedModule`. -/
theorem twistedModuleFunctor_obj {d : ℕ} (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) (M : Modules.{u, u} B S hS F hF) :
    (twistedModuleFunctor B S hS F hF L n).obj M = twistedModule B S hS F hF M L n :=
  foldl_comp_obj _ _ _ M

/-- Twisting by a finite family of integer powers of invertible modules is an
autoequivalence. -/
instance isEquivalence_twistedModuleFunctor {d : ℕ} (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) : (twistedModuleFunctor B S hS F hF L n).IsEquivalence :=
  foldl_comp_isEquivalence _ _ _ inferInstance

/-- **Twisting by invertible modules is exact**: it carries a short exact sequence of
`𝒪_X`-modules to a short exact sequence. -/
theorem shortExact_map_twistedModuleFunctor {d : ℕ} (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) {Sc : ShortComplex (Modules.{u, u} B S hS F hF)} (hSc : Sc.ShortExact) :
    (Sc.map (twistedModuleFunctor B S hS F hF L n)).ShortExact :=
  hSc.map_of_exact _

/-- Twisting by invertible modules followed by the universe lift of the module sections. -/
def twistedModuleUliftFunctor {d : ℕ} (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) : Modules.{u, u} B S hS F hF ⥤ Modules.{u, max (u + 1) w} B S hS F hF :=
  twistedModuleFunctor B S hS F hF L n ⋙
    SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, max (u + 1) w}

/-- Twisting followed by the universe lift preserves zero morphisms. -/
instance preservesZeroMorphisms_twistedModuleUliftFunctor {d : ℕ}
    (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) : (twistedModuleUliftFunctor.{u, w} B S hS F hF L n).PreservesZeroMorphisms :=
  have : (twistedModuleFunctor B S hS F hF L n).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  Functor.preservesZeroMorphisms_comp _ _

/-- The value of `AlgebraicGeometry.Space.twistedModuleUliftFunctor` is
`AlgebraicGeometry.Space.twistedModuleUlift`. -/
theorem twistedModuleUliftFunctor_obj {d : ℕ} (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) (M : Modules.{u, u} B S hS F hF) :
    (twistedModuleUliftFunctor.{u, w} B S hS F hF L n).obj M =
      twistedModuleUlift.{u, w} B S hS F hF M L n := by
  change SheafOfModules.uliftForPresentation _ = SheafOfModules.uliftForPresentation _
  rw [twistedModuleFunctor_obj]

/-- **Twisting by invertible modules followed by the universe lift is exact.** -/
theorem shortExact_map_twistedModuleUliftFunctor {d : ℕ}
    (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) {Sc : ShortComplex (Modules.{u, u} B S hS F hF)} (hSc : Sc.ShortExact) :
    (Sc.map (twistedModuleUliftFunctor.{u, w} B S hS F hF L n)).ShortExact := by
  have : (smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{u})
  have : HasWeakSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{u})
  have : (smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) w} :=
    moduleWEqualsLocallyBijective.{u, w} B S hS F
  have : HasWeakSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{max (u + 1) w} :=
    moduleHasWeakSheafify.{u, w} B S hS F
  have : PreservesFiniteColimits
      (SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, max (u + 1) w}
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
    SheafOfModules.preservesFiniteColimits_uliftForPresentationFunctor.{u + 1, u, u, u,
      max (u + 1) w}
  have : PreservesFiniteLimits (twistedModuleUliftFunctor.{u, w} B S hS F hF L n) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (twistedModuleUliftFunctor.{u, w} B S hS F hF L n) :=
    comp_preservesFiniteColimits _ _
  exact hSc.map_of_exact _

end Twist

section Euler

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : AlgebraicSpaces B (Spec (.of k)) hk)

/-- **Additivity of the twisted Euler characteristics along a short exact sequence.** Let
`0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of `𝒪_X`-modules on a proper algebraic space
over a field, and `L₁, …, L_r` invertible modules. If the twists of `F₁` and `F₃` have
finite-dimensional cohomology below some degree `N` and vanishing cohomology from `N` on, then
for every integral tuple `n`

`χ(X, F₂ ⊗ L^{⊗ n}) = χ(X, F₁ ⊗ L^{⊗ n}) + χ(X, F₃ ⊗ L^{⊗ n})`. -/
theorem hasAdditiveTwistedEuler_of_shortExact {r : ℕ}
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    {Sc : ShortComplex (Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)} (hSc : Sc.ShortExact)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    [h₁ : ∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 Sc.X₁ L n)]
    [h₂ : ∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 Sc.X₂ L n)]
    [h₃ : ∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 Sc.X₃ L n)]
    (N : (Fin r → ℤ) → ℕ)
    (hfin₁ : ∀ n, ∀ i < N n, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 Sc.X₁ L n) i))
    (hfin₃ : ∀ n, ∀ i < N n, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 Sc.X₃ L n) i))
    (hvan₁ : ∀ n, ∀ i, N n ≤ i → IsZero (cohomologyOverBase.{u, w} k B hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 Sc.X₁ L n) i))
    (hvan₃ : ∀ n, ∀ i, N n ≤ i → IsZero (cohomologyOverBase.{u, w} k B hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 Sc.X₃ L n) i)) :
    HasAdditiveTwistedEuler.{u, w} k B hk X f hf Sc.X₁ Sc.X₂ Sc.X₃ L := by
  intro n
  set G := twistedModuleUliftFunctor.{u, w} B (Spec (.of k)) hk X.1 X.2 L n
  have e : ∀ M, G.obj M = twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M L n :=
    twistedModuleUliftFunctor_obj.{u, w} B (Spec (.of k)) hk X.1 X.2 L n
  have hS' := shortExact_map_twistedModuleUliftFunctor.{u, w} B (Spec (.of k)) hk X.1 X.2 L n hSc
  have c₁ : IsCoherent B (Spec (.of k)) hk X.1 X.2 (Sc.map G).X₁ :=
    isCoherent_of_iso B (Spec (.of k)) hk X.2 (eqToIso (e Sc.X₁)).symm (h₁ n)
  have c₂ : IsCoherent B (Spec (.of k)) hk X.1 X.2 (Sc.map G).X₂ :=
    isCoherent_of_iso B (Spec (.of k)) hk X.2 (eqToIso (e Sc.X₂)).symm (h₂ n)
  have c₃ : IsCoherent B (Spec (.of k)) hk X.1 X.2 (Sc.map G).X₃ :=
    isCoherent_of_iso B (Spec (.of k)) hk X.2 (eqToIso (e Sc.X₃)).symm (h₃ n)
  have I := fun M i => cohomologyOverBaseIso.{u, w} k B hk X.1 X.2 (eqToIso (e M)) i
  have key : eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf (Sc.map G).X₂ =
      eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf (Sc.map G).X₁ +
        eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf (Sc.map G).X₃ := by
    rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum,
      eulerCharacteristic_eq_finsum]
    exact finsum_alternating_finrank_cohomologyOverBase_add_of_shortExact_of_outer.{u, w} k B hk
      X.1 X.2 hS' (N n)
      (fun i hi => have := hfin₁ n i hi
        (I Sc.X₁ i).toLinearEquiv.symm.finiteDimensional)
      (fun i hi => have := hfin₃ n i hi
        (I Sc.X₃ i).toLinearEquiv.symm.finiteDimensional)
      (fun i hi => (hvan₁ n i hi).of_iso (I Sc.X₁ i))
      (fun i hi => (hvan₃ n i hi).of_iso (I Sc.X₃ i))
  have t : ∀ M (_ : IsCoherent B (Spec (.of k)) hk X.1 X.2 (G.obj M))
      [IsCoherent B (Spec (.of k)) hk X.1 X.2
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M L n)],
      eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf (G.obj M) =
        eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M L n) :=
    fun M _ _ => eulerCharacteristic_congr.{u, w} k B hk X.1 X.2 f hf (eqToIso (e M))
  rwa [← t Sc.X₁ c₁, ← t Sc.X₂ c₂, ← t Sc.X₃ c₃]

end Euler

end AlgebraicGeometry.Space

end
