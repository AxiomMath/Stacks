module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModuleCoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# Twisting by invertible modules on an algebraic space is exact

Let `X` be an algebraic space and `L` an invertible `𝒪_X`-module.  For every integer `m` the
functor `M ↦ M ⊗ L^{⊗ m}` on `𝒪_X`-modules is an equivalence of categories, tensoring with
`L^{⊗ (-m)}` being an inverse (Stacks 01CU); hence it is exact.  So is the composite twist
`M ↦ M ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r}` by a finite family, and so is that twist followed by the
universe lift of the sections, which is the module whose Euler characteristic
`AlgebraicGeometry.Space.eulerCharacteristic` takes.  A short exact sequence of `𝒪_X`-modules
therefore stays short exact after twisting.

## Main definitions

* `AlgebraicGeometry.Space.twistStepEquivalenceFunctor`: the functor `M ↦ M ⊗ L^{⊗ m}`, whose
  value is `AlgebraicGeometry.Space.twistStep`.
* `AlgebraicGeometry.Space.twistedModuleExactFunctor`: the functor
  `M ↦ M ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r}`, whose value is `AlgebraicGeometry.Space.twistedModule`.
* `AlgebraicGeometry.Space.twistedModuleUliftExactFunctor`: the same followed by the universe
  lift of the sections, whose value is `AlgebraicGeometry.Space.twistedModuleUlift`.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_twistStepEquivalenceFunctor` and
  `AlgebraicGeometry.Space.isEquivalence_twistedModuleExactFunctor`: both twists are
  autoequivalences.
* `AlgebraicGeometry.Space.shortExact_map_twistedModuleUliftExactFunctor`: twisting followed by
  the universe lift carries short exact sequences to short exact sequences.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0DN2](https://stacks.math.columbia.edu/tag/0DN2)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The integer tensor power `L^{⊗ m}` of an invertible module is invertible, in the sense of
`AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
private theorem isInvertible_twistPower (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property L]
    (m : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property
      (@Stacks.SheafOfModules.Invertible.tensorPower.{u, u + 1, u}
        (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
        (structurePresheaf B S hS F)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ L
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) m) :=
  let := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL
  Stacks.SheafOfModules.Invertible.tensorPower_isInvertible _ _ L m

/-- Tensoring with the integer power `L^{⊗ m}` of an invertible module, as a functor; its value
at `M` is `AlgebraicGeometry.Space.twistStep`. -/
def twistStepEquivalenceFunctor (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property L]
    (m : ℤ) : Modules.{u, u} B S hS F hF ⥤ Modules.{u, u} B S hS F hF :=
  (Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS F hF).O).flip.obj
    (@Stacks.SheafOfModules.Invertible.tensorPower.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) m)

/-- The value of `AlgebraicGeometry.Space.twistStepEquivalenceFunctor` is the twisting step. -/
theorem twistStepEquivalenceFunctor_obj (L : Modules.{u, u} B S hS F hF)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property L]
    (m : ℤ) (M : Modules.{u, u} B S hS F hF) :
    (twistStepEquivalenceFunctor B S hS F hF L m).obj M = twistStep B S hS F hF L m M :=
  rfl

/-- Tensoring with an integer power of an invertible module is an autoequivalence
(Stacks 01CU). -/
instance isEquivalence_twistStepEquivalenceFunctor (L : Modules.{u, u} B S hS F hF)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property L]
    (m : ℤ) : (twistStepEquivalenceFunctor B S hS F hF L m).IsEquivalence :=
  @Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible.{u, u + 1, u}
    (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
    (structurePresheaf B S hS F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ _
    (isInvertible_twistPower B S hS F hF L m)

/-- The composite of the functors `T j` along a list, read on an object: the iterated values. -/
private theorem foldl_comp_functor_obj {C : Type*} [Category* C] {ι : Type*} (T : ι → C ⥤ C) :
    ∀ (l : List ι) (G : C ⥤ C) (M : C),
      (l.foldl (fun G j => G ⋙ T j) G).obj M = l.foldl (fun N j => (T j).obj N) (G.obj M)
  | [], _, _ => rfl
  | j :: l, G, M => foldl_comp_functor_obj T l (G ⋙ T j) M

/-- The composite along a list of autoequivalences, starting from an autoequivalence, is an
autoequivalence. -/
private theorem foldl_comp_functor_isEquivalence {C : Type*} [Category* C] {ι : Type*}
    (T : ι → C ⥤ C) [∀ j, (T j).IsEquivalence] :
    ∀ (l : List ι) (G : C ⥤ C), G.IsEquivalence →
      (l.foldl (fun G j => G ⋙ T j) G).IsEquivalence
  | [], _, hG => hG
  | j :: l, G, _ => foldl_comp_functor_isEquivalence T l (G ⋙ T j) inferInstance

/-- Twisting by a finite family of integer powers of invertible modules, as a functor: the
composite of the twisting steps in the order of `Fin r`, as in
`AlgebraicGeometry.Space.twistedModule`. -/
def twistedModuleExactFunctor {r : ℕ} (L : Fin r → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin r → ℤ) : Modules.{u, u} B S hS F hF ⥤ Modules.{u, u} B S hS F hF :=
  (List.finRange r).foldl (fun G j => G ⋙ twistStepEquivalenceFunctor B S hS F hF (L j) (n j))
    (𝟭 _)

/-- The value of `AlgebraicGeometry.Space.twistedModuleExactFunctor` is
`AlgebraicGeometry.Space.twistedModule`. -/
theorem twistedModuleExactFunctor_obj {r : ℕ} (L : Fin r → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin r → ℤ) (M : Modules.{u, u} B S hS F hF) :
    (twistedModuleExactFunctor B S hS F hF L n).obj M = twistedModule B S hS F hF M L n :=
  foldl_comp_functor_obj _ _ _ M

/-- Twisting by a finite family of invertible modules is an autoequivalence. -/
instance isEquivalence_twistedModuleExactFunctor {r : ℕ} (L : Fin r → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin r → ℤ) : (twistedModuleExactFunctor B S hS F hF L n).IsEquivalence :=
  foldl_comp_functor_isEquivalence _ _ _ inferInstance

/-- Twisting by a finite family followed by the universe lift of the sections, as a functor; its
value is `AlgebraicGeometry.Space.twistedModuleUlift`. -/
def twistedModuleUliftExactFunctor {r : ℕ} (L : Fin r → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin r → ℤ) : Modules.{u, u} B S hS F hF ⥤ Modules.{u, max (u + 1) w} B S hS F hF :=
  twistedModuleExactFunctor B S hS F hF L n ⋙
    SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, max (u + 1) w}

/-- Twisting followed by the universe lift preserves zero morphisms. -/
instance preservesZeroMorphisms_twistedModuleUliftExactFunctor {r : ℕ}
    (L : Fin r → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin r → ℤ) :
    (twistedModuleUliftExactFunctor.{u, w} B S hS F hF L n).PreservesZeroMorphisms :=
  have : PreservesFiniteLimits (twistedModuleUliftExactFunctor.{u, w} B S hS F hF L n) :=
    comp_preservesFiniteLimits _ _
  inferInstance

/-- The value of `AlgebraicGeometry.Space.twistedModuleUliftExactFunctor` is
`AlgebraicGeometry.Space.twistedModuleUlift`. -/
theorem twistedModuleUliftExactFunctor_obj {r : ℕ} (L : Fin r → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin r → ℤ) (M : Modules.{u, u} B S hS F hF) :
    (twistedModuleUliftExactFunctor.{u, w} B S hS F hF L n).obj M =
      twistedModuleUlift.{u, w} B S hS F hF M L n :=
  congrArg (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w})
    (twistedModuleExactFunctor_obj B S hS F hF L n M)

/-- Twisting followed by the universe lift is exact: it carries a short exact sequence of
`𝒪_X`-modules to a short exact sequence. -/
theorem shortExact_map_twistedModuleUliftExactFunctor {r : ℕ}
    (L : Fin r → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin r → ℤ) {Sc : ShortComplex (Modules.{u, u} B S hS F hF)} (hSc : Sc.ShortExact) :
    (Sc.map (twistedModuleUliftExactFunctor.{u, w} B S hS F hF L n)).ShortExact := by
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
  have : PreservesFiniteLimits (twistedModuleUliftExactFunctor.{u, w} B S hS F hF L n) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (twistedModuleUliftExactFunctor.{u, w} B S hS F hF L n) :=
    comp_preservesFiniteColimits _ _
  exact hSc.map_of_exact _

end AlgebraicGeometry.Space

end
