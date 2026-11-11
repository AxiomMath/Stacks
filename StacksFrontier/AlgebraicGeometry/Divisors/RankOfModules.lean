module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalHom
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Ranks of modules on an integral scheme

Let `X` be an integral scheme with generic point `η`. The local ring `𝒪_{X,η}` is the function
field `κ(η)` of `X`, and the *rank* of an `𝒪_X`-module `ℱ` is the dimension `dim_{κ(η)} ℱ_η`
of its stalk at the generic point ([Stacks, Tag 0HAF]). This file proves the basic properties of
this rank listed in [Stacks, Section 0HAE].

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.rank`: the rank of a module on an integral scheme.

## Main results

* `AlgebraicGeometry.Scheme.Modules.rank_tfae`: the rank of a quasi-coherent module can be read
  on the sections over one, or every, nonempty affine open ([Stacks, Tag 0HAG]).
* `AlgebraicGeometry.Scheme.Modules.rank_pullback_of_isDominant`: the rank is invariant under
  pullback along a dominant morphism of integral schemes ([Stacks, Tag 0HAH]).
* `AlgebraicGeometry.Scheme.Modules.rank_of_shortExact`: the rank is additive in short exact
  sequences ([Stacks, Tag 0HAI]).
* `AlgebraicGeometry.Scheme.Modules.rank_tensor_and_rank_sheafHom`: the rank of a tensor
  product, and of a sheaf of homomorphisms out of a module of finite presentation, is the
  product of the ranks ([Stacks, Tag 0HAJ]).
* `AlgebraicGeometry.Scheme.Modules.exists_rank_eq_and_over_iso_free`: a quasi-coherent module
  of finite type has finite rank `r` and is free of rank `r` on a nonempty open
  ([Stacks, Tag 0HAK]).

## Implementation notes

The rank of a module `M` over a domain `R` with fraction field `K` is, following
Stacks, More on Algebra, Definition 15.23.1, the dimension `dim_K (M ⊗_R K)`; it is
written `Module.rank (FractionRing R) (FractionRing R ⊗[R] M)` below and agrees with Mathlib's
`Module.rank R M` (`rank_fractionRing_tensorProduct`).

## References

* [Stacks Project, Section 0HAE](https://stacks.math.columbia.edu/tag/0HAE)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Stacks 0HAF.** The *rank* of an `𝒪_X`-module `ℱ` on an integral scheme `X` with generic
point `η` is `dim_{κ(η)} ℱ_η`, the dimension of the stalk at the generic point over the local
ring there, which is the residue field `κ(η)` (the function field `X.functionField`). Stacks
makes the definition for quasi-coherent `ℱ`; the formula makes sense for every `𝒪_X`-module and
the results below assume quasi-coherence where Stacks does. -/
@[stacks 0HAF]
noncomputable def rank [IsIntegral X] (F : X.Modules) : Cardinal.{u} :=
  Module.rank X.functionField (F.presheaf.stalk (genericPoint X))

/-- For a domain `R` with fraction field `K`, the rank `dim_K (M ⊗_R K)` of an `R`-module `M`
in the sense of More on Algebra, Definition 15.23.1 is Mathlib's `Module.rank R M`. -/
theorem rank_fractionRing_tensorProduct (R : Type u) [CommRing R] [IsDomain R] (M : Type u)
    [AddCommGroup M] [Module R M] :
    Module.rank (FractionRing R) (FractionRing R ⊗[R] M) = Module.rank R M :=
  (TensorProduct.isBaseChange R M (FractionRing R)).rank_eq

/-- The generic point lies in every nonempty open of an irreducible scheme. -/
theorem genericPoint_mem_of_nonempty [IsIntegral X] {U : X.Opens} (hU : Nonempty U) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- On a nonempty affine open `U` of an integral scheme, the rank of a quasi-coherent module `ℱ`
is the rank of the `𝒪_X(U)`-module `ℱ(U)`: the germ map `ℱ(U) → ℱ_η` is the localization at
all nonzero elements of the domain `𝒪_X(U)`, whose fraction field is `κ(η)`. -/
theorem rank_eq_rank_sections [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) [hne : Nonempty U] :
    F.rank = Module.rank Γ(X, U) Γ(F, U) := by
  have hη : genericPoint X ∈ U := genericPoint_mem_of_nonempty hne
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule F hη
  have hloc := Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ F hU hη
  have hp : (hU.primeIdealOf ⟨genericPoint X, hη⟩).asIdeal = ⊥ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  have h2 := Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_of_eq hp hloc
  have h3 : IsLocalizedModule ((⊥ : Ideal Γ(X, U)).primeCompl)
      (Stacks.ModuleStalkSpecialization.germₗ F hη) := h2
  rw [Ideal.primeCompl_bot] at h3
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsScalarTower Γ(X, U) X.functionField (F.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have bc : IsBaseChange X.functionField (Stacks.ModuleStalkSpecialization.germₗ F hη) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors Γ(X, U)) X.functionField _).mp h3
  exact bc.rank_eq

/-- **Stacks 0HAG.** Let `X` be an integral scheme, `ℱ` a quasi-coherent `𝒪_X`-module and `r` a
cardinal. The following are equivalent: `ℱ` has rank `r`; for every nonempty affine open
`U ⊆ X` the `𝒪_X(U)`-module `ℱ(U)` has rank `r`; for some nonempty affine open `U ⊆ X` the
`𝒪_X(U)`-module `ℱ(U)` has rank `r`. The rank of a module `M` over a domain `R` is
`dim_K (M ⊗_R K)` for `K` the fraction field of `R`. -/
@[stacks 0HAG]
theorem rank_tfae [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent] (r : Cardinal.{u}) :
    List.TFAE [F.rank = r,
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Module.rank (FractionRing Γ(X, U)) (FractionRing Γ(X, U) ⊗[Γ(X, U)] Γ(F, U)) = r,
      ∃ U : X.Opens, IsAffineOpen U ∧ Nonempty U ∧
        Module.rank (FractionRing Γ(X, U)) (FractionRing Γ(X, U) ⊗[Γ(X, U)] Γ(F, U)) = r] := by
  have key : ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
      Module.rank (FractionRing Γ(X, U)) (FractionRing Γ(X, U) ⊗[Γ(X, U)] Γ(F, U)) =
        F.rank := by
    intro U hU hne
    have : IsDomain Γ(X, U) := IsIntegral.component_integral U
    rw [rank_fractionRing_tensorProduct, rank_eq_rank_sections F hU]
  tfae_have 1 → 2 := fun h U hU hne ↦ (key U hU hne).trans h
  tfae_have 2 → 3 := fun h ↦ by
    obtain ⟨V, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, ⟨⟨_, hxV⟩⟩, h V hV ⟨⟨_, hxV⟩⟩⟩
  tfae_have 3 → 1 := fun ⟨U, hU, hne, h⟩ ↦ (key U hU hne).symm.trans h
  tfae_finish

/-- The rank of `ℱ` is the dimension of the stalk `ℱ_y` over `𝒪_{X,y}` at any point `y` which
is the generic point. -/
theorem rank_eq_of_eq_genericPoint [IsIntegral X] (F : X.Modules) {y : X}
    (hy : y = genericPoint X) :
    Module.rank (X.presheaf.stalk y) (F.presheaf.stalk y) = F.rank := by
  subst hy
  rfl

/-- **Stacks 0HAH.** Let `f : X ⟶ Y` be a dominant morphism of integral schemes and `𝒢` a
quasi-coherent `𝒪_Y`-module. Then the rank of `𝒢` on `Y` is the rank of `f^*𝒢` on `X`. -/
@[stacks 0HAH]
theorem rank_pullback_of_isDominant {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (G : Y.Modules) [G.IsQuasicoherent] :
    G.rank = ((Scheme.Modules.pullback f).obj G).rank := by
  have hfη : f (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)
  let A := ToType (Y.presheaf.stalk (f (genericPoint X)))
  let B := ToType (X.presheaf.stalk (genericPoint X))
  let : Algebra A B := (f.stalkMap (genericPoint X)).hom.toAlgebra
  let e : TensorProduct A B (ToType (TopCat.Presheaf.stalk G.val.presheaf (f (genericPoint X))))
      ≃ₗ[B] ToType (TopCat.Presheaf.stalk ((Scheme.Modules.pullback f).obj G).val.presheaf
        (genericPoint X)) :=
    Stacks.ModuleSkyscraper.pullbackStalkLinearEquiv f (genericPoint X) G
  have hA : IsField A := by
    have h : ∀ y : Y, y = genericPoint Y → IsField (Y.presheaf.stalk y) := by
      rintro y rfl
      exact Field.toIsField Y.functionField
    exact h _ hfη
  let : Field A := hA.toField
  have hinj : Function.Injective (algebraMap A B) := (algebraMap A B).injective
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  calc G.rank = Module.rank A (ToType (TopCat.Presheaf.stalk G.val.presheaf
        (f (genericPoint X)))) := (rank_eq_of_eq_genericPoint G hfη).symm
    _ = Module.rank B (TensorProduct A B (ToType (TopCat.Presheaf.stalk G.val.presheaf
        (f (genericPoint X))))) := (TensorProduct.isBaseChange A _ B).rank_eq.symm
    _ = _ := e.rank_eq

/-- **Stacks 0HAI.** On an integral scheme, for a short exact sequence
`0 → ℱ → ℱ' → ℱ'' → 0` of quasi-coherent `𝒪_X`-modules the rank of `ℱ'` is the sum of the ranks
of `ℱ` and `ℱ''`. -/
@[stacks 0HAI]
theorem rank_of_shortExact [IsIntegral X] (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.rank = S.X₁.rank + S.X₃.rank := by
  obtain ⟨f, g, hf, hfg, hg⟩ :=
    Stacks.SheafOfModules.FlatShortExact.stalkShortExact (X := X.toRingedSpace) S hS
      (genericPoint X)
  let K := ToType (X.presheaf.stalk (genericPoint X))
  let : Field K := inferInstanceAs (Field X.functionField)
  let (E : X.Modules) : Module K
      (Stacks.SheafOfModules.FlatShortExact.abStalk (X := X.toRingedSpace) E (genericPoint X)) :=
    Stacks.SheafOfModules.FlatShortExact.stalkModule E (genericPoint X)
  have h := LinearMap.rank_range_add_rank_ker g
  rw [rank_range_of_surjective g hg, hfg.linearMap_ker_eq,
    rank_range_of_injective f hf] at h
  rw [add_comm] at h
  exact h.symm

/-- The rank of the tensor product `ℱ ⊗_{𝒪_X} 𝒢` is the product of the ranks: the stalk of a
tensor product is the tensor product of the stalks ([Stacks, Tag 01CB]). -/
theorem rank_tensor [IsIntegral X] (F G : X.Modules) :
    rank (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G) =
      F.rank * G.rank := by
  let : Field (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace
      (genericPoint X)) := inferInstanceAs (Field X.functionField)
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace F.val
    (genericPoint X)
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace G.val
    (genericPoint X)
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G).val (genericPoint X)
  exact (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X.toRingedSpace
    (genericPoint X) F G).rank_eq.trans (rank_tensorProduct' ..)

/-- The rank of the sheaf of homomorphisms `ℋom_{𝒪_X}(ℱ, 𝒢)` out of a module of finite
presentation is the product of the ranks: its stalk is `Hom(ℱ_η, 𝒢_η)` ([Stacks, Tag 01CP]),
and `ℱ_η` is finite dimensional. -/
theorem rank_sheafHom [IsIntegral X] (F G : X.Modules) [F.IsFinitePresentation] :
    rank (Stacks.SheafOfModules.SheafHomStalk.internalSheafHom X.toTopCat X.sheaf F G).obj =
      F.rank * G.rank := by
  let K := ToType (X.presheaf.stalk (genericPoint X))
  let : Field K := inferInstanceAs (Field X.functionField)
  let V := ToType (F.presheaf.stalk (genericPoint X))
  let W := ToType (G.presheaf.stalk (genericPoint X))
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : Module.Finite K V := Stacks.StalkFiniteType.finite_stalk F (genericPoint X)
  let H : X.Modules := (Stacks.SheafOfModules.SheafHomStalk.internalSheafHom X.toTopCat X.sheaf
    F G).obj
  let : Module K (H.presheaf.stalk (genericPoint X)) := moduleStalkPresheaf H (genericPoint X)
  let e : (V →ₗ[K] W) ≃ₗ[K] ToType (H.presheaf.stalk (genericPoint X)) :=
    (Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearEquivOfFinitePresentation
      (Stacks.SheafOfModules.SheafHomStalk.internalSheafHom X.toTopCat X.sheaf F G)
      (genericPoint X)).equiv.symm
  let b := Module.finBasis K V
  change Module.rank K _ = Module.rank K V * Module.rank K W
  rw [← e.rank_eq, ← (dualTensorHomEquiv K V W).rank_eq, rank_tensorProduct',
    ← b.toDualEquiv.rank_eq]

/-- **Stacks 0HAJ.** Let `X` be an integral scheme and `ℱ`, `𝒢` quasi-coherent `𝒪_X`-modules.
(1) The rank of `ℱ ⊗_{𝒪_X} 𝒢` is the product of the ranks of `ℱ` and `𝒢`. (2) If `ℱ` is of
finite presentation, the rank of `ℋom_{𝒪_X}(ℱ, 𝒢)` is the product of the ranks of `ℱ` and
`𝒢`. -/
@[stacks 0HAJ]
theorem rank_tensor_and_rank_sheafHom [IsIntegral X] (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] :
    rank (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G) =
        F.rank * G.rank ∧
      (F.IsFinitePresentation →
        rank (Stacks.SheafOfModules.SheafHomStalk.internalSheafHom X.toTopCat X.sheaf F G).obj =
          F.rank * G.rank) :=
  ⟨rank_tensor F G, fun _ ↦ rank_sheafHom F G⟩

/-- **Stacks 0HAK.** Let `X` be an integral scheme and `ℱ` a quasi-coherent `𝒪_X`-module of
finite type. Then `ℱ` has finite rank `r ≥ 0`, and there is a nonempty open `U ⊆ X` such that
`ℱ|_U` is free of rank `r`. -/
@[stacks 0HAK]
theorem exists_rank_eq_and_over_iso_free [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] :
    ∃ r : ℕ, F.rank = r ∧ ∃ U : X.Opens, Nonempty U ∧
      Nonempty (F.over U ≅
        _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin r))) := by
  classical
  let η := genericPoint X
  let K := ToType (X.presheaf.stalk η)
  let M := ToType (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf η)
  let : Module K M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val η
  let : Field K := inferInstanceAs (Field X.functionField)
  have : Module.Finite K M := _root_.SheafOfModules.finite_stalk X.sheaf F η
  refine ⟨Module.finrank K M, (Module.finrank_eq_rank K M).symm, ?_⟩
  let r := Module.finrank K M
  let b : Module.Basis (ULift.{u} (Fin r)) K M := (Module.finBasis K M).reindex Equiv.ulift.symm
  obtain ⟨U, -, hηU, s, hs⟩ :=
    finite_germ_lifts F.val.presheaf η (fun i ↦ (b i : M)) (V := (⊤ : X.Opens)) (Set.mem_univ η)
  have hspan : ⊤ ≤ Submodule.span K
      (Set.range fun i ↦ TopCat.Presheaf.germ F.val.presheaf U η hηU (s i)) := by
    simp only [hs]
    exact b.span_eq.ge
  obtain ⟨W, hWU, hηW, hspanW⟩ := span_germs_near F s η hηU hspan
  refine ⟨W, ⟨⟨η, hηW⟩⟩, ?_⟩
  let t : ULift.{u} (Fin r) → F.val.presheaf.obj (op W) :=
    fun i ↦ F.val.presheaf.map (homOfLE hWU).op (s i)
  have hgt : ∀ i, TopCat.Presheaf.germ F.val.presheaf W η hηW (t i) = b i := fun i ↦
    (germ_map_section F (homOfLE hWU) η hηW (s i)).trans (hs i)
  have hzero : ∀ ⦃V : X.Opens⦄ (f : V ⟶ W) (a : ULift.{u} (Fin r) → X.ringCatSheaf.obj.obj (op V)),
      ∑ i, a i • Stacks.SheafOfModules.res F f (t i) = 0 → a = 0 := by
    intro V f a ha
    funext i
    refine TopCat.Presheaf.section_ext X.sheaf V (a i) 0 fun y hy ↦ ?_
    have hηV : η ∈ V := genericPoint_mem_of_nonempty ⟨⟨y, hy⟩⟩
    have hgerm : ∀ j, TopCat.Presheaf.germ F.val.presheaf V η hηV
          (a j • Stacks.SheafOfModules.res F f (t j))
        = X.presheaf.germ V η hηV (a j) • (b j : M) := fun j ↦
      (PresheafOfModules.germ_smul (R := X.presheaf) F.val η V hηV (a j)
        (F.val.presheaf.map f.op (t j) : F.val.obj (op V))).trans
        (congrArg (fun w : M ↦ X.presheaf.germ V η hηV (a j) • w)
          ((germ_map_section F f η hηV (t j)).trans (hgt j)))
    have hsum : ∑ j, X.presheaf.germ V η hηV (a j) • (b j : M) = 0 :=
      (Finset.sum_congr rfl fun j _ ↦ (hgerm j).symm).trans
        ((map_sum (ConcreteCategory.hom
            (TopCat.Presheaf.germ F.val.presheaf V η hηV)) _ _).symm.trans
          ((congrArg (ConcreteCategory.hom
            (TopCat.Presheaf.germ F.val.presheaf V η hηV)) ha).trans (map_zero _)))
    have hai : X.presheaf.germ V η hηV (a i) = 0 :=
      Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum i
    have : a i = 0 := germ_injective_of_isIntegral X η hηV (hai.trans (map_zero _).symm)
    rw [this]
    rfl
  refine Stacks.SheafOfModules.nonempty_over_iso_free_of_inj_of_surj F t
    (fun V f a a' haa ↦ ?_) (fun V f t' y hy ↦ ?_)
  · refine sub_eq_zero.mp (hzero f (a - a') ?_)
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [show (∑ i, a i • Stacks.SheafOfModules.res F f (t i))
      = ∑ i, a' i • Stacks.SheafOfModules.res F f (t i) from haa, sub_self]
  · let : Module (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
    have hspany : ⊤ ≤ Submodule.span (X.presheaf.stalk y)
        (Set.range fun i ↦ TopCat.Presheaf.germ F.val.presheaf W y (f.le hy) (t i)) := by
      simpa only [t, germ_map_section F (homOfLE hWU) y (f.le hy)] using hspanW y (f.le hy)
    obtain ⟨W', hWV, hWU', hyW, c, hc⟩ := exists_combination_of_germ_mem_span F t t' y (f.le hy)
      hy (hspany Submodule.mem_top)
    refine ⟨W', homOfLE hWV, hyW, c, ?_⟩
    rwa [show homOfLE hWV ≫ f = homOfLE hWU' from Subsingleton.elim _ _]

end AlgebraicGeometry.Scheme.Modules
