module

public import StacksFrontier.AlgebraicGeometry.Modules.DerivedAffineSystemKZero
public import StacksFrontier.LinearAlgebra.ExteriorPower.SquareArrowFunctorsComparison
public import StacksFrontier.LinearAlgebra.ExteriorPower.SecondAdamsLocal
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.CodimensionWeightOperator
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.KernelGlue
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
public import StacksFrontier.Homology.Perfect.Regular
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.CechElementChase.Basic
import all StacksFrontier.Homology.Perfect.Regular

/-!
# The second Adams operation on `𝐐 ⊗ K₀(Coh_W(Y))` for a regular scheme

Let `Y` be a regular, quasi-compact, locally Noetherian scheme, and write `T(M) = M ⊗ M` and
`Λ²(M)` for the tensor and exterior squares. For a coherent `𝒪_Y`-module `F` let
`Lⱼ T(F)` and `Lⱼ Λ²(F)` be the quasi-coherent modules glued from the simplicial derived functors
of `T` and `Λ²` at the modules of sections of `F` over the affine opens; they are the derived
sheaves `Lⱼ (T ∘ right)(0 → F)` and `Lⱼ (Λ² ∘ right)(0 → F)` of the arrow `0 → F`. They are
coherent and supported in `supp F`, and they vanish for `j` large: over each of finitely many
affine opens `U` with regular ring of sections covering `Y`, the module `Γ(F, U)` has finite
projective dimension `d_U`, and the derived functors vanish above `2 d_U`. For a closed subset
`W ⊆ Y` this gives an endomorphism `ψ_W` of `K₀(Coh_W(Y))` with

  `ψ_W [F] = Σ_{j ≤ N} (-1)ʲ ([Lⱼ T(F)] - 2 [Lⱼ Λ²(F)])`

for every `N` past the vanishing bound.

**Additivity.** Let `0 → F' → F → F'' → 0` be exact in `Coh_W(Y)` and consider the arrow
`F' → F`. The four short exact sequences of semilinear functors on arrows

`0 → Λ² X₀ → Λ² X₁ → D_Λ(X) → 0`, `0 → X₀ ⊗ coker X → D_Λ(X) → Λ² coker X → 0`,
`0 → T X₀ → T X₁ → D_T(X) → 0`, `0 → (X₀ ⊗ coker X) ⊞ (coker X ⊗ X₀) → D_T(X) → T coker X → 0`,

together with the split sequence `0 → X₀ ⊗ coker X → (X₀ ⊗ coker X) ⊞ (coker X ⊗ X₀) →
coker X ⊗ X₀ → 0`, give glued long exact sequences of derived sheaves at `F' → F`, whose Euler
characteristics vanish in `K₀(Coh_W(Y))`. The outer terms are identified with the derived
sheaves of `0 → F'`, `0 → F` and `0 → F''`: the derived sheaves of `Q ∘ left` at `F' → F` with
those of `Q ∘ right` at `0 → F'` (through the identity of `F'`), those of `Q ∘ right` with those
at `0 → F` (the targets agree), and those of `Q ∘ coker` with those of `Q ∘ right` at `0 → F''`
(the sequence of sections over an affine open is exact). The two cross terms of `D_T` are
exchanged by the braiding, so they cancel against twice the cross term of `D_Λ`, and
`ψ_W [F] = ψ_W [F'] + ψ_W [F'']`.

**Naturality and the leading term.** The classes are those of the same modules for every `W`
containing the support, so `ψ_W` commutes with the maps induced by inclusions `W' ⊆ W`, and
`ψ = 𝐐 ⊗ ψ_W` is a natural endomorphism of `W ↦ 𝐐 ⊗ K₀(Coh_W(Y))`. If every point of `W` has
relative dimension at most `k` over the base of a Chow situation, at a point `y` with relative
dimension `k` and local ring of dimension `n` the coefficient of the `k`-cycle of `ψ x` is `2ⁿ`
times that of `x`: the multiplicities at `y` of the derived sheaves are the lengths of the
derived modules at the localized arrow over `𝒪_{Y,y}`, a regular local ring of dimension `n`, the
stalk `F_y` has finite length, and `Σ (-1)ʲ length Lⱼ T(F_y) - 2 Σ (-1)ʲ length Lⱼ Λ²(F_y)` is
`2ⁿ length F_y`.

## Main definitions

* `Stacks.Chow.derivedTensorSquareSheaf`, `Stacks.Chow.derivedExteriorSquareSheaf`: the derived
  sheaves `Lⱼ T(F)` and `Lⱼ Λ²(F)`.
* `Stacks.Chow.derivedSheafClass`, `Stacks.Chow.derivedSheafEulerClass`: the class in
  `K₀(Coh_W(Y))` of a derived sheaf of a quasi-coherent arrow, and alternating sums of them.
* `Stacks.Chow.secondAdamsSum`: `Σ_{j ≤ N} (-1)ʲ ([Lⱼ T(F)] - 2 [Lⱼ Λ²(F)])`.
* `Stacks.Chow.supportedSecondAdams`: the endomorphism `ψ_W` of `K₀(Coh_W(Y))`.
* `Stacks.Chow.supportedSecondAdamsRat`: the natural endomorphism `ψ` of
  `W ↦ 𝐐 ⊗ K₀(Coh_W(Y))`.

## Main results

* `Stacks.Chow.exists_isZero_derivedTensorSquareSheaf`: the derived sheaves of a coherent module
  vanish in large degrees; `Stacks.Chow.isCoherent_derivedTensorSquareSheaf` and
  `Stacks.Chow.supp_derivedTensorSquareSheaf_subset` (and the same for `Λ²`): coherence and
  support.
* `Stacks.Chow.derivedSheafEulerClass_eq_add`: the Euler relation of a glued long exact
  sequence.
* `Stacks.Chow.secondAdamsSum_add`: additivity on short exact sequences.
* `Stacks.Chow.supportedSecondAdams_mk_eq_secondAdamsSum`: the value of `ψ_W` on a class.
* `Stacks.Chow.supportedSecondAdams_comp_supportedCoherentKZeroMap`: naturality.
* `Stacks.Chow.rationalCycleCoeff_supportedCoherentKZeroRatCycle_supportedSecondAdamsRat`: the
  leading term, `2ⁿ` times the coefficient at a point of maximal relative dimension.

## Implementation notes

A single module `F` enters as the arrow `0 → F` from a zero module; the derived sheaves of
`Q ∘ right` only depend on the target. The derived sheaves are compared through the morphisms of
glued sheaves induced by commutative squares of arrows and by morphisms of semilinear functors,
which are isomorphisms as soon as they are on the modules of sections over every affine open.
The alternating sums in `ψ_W` are taken up to a vanishing bound chosen once and for all
(`Stacks.Chow.secondAdamsBound`); any larger bound gives the same class.

## References

* H. Gillet, C. Soulé, *Intersection theory using Adams operations*, Invent. Math. 90 (1987),
  243–277.
* [Stacks Project, Tag 0FEW](https://stacks.math.columbia.edu/tag/0FEW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped ZeroObject

universe u

/-! ### Exact sequences and the cokernel of an arrow -/

/-- If a morphism `g : X ⟶ X'` of arrows of modules, with `X'` of zero source, is surjective on
targets and `X₀ → X₁ → X'₁` is exact, then `g` induces an isomorphism of cokernels. -/
theorem CategoryTheory.ComposableArrows.isIso_cokernelFunctor_map_of_exact {A : Type u} [Ring A]
    {X X' : ComposableArrows (ModuleCat.{u} A) 1} (g : X ⟶ X') (hX' : IsZero X'.left)
    (hex : Function.Exact X.hom (g.app 1)) (hsurj : Function.Surjective (g.app 1)) :
    IsIso (cokernelFunctor.map g) := by
  have hπ : IsIso (cokernel.π X'.hom) := cokernel.π_of_zero (hX'.eq_of_src _ _)
  have hπX : Function.Surjective (cokernel.π X.hom) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hπX' : Function.Injective (cokernel.π X'.hom) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hπX's : Function.Surjective (cokernel.π X'.hom) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have h : cokernel.π X.hom ≫ cokernelFunctor.map g = g.app 1 ≫ cokernel.π X'.hom :=
    cokernel.π_desc _ _ _
  have hcomp : ∀ x, (cokernelFunctor.map g) (cokernel.π X.hom x) =
      cokernel.π X'.hom (g.app 1 x) := fun x => ConcreteCategory.congr_hom h x
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun z₁ z₂ h => ?_, fun z => ?_⟩
  · obtain ⟨x₁, rfl⟩ := hπX z₁
    obtain ⟨x₂, rfl⟩ := hπX z₂
    rw [hcomp, hcomp] at h
    have h' : g.app 1 (x₁ - x₂) = 0 := by rw [map_sub, hπX' h, sub_self]
    obtain ⟨x, hx⟩ := (hex _).1 h'
    have h₀ : cokernel.π X.hom (X.hom x) = 0 :=
      ConcreteCategory.congr_hom (cokernel.condition X.hom) x
    have h₁ : cokernel.π X.hom x₁ = cokernel.π X.hom x₂ := by
      rw [← sub_eq_zero, ← map_sub, ← hx, h₀]
    exact h₁
  · obtain ⟨y, rfl⟩ := hπX's z
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨_, hcomp x⟩

/-! ### Vanishing on a cover, and the arrows of sections -/

namespace Stacks.Modules

open Stacks.AlgebraicGeometry.FiniteTypeSubmodule (subsingleton_sections_of_isZero)

variable {Y : Scheme.{u}}

/-- **A quasi-coherent module is zero as soon as its sections over the members of an affine open
cover are**: its stalk at a point of a member `U` is a localization of `Γ(G, U)`. -/
theorem isZero_of_subsingleton_sections_of_cover (G : Y.Modules) [G.IsQuasicoherent]
    {ι : Type*} (U : ι → Y.affineOpens) (hU : ∀ y : Y, ∃ i, y ∈ ((U i : Y.affineOpens) : Y.Opens))
    (h : ∀ i, Subsingleton Γ(G, U i)) : IsZero G := by
  refine Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty G
    (Set.eq_empty_of_forall_notMem fun y hy => ?_)
  obtain ⟨i, hi⟩ := hU y
  have := h i
  have hl := ModuleStalkSpecialization.length_stalk_eq_length_localizedModule G (U i).2 hi
  have : Subsingleton (LocalizedModule ((U i).2.primeIdealOf ⟨y, hi⟩).asIdeal.primeCompl
      Γ(G, U i)) := inferInstance
  rw [(Module.length_eq_zero_iff).2 this] at hl
  exact (not_nontrivial_iff_subsingleton.2 (Module.length_eq_zero_iff.1 hl))
    ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ y).1 hy)

/-- The map on sections of an isomorphism of `𝒪_Y`-modules is an isomorphism of modules. -/
theorem isIso_ofHom_appₗ {G G' : Y.Modules} (b : G ⟶ G') [IsIso b] (U : Y.Opens) :
    IsIso (ModuleCat.ofHom (Stacks.AlgebraicGeometry.QcohLimits.appₗ b U)) :=
  ⟨ModuleCat.ofHom (Stacks.AlgebraicGeometry.QcohLimits.appₗ (inv b) U),
    by ext (x : Γ(G, U))
       exact congrArg (fun t => (Scheme.Modules.Hom.app t U).hom x) (IsIso.hom_inv_id b),
    by ext (x : Γ(G', U))
       exact congrArg (fun t => (Scheme.Modules.Hom.app t U).hom x) (IsIso.inv_hom_id b)⟩

variable {F' F G' G : Y.Modules} {f : F' ⟶ F} {g : G' ⟶ G}

/-- A square whose left side is an isomorphism induces isomorphisms on the sources of the arrows
of sections. -/
instance isIso_arrowSectionsMap_app_zero (a : F' ⟶ G') (b : F ⟶ G) (w : f ≫ b = a ≫ g)
    [IsIso a] (U : Y.affineOpens) : IsIso ((arrowSectionsMap a b w U).app 0) :=
  isIso_ofHom_appₗ a U

/-- A square whose right side is an isomorphism induces isomorphisms on the targets of the arrows
of sections. -/
instance isIso_arrowSectionsMap_app_one (a : F' ⟶ G') (b : F ⟶ G) (w : f ≫ b = a ≫ g)
    [IsIso b] (U : Y.affineOpens) : IsIso ((arrowSectionsMap a b w U).app 1) :=
  isIso_ofHom_appₗ b U

/-- The arrow of sections of an isomorphism is an isomorphism. -/
instance isIso_arrowSections_hom (f : F' ⟶ F) [IsIso f] (U : Y.affineOpens) :
    IsIso (arrowSections f U).hom :=
  isIso_ofHom_appₗ f U

/-- The arrow of sections of a monomorphism is a monomorphism. -/
instance mono_arrowSections_hom (f : F' ⟶ F) [Mono f] (U : Y.affineOpens) :
    Mono (arrowSections f U).hom :=
  (ModuleCat.mono_iff_injective _).2
    (AlgebraicGeometry.CardinalGeneration.injective_app_of_mono f U)

/-- The arrow of sections of a morphism out of a zero module has zero source. -/
theorem isZero_arrowSections_left (f : F' ⟶ F) (hF' : IsZero F') (U : Y.affineOpens) :
    IsZero (arrowSections f U).left :=
  @ModuleCat.isZero_of_subsingleton _ _ _ (subsingleton_sections_of_isZero hF' U)

/-- **The cokernel of the arrow of sections of a short exact sequence.** For a short exact
sequence `0 → F' → F → F'' → 0` of quasi-coherent modules and an affine open `U`, the square from
`F' → F` to `0 → F''` induces an isomorphism `coker (Γ(F', U) → Γ(F, U)) ≅ Γ(F'', U)`. -/
theorem isIso_cokernelFunctor_map_arrowSectionsMap [F'.IsQuasicoherent] [F.IsQuasicoherent]
    {F'' G₀ : Y.Modules} [F''.IsQuasicoherent] (u : F' ⟶ F) (v : F ⟶ F'') (huv : u ≫ v = 0)
    (hS : (ShortComplex.mk u v huv).ShortExact) (g₀ : G₀ ⟶ F'') (hG₀ : IsZero G₀)
    (w : u ≫ v = 0 ≫ g₀) (U : Y.affineOpens) :
    IsIso (ComposableArrows.cokernelFunctor.map (arrowSectionsMap 0 v w U)) := by
  have := hS.epi_g
  refine ComposableArrows.isIso_cokernelFunctor_map_of_exact _
    (isZero_arrowSections_left g₀ hG₀ U) (fun y => ⟨fun hy => ?_, ?_⟩)
    (Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen Y v U U.2)
  · exact Stacks.CechElementChase.exists_app_map_f_eq _ _ hS U y hy
  · rintro ⟨x, rfl⟩
    change ((u ≫ v).app (U : Y.Opens)).hom x = 0
    rw [huv]
    rfl

end Stacks.Modules

/-! ### Semilinear functors: the biproduct and the squares of the target -/

namespace Stacks.SemilinearArrowFunctor

open Stacks.Cohomology.AmbientMayerVietoris (biprod_inl_fst_app biprod_inl_snd_app
  biprod_inr_snd_app biprod_total_app)

variable {Φ Ψ : SemilinearArrowFunctor.{u}}

/-- The inclusion `Φ ⟶ Φ ⊞ Ψ` of the first summand. -/
def biprodInl : Φ ⟶ biprod Φ Ψ where
  app A := Limits.biprod.inl
  comm {A B} φ := by
    ext Y : 2
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.app_add, Preadditive.comp_add, reassoc_of% biprod_inl_fst_app,
      reassoc_of% biprod_inl_snd_app, zero_comp, add_zero]

/-- The projection `Φ ⊞ Ψ ⟶ Ψ` onto the second summand. -/
def biprodSnd : biprod Φ Ψ ⟶ Ψ where
  app A := Limits.biprod.snd
  comm {A B} φ := by
    ext Y : 2
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.app_add, Preadditive.add_comp, Category.assoc, ← Functor.map_comp,
      biprod_inl_snd_app, biprod_inr_snd_app, Functor.map_zero, comp_zero, zero_add,
      CategoryTheory.Functor.map_id]
    exact (congrArg (_ ≫ ·) (Category.comp_id _)).symm

/-- `0 → Φ → Φ ⊞ Ψ → Ψ → 0` is a short exact sequence of semilinear functors: it is split at
every arrow. -/
theorem shortExact_biprodInl_biprodSnd : ShortExact (biprodInl (Φ := Φ) (Ψ := Ψ)) biprodSnd :=
  ShortExact.mk' (fun A => NatTrans.ext (funext fun X =>
      biprod_inl_snd_app (Φ.obj A) (Ψ.obj A) X))
    fun A P _ => ShortComplex.Splitting.shortExact
      { r := (Limits.biprod.fst : Φ.obj A ⊞ Ψ.obj A ⟶ Φ.obj A).app P
        s := (Limits.biprod.inr : Ψ.obj A ⟶ Φ.obj A ⊞ Ψ.obj A).app P
        f_r := biprod_inl_fst_app _ _ P
        s_g := biprod_inr_snd_app _ _ P
        id := biprod_total_app _ _ P }

/-- `T ∘ right` commutes with flat base change on projective arrows. -/
theorem hasFlatBaseChange_tensorSquareRight : (tensor right right).HasFlatBaseChange.{u} :=
  hasFlatBaseChange_tensor hasFlatBaseChange_right hasFlatBaseChange_right

/-- `Λ² ∘ right` commutes with flat base change on projective arrows. -/
theorem hasFlatBaseChange_exteriorSquareRight : (exteriorPower 2 right).HasFlatBaseChange.{u} :=
  hasFlatBaseChange_exteriorPower 2 hasFlatBaseChange_right

/-- `T ∘ right` preserves finiteness. -/
theorem preservesFinite_tensorSquareRight : (tensor right right).PreservesFinite.{u} :=
  preservesFinite_tensor preservesFinite_right preservesFinite_right

/-- `Λ² ∘ right` preserves finiteness. -/
theorem preservesFinite_exteriorSquareRight : (exteriorPower 2 right).PreservesFinite.{u} :=
  preservesFinite_exteriorPower 2 preservesFinite_right

/-- `T ∘ right` vanishes on zero arrows. -/
theorem vanishesOnZero_tensorSquareRight : (tensor right right).VanishesOnZero.{u} :=
  vanishesOnZero_tensor_left vanishesOnZero_right _

/-- `Λ² ∘ right` vanishes on zero arrows. -/
theorem vanishesOnZero_exteriorSquareRight : (exteriorPower 2 right).VanishesOnZero.{u} :=
  vanishesOnZero_exteriorPower two_ne_zero vanishesOnZero_right

open SimplicialProjectiveResolution in
/-- **The second Adams operation at a finite-length target, over any range past `2c`.** For a
regular local ring `R` of dimension `c`, an arrow `X` whose target has finite length and
`N ≥ 2c`, `Σ_{j ≤ N} (-1)ʲ (length Lⱼ(T ∘ right)(X) - 2 length Lⱼ(Λ² ∘ right)(X))` is
`2^c · length X₁`: the derived modules vanish above `2c`. -/
theorem sum_range_length_tensor_right_sub_two_mul_length_exteriorPower_right
    {R : CommRingCat.{u}} [IsRegularLocalRing R] {c : ℕ} (hc : ringKrullDim R = c)
    {X : ComposableArrows (ModuleCat.{u} R) 1} (hX : IsFiniteLength R X.right)
    (P : SimplicialProjectiveResolution X) {N : ℕ} (hN : 2 * c ≤ N) :
    ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ j •
        (((Module.length R (P.derivedHomology (D := ModuleCat.{u} R)
          ((tensor right right).obj R) j)).toNat : ℤ) -
        2 • ((Module.length R (P.derivedHomology (D := ModuleCat.{u} R)
          ((exteriorPower 2 right).obj R) j)).toNat : ℤ)) =
      2 ^ c * ((Module.length R X.right).toNat : ℤ) := by
  have hpd : HasProjectiveDimensionLE X.right c :=
    (IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE
      hc.le).2 X.right
  have hT := Module.sum_range_neg_one_pow_mul_length_eq_of_isZero
    (f := fun j => P.derivedHomology (D := ModuleCat.{u} R) ((tensor right right).obj R) j)
    (N := 2 * c + 1) (fun i hi => isZero_derivedHomology_tensor_right hpd P (by omega))
    (m := N + 1) (by omega)
  have hΛ := Module.sum_range_neg_one_pow_mul_length_eq_of_isZero
    (f := fun j => P.derivedHomology (D := ModuleCat.{u} R) ((exteriorPower 2 right).obj R) j)
    (N := 2 * c + 1) (fun i hi => isZero_derivedHomology_exteriorSquare_right hpd P (by omega))
    (m := N + 1) (by omega)
  beta_reduce at hT hΛ
  rw [← sum_length_tensor_right_sub_two_mul_sum_length_exteriorPower_right_of_isFiniteLength hc
    hX P, ← hT, ← hΛ]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  push_cast
  ring

/-! ### Derived sheaves: vanishing, coherence, support and comparisons -/

open Modules SimplicialProjectiveResolution

variable {Y : Scheme.{u}} {F' F G' G : Y.Modules} [F'.IsQuasicoherent] [F.IsQuasicoherent]

/-- `Lⱼ Φ(f)` vanishes as soon as `Lⱼ Φ` vanishes at the arrows of sections over the members of
an affine open cover. -/
theorem isZero_derivedSheaf_of_cover (hΦ : Φ.HasFlatBaseChange) (f : F' ⟶ F) (j : ℕ) {ι : Type*}
    (U : ι → Y.affineOpens) (hU : ∀ y : Y, ∃ i, y ∈ ((U i : Y.affineOpens) : Y.Opens))
    (h : ∀ i, IsZero ((arrowSectionsResolution Y f (U i)).derivedHomology
      (D := ModuleCat.{u} Γ(Y, U i)) (Φ.obj Γ(Y, U i)) j)) :
    IsZero (Φ.derivedSheaf f hΦ j) :=
  isZero_of_subsingleton_sections_of_cover _ U hU fun i =>
    (Φ.derivedSheafSectionsEquiv f hΦ j (U i)).toEquiv.subsingleton_congr.2
      (ModuleCat.isZero_iff_subsingleton.1 (h i))

/-- **Coherence** of `Lⱼ Φ(f)` for a semilinear functor preserving finiteness, on a locally
Noetherian scheme, at a morphism of quasi-coherent modules of finite type. -/
theorem isCoherent_derivedSheaf_of_preservesFinite [IsLocallyNoetherian Y] [F'.IsFiniteType]
    [F.IsFiniteType] (hΦ : Φ.HasFlatBaseChange) (hfin : Φ.PreservesFinite) (f : F' ⟶ F)
    (j : ℕ) : _root_.SheafOfModules.IsCoherent (Φ.derivedSheaf f hΦ j) :=
  Φ.isCoherent_derivedSheaf f hΦ j fun A hA _X h₀ h₁ P =>
    have := hA
    have := h₀
    have := h₁
    finite_derivedHomology (A := A) hfin P j

/-- **Support** of `Lⱼ Φ(f)` for a semilinear functor vanishing on zero arrows: it lies in every
set containing the supports of `F'` and `F`. -/
theorem supp_derivedSheaf_subset_of_vanishesOnZero (hΦ : Φ.HasFlatBaseChange)
    (hzero : Φ.VanishesOnZero) (f : F' ⟶ F) (j : ℕ) {W : Set Y}
    (hF' : SheafOfModules.supp F' ⊆ W) (hF : SheafOfModules.supp F ⊆ W) :
    SheafOfModules.supp (Φ.derivedSheaf f hΦ j) ⊆ W :=
  supp_derivedSheaf_subset_of_subset f hΦ j
    (fun _ _ h₀ h₁ P => isZero_derivedHomology_of_vanishesOnZero hzero h₀ h₁ P j) hF' hF

variable [G'.IsQuasicoherent] [G.IsQuasicoherent] {f : F' ⟶ F} {g : G' ⟶ G}

/-- A square of quasi-coherent arrows whose right side is an isomorphism induces isomorphisms on
`Lⱼ (Λⁿ ∘ right)`. -/
theorem isIso_derivedSheafMapOfSquare_exteriorPower_right (n : ℕ)
    (hΦ : (exteriorPower n right).HasFlatBaseChange.{u}) (a : F' ⟶ G') (b : F ⟶ G)
    (w : f ≫ b = a ≫ g) [IsIso b] (j : ℕ) :
    IsIso ((exteriorPower n right).derivedSheafMapOfSquare hΦ a b w j) :=
  isIso_derivedSheafMapOfSquare _ hΦ a b w j fun _ =>
    isIso_derivedMap_exteriorPower_right n _ _ _ j

/-- A square of quasi-coherent arrows whose right side is an isomorphism induces isomorphisms on
`Lⱼ (T ∘ right)`. -/
theorem isIso_derivedSheafMapOfSquare_tensor_right
    (hΦ : (tensor right right).HasFlatBaseChange.{u}) (a : F' ⟶ G') (b : F ⟶ G)
    (w : f ≫ b = a ≫ g) [IsIso b] (j : ℕ) :
    IsIso ((tensor right right).derivedSheafMapOfSquare hΦ a b w j) :=
  isIso_derivedSheafMapOfSquare _ hΦ a b w j fun _ => isIso_derivedMap_tensor_right _ _ _ j

/-- A square of quasi-coherent arrows whose left side is an isomorphism induces isomorphisms on
`Lⱼ (Λⁿ ∘ left)`. -/
theorem isIso_derivedSheafMapOfSquare_exteriorPower_left (n : ℕ)
    (hΦ : (exteriorPower n left).HasFlatBaseChange.{u}) (a : F' ⟶ G') (b : F ⟶ G)
    (w : f ≫ b = a ≫ g) [IsIso a] (j : ℕ) :
    IsIso ((exteriorPower n left).derivedSheafMapOfSquare hΦ a b w j) :=
  isIso_derivedSheafMapOfSquare _ hΦ a b w j fun _ =>
    isIso_derivedMap_exteriorPower_left n _ _ _ j

/-- A square of quasi-coherent arrows whose left side is an isomorphism induces isomorphisms on
`Lⱼ (T ∘ left)`. -/
theorem isIso_derivedSheafMapOfSquare_tensor_left
    (hΦ : (tensor left left).HasFlatBaseChange.{u}) (a : F' ⟶ G') (b : F ⟶ G)
    (w : f ≫ b = a ≫ g) [IsIso a] (j : ℕ) :
    IsIso ((tensor left left).derivedSheafMapOfSquare hΦ a b w j) :=
  isIso_derivedSheafMapOfSquare _ hΦ a b w j fun _ => isIso_derivedMap_tensor_left _ _ _ j

/-- At an isomorphism of quasi-coherent modules, `Lⱼ (Λⁿ ∘ left) ⟶ Lⱼ (Λⁿ ∘ right)` is an
isomorphism. -/
theorem isIso_derivedSheafMap_exteriorPowerMap_leftToRight (n : ℕ) (f : F' ⟶ F) [IsIso f]
    (h₁ : (exteriorPower n left).HasFlatBaseChange.{u})
    (h₂ : (exteriorPower n right).HasFlatBaseChange.{u}) (j : ℕ) :
    IsIso (derivedSheafMap f (exteriorPowerMap n leftToRight) h₁ h₂ j) :=
  isIso_derivedSheafMap f _ h₁ h₂ j fun _ =>
    isIso_derivedHomologyMap_exteriorPowerMap_leftToRight n _ j

/-- At an isomorphism of quasi-coherent modules, `Lⱼ (T ∘ left) ⟶ Lⱼ (T ∘ right)` is an
isomorphism. -/
theorem isIso_derivedSheafMap_tensorHom_leftToRight (f : F' ⟶ F) [IsIso f]
    (h₁ : (tensor left left).HasFlatBaseChange.{u})
    (h₂ : (tensor right right).HasFlatBaseChange.{u}) (j : ℕ) :
    IsIso (derivedSheafMap f (tensorHom leftToRight leftToRight) h₁ h₂ j) :=
  isIso_derivedSheafMap f _ h₁ h₂ j fun _ => isIso_derivedHomologyMap_tensorHom_leftToRight _ j

/-- At a morphism out of a zero module, `Lⱼ (Λⁿ ∘ right) ⟶ Lⱼ (Λⁿ ∘ coker)` is an
isomorphism. -/
theorem isIso_derivedSheafMap_exteriorPowerMap_rightToCoker (n : ℕ) (f : F' ⟶ F)
    (hF' : IsZero F') (h₁ : (exteriorPower n right).HasFlatBaseChange.{u})
    (h₂ : (exteriorPower n coker).HasFlatBaseChange.{u}) (j : ℕ) :
    IsIso (derivedSheafMap f (exteriorPowerMap n rightToCoker) h₁ h₂ j) :=
  isIso_derivedSheafMap f _ h₁ h₂ j fun U =>
    isIso_derivedHomologyMap_exteriorPowerMap_rightToCoker n (isZero_arrowSections_left f hF' U)
      _ j

/-- At a morphism out of a zero module, `Lⱼ (T ∘ right) ⟶ Lⱼ (T ∘ coker)` is an isomorphism. -/
theorem isIso_derivedSheafMap_tensorHom_rightToCoker (f : F' ⟶ F) (hF' : IsZero F')
    (h₁ : (tensor right right).HasFlatBaseChange.{u})
    (h₂ : (tensor coker coker).HasFlatBaseChange.{u}) (j : ℕ) :
    IsIso (derivedSheafMap f (tensorHom rightToCoker rightToCoker) h₁ h₂ j) :=
  isIso_derivedSheafMap f _ h₁ h₂ j fun U =>
    isIso_derivedHomologyMap_tensorHom_rightToCoker (isZero_arrowSections_left f hF' U) _ j

/-- The braiding induces isomorphisms `Lⱼ(X₀ ⊗ coker X)(f) ≅ Lⱼ(coker X ⊗ X₀)(f)`. -/
theorem isIso_derivedSheafMap_crossIsoCrossRev (f : F' ⟶ F) (h₁ : cross.HasFlatBaseChange.{u})
    (h₂ : crossRev.HasFlatBaseChange.{u}) (j : ℕ) :
    IsIso (derivedSheafMap f crossIsoCrossRev.hom h₁ h₂ j) :=
  isIso_derivedSheafMap f _ h₁ h₂ j fun U =>
    (derivedHomologyCrossIso (arrowSectionsResolution Y f U) j).isIso_hom

/-- For a short exact sequence `0 → F' → F → F'' → 0` of quasi-coherent modules, the square from
`F' → F` to an arrow `0 → F''` out of a zero module induces isomorphisms on
`Lⱼ (Λⁿ ∘ coker)`. -/
theorem isIso_derivedSheafMapOfSquare_exteriorPower_coker (n : ℕ)
    (hΦ : (exteriorPower n coker).HasFlatBaseChange.{u}) {F'' G₀ : Y.Modules}
    [F''.IsQuasicoherent] [G₀.IsQuasicoherent] (u : F' ⟶ F) (v : F ⟶ F'') (huv : u ≫ v = 0)
    (hS : (ShortComplex.mk u v huv).ShortExact) (g₀ : G₀ ⟶ F'') (hG₀ : IsZero G₀)
    (w : u ≫ v = 0 ≫ g₀) (j : ℕ) :
    IsIso ((exteriorPower n coker).derivedSheafMapOfSquare hΦ 0 v w j) := by
  have := hS.mono_f
  refine isIso_derivedSheafMapOfSquare _ hΦ 0 v w j fun U => ?_
  have : Mono (arrowSections g₀ U).hom := (isZero_arrowSections_left g₀ hG₀ U).mono _
  have := isIso_cokernelFunctor_map_arrowSectionsMap u v huv hS g₀ hG₀ w U
  exact isIso_derivedMap_exteriorPower_coker n _ _ _ j

/-- For a short exact sequence `0 → F' → F → F'' → 0` of quasi-coherent modules, the square from
`F' → F` to an arrow `0 → F''` out of a zero module induces isomorphisms on `Lⱼ (T ∘ coker)`. -/
theorem isIso_derivedSheafMapOfSquare_tensor_coker
    (hΦ : (tensor coker coker).HasFlatBaseChange.{u}) {F'' G₀ : Y.Modules}
    [F''.IsQuasicoherent] [G₀.IsQuasicoherent] (u : F' ⟶ F) (v : F ⟶ F'') (huv : u ≫ v = 0)
    (hS : (ShortComplex.mk u v huv).ShortExact) (g₀ : G₀ ⟶ F'') (hG₀ : IsZero G₀)
    (w : u ≫ v = 0 ≫ g₀) (j : ℕ) :
    IsIso ((tensor coker coker).derivedSheafMapOfSquare hΦ 0 v w j) := by
  have := hS.mono_f
  refine isIso_derivedSheafMapOfSquare _ hΦ 0 v w j fun U => ?_
  have : Mono (arrowSections g₀ U).hom := (isZero_arrowSections_left g₀ hG₀ U).mono _
  have := isIso_cokernelFunctor_map_arrowSectionsMap u v huv hS g₀ hG₀ w U
  exact isIso_derivedMap_tensor_coker _ _ _ j

end Stacks.SemilinearArrowFunctor

namespace Stacks.Chow

open SemilinearArrowFunctor Modules SimplicialProjectiveResolution

variable {Y : Scheme.{u}}

/-! ### The derived tensor and exterior squares of a module -/

/-- The zero `𝒪_Y`-module is quasi-coherent. -/
instance isQuasicoherent_zeroModule : (0 : Y.Modules).IsQuasicoherent :=
  isQuasicoherent_zero Y

/-- The zero `𝒪_Y`-module is of finite type. -/
instance isFiniteType_zeroModule : (0 : Y.Modules).IsFiniteType :=
  (AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
    (Stacks.SheafOfModules.isCoherent_of_isZero (isZero_zero Y.Modules))).isFiniteType

/-- A coherent `𝒪_Y`-module is quasi-coherent. -/
instance isQuasicoherent_coherentModules
    (A : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf) : A.obj.IsQuasicoherent :=
  haveI := AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent A.property
  isQuasicoherent_of_isCoherent _

/-- A coherent `𝒪_Y`-module is of finite type. -/
instance isFiniteType_coherentModules
    (A : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf) : A.obj.IsFiniteType :=
  A.property.isFiniteType

/-- The zero module is supported in every set. -/
theorem supp_zero_subset (T : Set Y) : SheafOfModules.supp (0 : Y.Modules) ⊆ T := fun x hx =>
  (Set.ext_iff.1 (SheafOfModules.supp_eq_empty_of_isZero (isZero_zero Y.Modules)) x).1 hx |>.elim

section DerivedSquares

variable (F : Y.Modules) [F.IsQuasicoherent]

/-- **The derived tensor square `Lⱼ T(F)`** of a quasi-coherent module: the derived sheaf of
`T ∘ right` at the arrow `0 → F`; its sections over an affine open `U` are
`Tor_j(Γ(F, U), Γ(F, U))`. -/
def derivedTensorSquareSheaf (j : ℕ) : Y.Modules :=
  (tensor right right).derivedSheaf (0 : (0 : Y.Modules) ⟶ F) hasFlatBaseChange_tensorSquareRight j

/-- **The derived exterior square `Lⱼ Λ²(F)`** of a quasi-coherent module: the derived sheaf of
`Λ² ∘ right` at the arrow `0 → F`; its sections over an affine open `U` are the derived exterior
squares of `Γ(F, U)`. -/
def derivedExteriorSquareSheaf (j : ℕ) : Y.Modules :=
  (exteriorPower 2 right).derivedSheaf (0 : (0 : Y.Modules) ⟶ F)
    hasFlatBaseChange_exteriorSquareRight j

/-- `Lⱼ T(F)` is coherent for `F` coherent on a locally Noetherian scheme. -/
theorem isCoherent_derivedTensorSquareSheaf [IsLocallyNoetherian Y] [F.IsFiniteType] (j : ℕ) :
    _root_.SheafOfModules.IsCoherent (derivedTensorSquareSheaf F j) :=
  isCoherent_derivedSheaf_of_preservesFinite _ preservesFinite_tensorSquareRight _ j

/-- `Lⱼ Λ²(F)` is coherent for `F` coherent on a locally Noetherian scheme. -/
theorem isCoherent_derivedExteriorSquareSheaf [IsLocallyNoetherian Y] [F.IsFiniteType] (j : ℕ) :
    _root_.SheafOfModules.IsCoherent (derivedExteriorSquareSheaf F j) :=
  isCoherent_derivedSheaf_of_preservesFinite _ preservesFinite_exteriorSquareRight _ j

/-- `Lⱼ T(F)` is supported in `supp F`. -/
theorem supp_derivedTensorSquareSheaf_subset (j : ℕ) :
    SheafOfModules.supp (derivedTensorSquareSheaf F j) ⊆ SheafOfModules.supp F :=
  supp_derivedSheaf_subset_of_vanishesOnZero _ vanishesOnZero_tensorSquareRight _ j
    (supp_zero_subset _) le_rfl

/-- `Lⱼ Λ²(F)` is supported in `supp F`. -/
theorem supp_derivedExteriorSquareSheaf_subset (j : ℕ) :
    SheafOfModules.supp (derivedExteriorSquareSheaf F j) ⊆ SheafOfModules.supp F :=
  supp_derivedSheaf_subset_of_vanishesOnZero _ vanishesOnZero_exteriorSquareRight _ j
    (supp_zero_subset _) le_rfl

/-- **Vanishing in large degrees.** On a regular quasi-compact scheme, the derived squares of a
quasi-coherent module of finite type vanish in large degrees: `Y` is covered by finitely many
affine opens `U` with regular ring of sections, over which `Γ(F, U)` has finite projective
dimension `d_U`, and `Lⱼ T` and `Lⱼ Λ²` vanish there for `j > 2 d_U`. -/
theorem exists_isZero_derivedTensorSquareSheaf (hY : IsRegular Y) [CompactSpace Y]
    [F.IsFiniteType] :
    ∃ N : ℕ, ∀ j, N < j → IsZero (derivedTensorSquareSheaf F j) ∧
      IsZero (derivedExteriorSquareSheaf F j) := by
  choose U hyU hreg using hY
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => ((U y : Y.Opens) : Set Y))
    (fun y => (U y).1.2) (fun y _ => Set.mem_iUnion.2 ⟨y, hyU y⟩)
  have hd : ∀ y, ∃ d : ℕ, HasProjectiveDimensionLE (ModuleCat.of Γ(Y, U y) Γ(F, U y)) d := by
    intro y
    have := hreg y
    have := AlgebraicGeometry.CoherentFinite.finite_sections F (U y).2
    exact StacksDraft.Perfect.exists_hasProjectiveDimensionLE _
  choose d hd using hd
  refine ⟨2 * t.sup d, fun j hj => ?_⟩
  have hcov : ∀ y : Y, ∃ i : t, y ∈ ((U i : Y.affineOpens) : Y.Opens) := fun y => by
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, hyi⟩
  have hle : ∀ i : t, 2 * d i < j := fun i =>
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Finset.le_sup (f := d) i.2)) hj
  exact ⟨isZero_derivedSheaf_of_cover _ _ j (fun i : t => U i) hcov fun i =>
      isZero_derivedHomology_tensor_right (hd i) _ (by have := hle i; omega),
    isZero_derivedSheaf_of_cover _ _ j (fun i : t => U i) hcov fun i =>
      isZero_derivedHomology_exteriorSquare_right (hd i) _ (hle i)⟩

/-- The least `N` past which the derived squares of `F` vanish (`0` if there is none). -/
def secondAdamsBound : ℕ :=
  sInf {N | ∀ j, N < j → IsZero (derivedTensorSquareSheaf F j) ∧
    IsZero (derivedExteriorSquareSheaf F j)}

/-- On a regular quasi-compact scheme the derived squares of `F` vanish past
`Stacks.Chow.secondAdamsBound`. -/
theorem isZero_of_secondAdamsBound_lt (hY : IsRegular Y) [CompactSpace Y] [F.IsFiniteType]
    {j : ℕ} (hj : secondAdamsBound F < j) :
    IsZero (derivedTensorSquareSheaf F j) ∧ IsZero (derivedExteriorSquareSheaf F j) :=
  Nat.sInf_mem (exists_isZero_derivedTensorSquareSheaf F hY) j hj

end DerivedSquares

/-! ### Classes of derived sheaves in `K₀(Coh_W(Y))` -/

variable [IsLocallyNoetherian Y] (W : Closeds Y)

section DerivedClass

variable {Φ : SemilinearArrowFunctor.{u}} (hΦ : Φ.HasFlatBaseChange) (hfin : Φ.PreservesFinite)
  (hzero : Φ.VanishesOnZero) {F' F : Y.Modules} [F'.IsQuasicoherent] [F.IsQuasicoherent]
  [F'.IsFiniteType] [F.IsFiniteType] (f : F' ⟶ F) (hF' : SheafOfModules.supp F' ⊆ W)
  (hF : SheafOfModules.supp F ⊆ W)

/-- The class `[Lⱼ Φ(f)]` in `K₀(Coh_W(Y))` of a derived sheaf of a morphism of quasi-coherent
modules of finite type supported in `W`, for `Φ` preserving finiteness and vanishing on zero
arrows. -/
def derivedSheafClass (j : ℕ) : supportedCoherentKZero W :=
  KZero.mk _ (coherentSupportedInMk (Φ.derivedSheaf f hΦ j)
    (isCoherent_derivedSheaf_of_preservesFinite hΦ hfin f j)
    (supp_derivedSheaf_subset_of_vanishesOnZero hΦ hzero f j hF' hF))

/-- The alternating sum `Σ_{j ≤ N} (-1)ʲ [Lⱼ Φ(f)]` in `K₀(Coh_W(Y))`. -/
def derivedSheafEulerClass (N : ℕ) : supportedCoherentKZero W :=
  ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ j • derivedSheafClass W hΦ hfin hzero f hF' hF j

variable {W hΦ hfin hzero f hF' hF}

/-- The class of a zero derived sheaf vanishes. -/
theorem derivedSheafClass_eq_zero {j : ℕ} (h : IsZero (Φ.derivedSheaf f hΦ j)) :
    derivedSheafClass W hΦ hfin hzero f hF' hF j = 0 :=
  supportedCoherentKZero_mk_eq_zero _ h

/-- Isomorphic derived sheaves have the same class. -/
theorem derivedSheafClass_eq_of_iso {Ψ : SemilinearArrowFunctor.{u}} {hΨ : Ψ.HasFlatBaseChange}
    {hfin' : Ψ.PreservesFinite} {hzero' : Ψ.VanishesOnZero} {G' G : Y.Modules}
    [G'.IsQuasicoherent] [G.IsQuasicoherent] [G'.IsFiniteType] [G.IsFiniteType] {g : G' ⟶ G}
    {hG' : SheafOfModules.supp G' ⊆ W} {hG : SheafOfModules.supp G ⊆ W} {j k : ℕ}
    (e : Φ.derivedSheaf f hΦ j ≅ Ψ.derivedSheaf g hΨ k) :
    derivedSheafClass W hΦ hfin hzero f hF' hF j = derivedSheafClass W hΨ hfin' hzero' g hG' hG k :=
  supportedCoherentKZero_mk_eq_of_iso _ _ e

/-- Degreewise isomorphic derived sheaves have the same alternating sums. -/
theorem derivedSheafEulerClass_eq_of_iso {Ψ : SemilinearArrowFunctor.{u}}
    {hΨ : Ψ.HasFlatBaseChange} {hfin' : Ψ.PreservesFinite} {hzero' : Ψ.VanishesOnZero}
    {G' G : Y.Modules} [G'.IsQuasicoherent] [G.IsQuasicoherent] [G'.IsFiniteType]
    [G.IsFiniteType] {g : G' ⟶ G} {hG' : SheafOfModules.supp G' ⊆ W}
    {hG : SheafOfModules.supp G ⊆ W} (N : ℕ)
    (e : ∀ j, Φ.derivedSheaf f hΦ j ≅ Ψ.derivedSheaf g hΨ j) :
    derivedSheafEulerClass W hΦ hfin hzero f hF' hF N =
      derivedSheafEulerClass W hΨ hfin' hzero' g hG' hG N :=
  Finset.sum_congr rfl fun j _ => by rw [derivedSheafClass_eq_of_iso (e j)]

end DerivedClass

/-- **The Euler relation of a glued long exact sequence.** For a short exact sequence
`0 → Φ₁ → Φ₂ → Φ₃ → 0` of semilinear functors and a morphism `f` of quasi-coherent modules of
finite type supported in `W` with `L_{N+1} Φ₃(f) = 0`,
`Σ_{j ≤ N} (-1)ʲ [Lⱼ Φ₂(f)] = Σ_{j ≤ N} (-1)ʲ [Lⱼ Φ₁(f)] + Σ_{j ≤ N} (-1)ʲ [Lⱼ Φ₃(f)]`. -/
theorem derivedSheafEulerClass_eq_add {Φ₁ Φ₂ Φ₃ : SemilinearArrowFunctor.{u}} {α : Φ₁ ⟶ Φ₂}
    {β : Φ₂ ⟶ Φ₃} (h : ShortExact α β) (hΦ₁ : Φ₁.HasFlatBaseChange)
    (hΦ₂ : Φ₂.HasFlatBaseChange) (hΦ₃ : Φ₃.HasFlatBaseChange) (hfin₁ : Φ₁.PreservesFinite)
    (hfin₂ : Φ₂.PreservesFinite) (hfin₃ : Φ₃.PreservesFinite) (hzero₁ : Φ₁.VanishesOnZero)
    (hzero₂ : Φ₂.VanishesOnZero) (hzero₃ : Φ₃.VanishesOnZero) {F' F : Y.Modules}
    [F'.IsQuasicoherent] [F.IsQuasicoherent] [F'.IsFiniteType] [F.IsFiniteType] (f : F' ⟶ F)
    (hF' : SheafOfModules.supp F' ⊆ W) (hF : SheafOfModules.supp F ⊆ W) (N : ℕ)
    (hN : IsZero (Φ₃.derivedSheaf f hΦ₃ (N + 1))) :
    derivedSheafEulerClass W hΦ₂ hfin₂ hzero₂ f hF' hF N =
      derivedSheafEulerClass W hΦ₁ hfin₁ hzero₁ f hF' hF N +
        derivedSheafEulerClass W hΦ₃ hfin₃ hzero₃ f hF' hF N := by
  have h0 := sum_range_neg_one_pow_zsmul_derivedSheaf_eq_zero f h hΦ₁ hΦ₂ hΦ₃
    (fun Φ hΦ j A hA X h₀ h₁ P => by
      have key : Φ.PreservesFinite := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hΦ
        rcases hΦ with rfl | rfl | rfl <;> assumption
      have := hA
      have := h₀
      have := h₁
      exact finite_derivedHomology (A := A) key P j)
    (fun Φ hΦ j A X h₀ h₁ P => by
      have key : Φ.VanishesOnZero := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hΦ
        rcases hΦ with rfl | rfl | rfl <;> assumption
      exact isZero_derivedHomology_of_vanishesOnZero key h₀ h₁ P j)
    hF' hF N hN
  have : derivedSheafEulerClass W hΦ₁ hfin₁ hzero₁ f hF' hF N -
      derivedSheafEulerClass W hΦ₂ hfin₂ hzero₂ f hF' hF N +
      derivedSheafEulerClass W hΦ₃ hfin₃ hzero₃ f hF' hF N = 0 := by
    rw [derivedSheafEulerClass, derivedSheafEulerClass, derivedSheafEulerClass,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h0
    rw [← smul_sub, ← smul_add]
    rfl
  refine sub_eq_zero.1 ?_
  rw [← neg_eq_zero, ← this]
  abel

/-! ### The second Adams sum and its additivity -/

/-- **The second Adams sum** `Σ_{j ≤ N} (-1)ʲ ([Lⱼ T(F)] - 2 [Lⱼ Λ²(F)])` in `K₀(Coh_W(Y))` of a
quasi-coherent module of finite type supported in `W`. -/
def secondAdamsSum (F : Y.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hF : SheafOfModules.supp F ⊆ W) (N : ℕ) : supportedCoherentKZero W :=
  ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ j •
    (derivedSheafClass W hasFlatBaseChange_tensorSquareRight preservesFinite_tensorSquareRight
        vanishesOnZero_tensorSquareRight (0 : (0 : Y.Modules) ⟶ F) (supp_zero_subset _) hF j -
      2 • derivedSheafClass W hasFlatBaseChange_exteriorSquareRight
        preservesFinite_exteriorSquareRight vanishesOnZero_exteriorSquareRight
        (0 : (0 : Y.Modules) ⟶ F) (supp_zero_subset _) hF j)

/-- The second Adams sum is the difference of the alternating sums of `[Lⱼ T(F)]` and of twice
`[Lⱼ Λ²(F)]`. -/
theorem secondAdamsSum_eq_derivedSheafEulerClass (F : Y.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (hF : SheafOfModules.supp F ⊆ W) (N : ℕ) :
    secondAdamsSum W F hF N =
      derivedSheafEulerClass W hasFlatBaseChange_tensorSquareRight
          preservesFinite_tensorSquareRight vanishesOnZero_tensorSquareRight
          (0 : (0 : Y.Modules) ⟶ F) (supp_zero_subset _) hF N -
        2 • derivedSheafEulerClass W hasFlatBaseChange_exteriorSquareRight
          preservesFinite_exteriorSquareRight vanishesOnZero_exteriorSquareRight
          (0 : (0 : Y.Modules) ⟶ F) (supp_zero_subset _) hF N := by
  rw [secondAdamsSum, derivedSheafEulerClass, derivedSheafEulerClass, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_sub, smul_comm]

variable {W}

/-- The second Adams sum does not change past the degrees in which the derived squares
vanish. -/
theorem secondAdamsSum_eq_of_le (F : Y.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hF : SheafOfModules.supp F ⊆ W) {N : ℕ}
    (hN : ∀ j, N < j → IsZero (derivedTensorSquareSheaf F j) ∧
      IsZero (derivedExteriorSquareSheaf F j))
    {M : ℕ} (hM : N ≤ M) : secondAdamsSum W F hF M = secondAdamsSum W F hF N := by
  induction M, hM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    rw [← ih, secondAdamsSum, Finset.sum_range_succ, ← secondAdamsSum,
      derivedSheafClass_eq_zero (hN (M + 1) (by omega)).1,
      derivedSheafClass_eq_zero (hN (M + 1) (by omega)).2, smul_zero, sub_zero, smul_zero,
      add_zero]

/-- **Additivity of the second Adams sum.** For a short exact sequence `0 → F' → F → F'' → 0` of
quasi-coherent modules of finite type supported in `W` whose derived squares vanish past `N`,
`ψ(F) = ψ(F') + ψ(F'')` for the sums up to `N + 1`. -/
theorem secondAdamsSum_add {F' F F'' : Y.Modules} [F'.IsQuasicoherent] [F.IsQuasicoherent]
    [F''.IsQuasicoherent] [F'.IsFiniteType] [F.IsFiniteType] [F''.IsFiniteType]
    (u : F' ⟶ F) (v : F ⟶ F'') (huv : u ≫ v = 0) (hS : (ShortComplex.mk u v huv).ShortExact)
    (hF' : SheafOfModules.supp F' ⊆ W) (hF : SheafOfModules.supp F ⊆ W)
    (hF'' : SheafOfModules.supp F'' ⊆ W) (N : ℕ)
    (hN' : ∀ j, N < j → IsZero (derivedTensorSquareSheaf F' j) ∧
      IsZero (derivedExteriorSquareSheaf F' j))
    (hN : ∀ j, N < j → IsZero (derivedTensorSquareSheaf F j) ∧
      IsZero (derivedExteriorSquareSheaf F j))
    (hN'' : ∀ j, N < j → IsZero (derivedTensorSquareSheaf F'' j) ∧
      IsZero (derivedExteriorSquareSheaf F'' j)) :
    secondAdamsSum W F hF (N + 1) =
      secondAdamsSum W F' hF' (N + 1) + secondAdamsSum W F'' hF'' (N + 1) := by
  have := hS.mono_f
  -- the functors, with flat base change, finiteness and vanishing on zero arrows
  have fL2 := hasFlatBaseChange_exteriorPower 2 hasFlatBaseChange_left.{u}
  have pL2 := preservesFinite_exteriorPower 2 preservesFinite_left.{u}
  have zL2 := vanishesOnZero_exteriorPower two_ne_zero vanishesOnZero_left.{u}
  have fR2 := hasFlatBaseChange_exteriorSquareRight.{u}
  have pR2 := preservesFinite_exteriorSquareRight.{u}
  have zR2 := vanishesOnZero_exteriorSquareRight.{u}
  have fC2 := hasFlatBaseChange_exteriorPower 2 hasFlatBaseChange_coker.{u}
  have pC2 := preservesFinite_exteriorPower 2 preservesFinite_coker.{u}
  have zC2 := vanishesOnZero_exteriorPower two_ne_zero vanishesOnZero_coker.{u}
  have fLT := hasFlatBaseChange_tensor hasFlatBaseChange_left.{u} hasFlatBaseChange_left
  have pLT := preservesFinite_tensor preservesFinite_left.{u} preservesFinite_left
  have zLT := vanishesOnZero_tensor_left vanishesOnZero_left.{u} left
  have fRT := hasFlatBaseChange_tensorSquareRight.{u}
  have pRT := preservesFinite_tensorSquareRight.{u}
  have zRT := vanishesOnZero_tensorSquareRight.{u}
  have fCT := hasFlatBaseChange_tensor hasFlatBaseChange_coker.{u} hasFlatBaseChange_coker
  have pCT := preservesFinite_tensor preservesFinite_coker.{u} preservesFinite_coker
  have zCT := vanishesOnZero_tensor_left vanishesOnZero_coker.{u} coker
  have fD2 := hasFlatBaseChange_relExteriorSquare.{u}
  have pD2 := preservesFinite_relExteriorSquare.{u}
  have zD2 := vanishesOnZero_relExteriorSquare.{u}
  have fDT := hasFlatBaseChange_relTensorSquare.{u}
  have pDT := preservesFinite_relTensorSquare.{u}
  have zDT := vanishesOnZero_relTensorSquare.{u}
  have fX := hasFlatBaseChange_cross.{u}
  have pX := preservesFinite_cross.{u}
  have zX := vanishesOnZero_cross.{u}
  have fXr := hasFlatBaseChange_crossRev.{u}
  have pXr := preservesFinite_crossRev.{u}
  have zXr := vanishesOnZero_crossRev.{u}
  have fS := hasFlatBaseChange_crossSum.{u}
  have pS := preservesFinite_crossSum.{u}
  have zS := vanishesOnZero_crossSum.{u}
  -- the five short exact sequences of functors
  have sA : ShortExact (exteriorPowerMap 2 leftToRight.{u})
      (cokernelπ (exteriorPowerMap 2 leftToRight)) :=
    ShortExact.mk' (fun A => comp_cokernelπ_app _ A) fun A P hP => shortExact_exteriorSquare A P hP
  have sB : ShortExact crossToRelExteriorSquare.{u} relExteriorSquareToCoker :=
    ShortExact.mk' crossToRelExteriorSquare_comp_relExteriorSquareToCoker_app
      fun A P hP => shortExact_relExteriorSquare A P hP
  have sC : ShortExact (tensorHom leftToRight.{u} leftToRight)
      (cokernelπ (tensorHom leftToRight leftToRight)) :=
    ShortExact.mk' (fun A => comp_cokernelπ_app _ A) fun A P hP => shortExact_tensorSquare A P hP
  have sD : ShortExact crossSumToRelTensorSquare.{u} relTensorSquareToCoker :=
    ShortExact.mk' crossSumToRelTensorSquare_comp_relTensorSquareToCoker_app
      fun A P hP => shortExact_relTensorSquare A P hP
  have sE : ShortExact (biprodInl (Φ := cross.{u}) (Ψ := crossRev)) biprodSnd :=
    shortExact_biprodInl_biprodSnd
  -- the comparison isomorphisms with the derived squares of `F'`, `F` and `F''`
  have wR : ∀ {G : Y.Modules} (b : G ⟶ F), (0 : (0 : Y.Modules) ⟶ G) ≫ b = 0 ≫ u := fun _ => by
    simp
  have eR : ∀ {Φ : SemilinearArrowFunctor.{u}} (hΦ : Φ.HasFlatBaseChange),
      (∀ j, IsIso (Φ.derivedSheafMapOfSquare hΦ 0 (𝟙 F) (wR (𝟙 F)) j)) →
      ∀ j, Φ.derivedSheaf (0 : (0 : Y.Modules) ⟶ F) hΦ j ≅ Φ.derivedSheaf u hΦ j :=
    fun {Φ} hΦ h j => haveI := h j; asIso (Φ.derivedSheafMapOfSquare hΦ 0 (𝟙 F) (wR (𝟙 F)) j)
  have w₁ : (0 : (0 : Y.Modules) ⟶ F') ≫ 𝟙 F' = 0 ≫ 𝟙 F' := by simp
  have eL : ∀ {Φ Ψ : SemilinearArrowFunctor.{u}} (α : Ψ ⟶ Φ) (hΨ : Ψ.HasFlatBaseChange)
      (hΦ : Φ.HasFlatBaseChange), (∀ j, IsIso (Φ.derivedSheafMapOfSquare hΦ 0 (𝟙 F') w₁ j)) →
      (∀ j, IsIso (derivedSheafMap (𝟙 F') α hΨ hΦ j)) →
      (∀ j, IsIso (Ψ.derivedSheafMapOfSquare hΨ (𝟙 F') u rfl j)) →
      ∀ j, Φ.derivedSheaf (0 : (0 : Y.Modules) ⟶ F') hΦ j ≅ Ψ.derivedSheaf u hΨ j :=
    fun {Φ Ψ} α hΨ hΦ h₁ h₂ h₃ j => haveI := h₁ j; haveI := h₂ j; haveI := h₃ j
      asIso (Φ.derivedSheafMapOfSquare hΦ 0 (𝟙 F') w₁ j) ≪≫
        (asIso (derivedSheafMap (𝟙 F') α hΨ hΦ j)).symm ≪≫
        asIso (Ψ.derivedSheafMapOfSquare hΨ (𝟙 F') u rfl j)
  have w₃ : u ≫ v = 0 ≫ (0 : (0 : Y.Modules) ⟶ F'') := huv.trans zero_comp.symm
  have eC : ∀ {Φ Ψ : SemilinearArrowFunctor.{u}} (α : Φ ⟶ Ψ) (hΦ : Φ.HasFlatBaseChange)
      (hΨ : Ψ.HasFlatBaseChange),
      (∀ j, IsIso (derivedSheafMap (0 : (0 : Y.Modules) ⟶ F'') α hΦ hΨ j)) →
      (∀ j, IsIso (Ψ.derivedSheafMapOfSquare hΨ 0 v w₃ j)) →
      ∀ j, Φ.derivedSheaf (0 : (0 : Y.Modules) ⟶ F'') hΦ j ≅ Ψ.derivedSheaf u hΨ j :=
    fun {Φ Ψ} α hΦ hΨ h₁ h₂ j => haveI := h₁ j; haveI := h₂ j
      asIso (derivedSheafMap (0 : (0 : Y.Modules) ⟶ F'') α hΦ hΨ j) ≪≫
        (asIso (Ψ.derivedSheafMapOfSquare hΨ 0 v w₃ j)).symm
  have eR2 := eR fR2 (isIso_derivedSheafMapOfSquare_exteriorPower_right 2 fR2 0 (𝟙 F) (wR (𝟙 F)))
  have eRT := eR fRT (isIso_derivedSheafMapOfSquare_tensor_right fRT 0 (𝟙 F) (wR (𝟙 F)))
  have eL2 := eL (exteriorPowerMap 2 leftToRight) fL2 fR2
    (isIso_derivedSheafMapOfSquare_exteriorPower_right 2 fR2 0 (𝟙 F') w₁)
    (isIso_derivedSheafMap_exteriorPowerMap_leftToRight 2 (𝟙 F') fL2 fR2)
    (isIso_derivedSheafMapOfSquare_exteriorPower_left 2 fL2 (𝟙 F') u rfl)
  have eLT := eL (tensorHom leftToRight leftToRight) fLT fRT
    (isIso_derivedSheafMapOfSquare_tensor_right fRT 0 (𝟙 F') w₁)
    (isIso_derivedSheafMap_tensorHom_leftToRight (𝟙 F') fLT fRT)
    (isIso_derivedSheafMapOfSquare_tensor_left fLT (𝟙 F') u rfl)
  have eC2 := eC (exteriorPowerMap 2 rightToCoker) fR2 fC2
    (isIso_derivedSheafMap_exteriorPowerMap_rightToCoker 2 _ (isZero_zero _) fR2 fC2)
    (isIso_derivedSheafMapOfSquare_exteriorPower_coker 2 fC2 u v huv hS _ (isZero_zero _) w₃)
  have eCT := eC (tensorHom rightToCoker rightToCoker) fRT fCT
    (isIso_derivedSheafMap_tensorHom_rightToCoker _ (isZero_zero _) fRT fCT)
    (isIso_derivedSheafMapOfSquare_tensor_coker fCT u v huv hS _ (isZero_zero _) w₃)
  have eXr : ∀ j, cross.derivedSheaf u fX j ≅ crossRev.derivedSheaf u fXr j := fun j =>
    have := isIso_derivedSheafMap_crossIsoCrossRev u fX fXr j
    asIso (derivedSheafMap u crossIsoCrossRev.hom fX fXr j)
  -- vanishing in degree `N + 2` of the third terms of the long exact sequences
  have vC2 : ∀ j, N < j → IsZero ((exteriorPower 2 coker).derivedSheaf u fC2 j) := fun j hj =>
    (hN'' j hj).2.of_iso (eC2 j).symm
  have vCT : ∀ j, N < j → IsZero ((tensor coker coker).derivedSheaf u fCT j) := fun j hj =>
    (hN'' j hj).1.of_iso (eCT j).symm
  have vD2 : IsZero (relExteriorSquare.derivedSheaf u fD2 (N + 2)) :=
    (exact_derivedSheafMap_derivedSheafδ u sA fL2 fR2 fD2 (N + 1)).isZero_X₂
      (((hN (N + 2) (by omega)).2.of_iso (eR2 (N + 2)).symm).eq_of_src _ _)
      (((hN' (N + 1) (by omega)).2.of_iso (eL2 (N + 1)).symm).eq_of_tgt _ _)
  have vDT : IsZero (relTensorSquare.derivedSheaf u fDT (N + 2)) :=
    (exact_derivedSheafMap_derivedSheafδ u sC fLT fRT fDT (N + 1)).isZero_X₂
      (((hN (N + 2) (by omega)).1.of_iso (eRT (N + 2)).symm).eq_of_src _ _)
      (((hN' (N + 1) (by omega)).1.of_iso (eLT (N + 1)).symm).eq_of_tgt _ _)
  have vX : IsZero (cross.derivedSheaf u fX (N + 2)) :=
    (exact_derivedSheafδ_derivedSheafMap u sB fX fD2 fC2 (N + 2)).isZero_X₂
      ((vC2 (N + 2 + 1) (by omega)).eq_of_src _ _) (vD2.eq_of_tgt _ _)
  have vXr : IsZero (crossRev.derivedSheaf u fXr (N + 2)) := vX.of_iso (eXr (N + 2)).symm
  -- the Euler relations of the five long exact sequences at `F' → F`
  have rA := derivedSheafEulerClass_eq_add W sA fL2 fR2 fD2 pL2 pR2 pD2 zL2 zR2 zD2 u hF' hF
    (N + 1) vD2
  have rB := derivedSheafEulerClass_eq_add W sB fX fD2 fC2 pX pD2 pC2 zX zD2 zC2 u hF' hF (N + 1)
    (vC2 (N + 2) (by omega))
  have rC := derivedSheafEulerClass_eq_add W sC fLT fRT fDT pLT pRT pDT zLT zRT zDT u hF' hF
    (N + 1) vDT
  have rD := derivedSheafEulerClass_eq_add W sD fS fDT fCT pS pDT pCT zS zDT zCT u hF' hF (N + 1)
    (vCT (N + 2) (by omega))
  have rE := derivedSheafEulerClass_eq_add W sE fX fS fXr pX pS pXr zX zS zXr u hF' hF (N + 1)
    vXr
  -- the identifications of the outer terms
  have iR2 := derivedSheafEulerClass_eq_of_iso (hfin := pR2) (hzero := zR2) (hfin' := pR2)
    (hzero' := zR2) (hF' := supp_zero_subset (W : Set Y)) (hF := hF) (hG' := hF') (hG := hF)
    (N + 1) eR2
  have iRT := derivedSheafEulerClass_eq_of_iso (hfin := pRT) (hzero := zRT) (hfin' := pRT)
    (hzero' := zRT) (hF' := supp_zero_subset (W : Set Y)) (hF := hF) (hG' := hF') (hG := hF)
    (N + 1) eRT
  have iL2 := derivedSheafEulerClass_eq_of_iso (hfin := pR2) (hzero := zR2) (hfin' := pL2)
    (hzero' := zL2) (hF' := supp_zero_subset (W : Set Y)) (hF := hF') (hG' := hF') (hG := hF)
    (N + 1) eL2
  have iLT := derivedSheafEulerClass_eq_of_iso (hfin := pRT) (hzero := zRT) (hfin' := pLT)
    (hzero' := zLT) (hF' := supp_zero_subset (W : Set Y)) (hF := hF') (hG' := hF') (hG := hF)
    (N + 1) eLT
  have iC2 := derivedSheafEulerClass_eq_of_iso (hfin := pR2) (hzero := zR2) (hfin' := pC2)
    (hzero' := zC2) (hF' := supp_zero_subset (W : Set Y)) (hF := hF'') (hG' := hF') (hG := hF)
    (N + 1) eC2
  have iCT := derivedSheafEulerClass_eq_of_iso (hfin := pRT) (hzero := zRT) (hfin' := pCT)
    (hzero' := zCT) (hF' := supp_zero_subset (W : Set Y)) (hF := hF'') (hG' := hF') (hG := hF)
    (N + 1) eCT
  have iXr := derivedSheafEulerClass_eq_of_iso (hfin := pX) (hzero := zX) (hfin' := pXr)
    (hzero' := zXr) (hF' := hF') (hF := hF) (hG' := hF') (hG := hF) (N + 1) eXr
  rw [secondAdamsSum_eq_derivedSheafEulerClass, secondAdamsSum_eq_derivedSheafEulerClass,
    secondAdamsSum_eq_derivedSheafEulerClass, iR2, iRT, iL2, iLT, iC2, iCT, rC, rD, rE, ← iXr,
    rA, rB]
  abel

/-- The second Adams sums for `W' ⊆ W` agree under the map induced by the inclusion. -/
theorem supportedCoherentKZeroMap_secondAdamsSum {W' : Closeds Y} (h : W' ≤ W) (F : Y.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (hF : SheafOfModules.supp F ⊆ W') (N : ℕ) :
    supportedCoherentKZeroMap h (secondAdamsSum W' F hF N) =
      secondAdamsSum W F (hF.trans h) N := by
  simp only [secondAdamsSum, map_sum, map_zsmul, map_sub, map_nsmul, derivedSheafClass,
    supportedCoherentKZeroMap_mk]
  rfl

/-! ### The leading term of the second Adams sum -/

/-- **The leading term of the second Adams sum at a point.** Let `F` be a quasi-coherent module of
finite type supported in `W`, on which the relative dimension is at most `k`, and let `y` have
relative dimension `k` and local ring of dimension `n`. For `N ≥ 2n` the coefficient at `y` of the
`k`-cycle of the second Adams sum of `F` up to `N` is `2ⁿ` times the multiplicity of `F` at `y`. -/
theorem cycleCoeffHom_supportedCoherentKZeroCycle_secondAdamsSum (C : ChowSituation.{u})
    (a : Y ⟶ C.S) [LocallyOfFiniteType a] (hY : IsRegular Y) (W : Closeds Y) (k : ℤ)
    (hW : ∀ z ∈ W, relativeDimension C.dimensionFunction a z ≤ k)
    (F : Y.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (hF : SheafOfModules.supp F ⊆ W)
    {y : Y} (hy : relativeDimension C.dimensionFunction a y = k) {n : ℕ}
    (hn : ringKrullDim (Y.presheaf.stalk y) = (n : ℕ∞)) {N : ℕ} (hN : 2 * n ≤ N) :
    cycleCoeffHom C a k y (supportedCoherentKZeroCycle C a W k hW (secondAdamsSum W F hF N)) =
      2 ^ n * (sheafMultiplicity F y : ℤ) := by
  obtain ⟨V, hV, hyV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  let U : Y.affineOpens := ⟨V, hV⟩
  set 𝔭 := (U.2.primeIdealOf ⟨y, hyV⟩).asIdeal
  let R := CommRingCat.of (Localization.AtPrime 𝔭)
  -- the localized arrow `0 → Γ(F, U)_𝔭` and a resolution of it
  let X := (extendScalarsArrow (algebraMap Γ(Y, U) (Localization.AtPrime 𝔭))).obj
    (arrowSections (0 : (0 : Y.Modules) ⟶ F) U)
  let Q : SimplicialProjectiveResolution X := Classical.arbitrary _
  -- the multiplicities of the derived squares at `y` are lengths of derived modules at `X`
  have hT : ∀ j, sheafMultiplicity (derivedTensorSquareSheaf F j) y =
      (Module.length R (Q.derivedHomology (D := ModuleCat.{u} R) ((tensor right right).obj R)
        j)).toNat := fun j =>
    sheafMultiplicity_derivedSheaf_eq_length_extendScalarsArrow _ _ j U hyV Q
  have hΛ : ∀ j, sheafMultiplicity (derivedExteriorSquareSheaf F j) y =
      (Module.length R (Q.derivedHomology (D := ModuleCat.{u} R) ((exteriorPower 2 right).obj R)
        j)).toNat := fun j =>
    sheafMultiplicity_derivedSheaf_eq_length_extendScalarsArrow _ _ j U hyV Q
  -- `Γ(Y, U)_𝔭` is the local ring at `y`: regular, of dimension `n`
  obtain ⟨_, hR⟩ : IsRegularLocalRing R ∧ ringKrullDim R = n := by
    let := Y.presheaf.algebra_section_stalk ⟨y, hyV⟩
    have : IsLocalization.AtPrime (Y.presheaf.stalk y) 𝔭 := U.2.isLocalization_stalk ⟨y, hyV⟩
    let e : Localization.AtPrime 𝔭 ≃+* Y.presheaf.stalk y :=
      (IsLocalization.algEquiv 𝔭.primeCompl (Localization.AtPrime 𝔭)
        (Y.presheaf.stalk y)).toRingEquiv
    have := IsRegular.isRegularLocalRing_stalk hY y
    exact ⟨IsRegularLocalRing.of_ringEquiv e.symm, (ringKrullDim_eq_of_ringEquiv e).trans hn⟩
  -- the length of `X₁ = Γ(F, U)_𝔭` is the length of the stalk `F_y`, which is finite
  have hlen : Module.length R X.right =
      Module.length (Y.presheaf.stalk y) (F.presheaf.stalk y) := by
    let φ := algebraMap Γ(Y, U) (Localization.AtPrime 𝔭)
    let M := ModuleCat.of Γ(Y, U) Γ(F, (U : Y.Opens))
    have hu : IsIso (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M
        ((ModuleCat.extendScalars φ).obj M)).symm
        ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M)) := by
      rw [Adjunction.homEquiv_symm_unit]
      infer_instance
    exact (Stacks.Modules.length_localizedModule_eq_of_isBaseChangeAlong 𝔭.primeCompl
      (T := Localization.AtPrime 𝔭) _ (@Stacks.Modules.isBaseChangeAlong_of_isIso _ _ _ _ φ _ _
        ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M) hu)).symm.trans
      (ModuleStalkSpecialization.length_stalk_eq_length_localizedModule F U.2 hyV).symm
  have hfl : IsFiniteLength R X.right := by
    rw [← Module.length_ne_top_iff, hlen, Module.length_ne_top_iff]
    exact isFiniteLength_stalk_of_forall_relativeDimension_le C a k F
      (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
        F) (fun z hz => hW z (hF hz)) hy
  -- the coefficient of the cycle of a derived class is the multiplicity of the derived sheaf
  have hcyc : ∀ {Φ : SemilinearArrowFunctor.{u}} (hΦ : Φ.HasFlatBaseChange)
      (hfin : Φ.PreservesFinite) (hzero : Φ.VanishesOnZero) (j : ℕ),
      cycleCoeffHom C a k y (supportedCoherentKZeroCycle C a W k hW
        (derivedSheafClass W hΦ hfin hzero (0 : (0 : Y.Modules) ⟶ F) (supp_zero_subset _) hF
          j)) =
        sheafMultiplicity (Φ.derivedSheaf (0 : (0 : Y.Modules) ⟶ F) hΦ j) y :=
    fun _ _ _ _ => supportedCoherentKZeroCycle_mk_apply_of_eq C a W k hW _ hy
  rw [secondAdamsSum, map_sum, map_sum]
  simp only [map_zsmul, map_sub, map_nsmul, hcyc]
  change ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ j •
    ((sheafMultiplicity (derivedTensorSquareSheaf F j) y : ℤ) -
      2 • (sheafMultiplicity (derivedExteriorSquareSheaf F j) y : ℤ)) = _
  simp only [hT, hΛ]
  rw [sheafMultiplicity, ← hlen]
  exact sum_range_length_tensor_right_sub_two_mul_length_exteriorPower_right hR hfl Q hN

/-! ### The endomorphism `ψ_W` of `K₀(Coh_W(Y))` and its naturality -/

variable [CompactSpace Y]

/-- The second Adams sum taken past the bound `Stacks.Chow.secondAdamsBound` is the sum up to
the bound. -/
theorem secondAdamsSum_eq_of_secondAdamsBound_le (hY : IsRegular Y) (F : Y.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (hF : SheafOfModules.supp F ⊆ W) {M : ℕ}
    (hM : secondAdamsBound F ≤ M) :
    secondAdamsSum W F hF M = secondAdamsSum W F hF (secondAdamsBound F) :=
  secondAdamsSum_eq_of_le F hF (fun _ hj => isZero_of_secondAdamsBound_lt F hY hj) hM

/-- **The second Adams operation `ψ_W` on `K₀(Coh_W(Y))`** for a regular quasi-compact locally
Noetherian scheme `Y` and a closed subset `W`: the class of a coherent module `F` supported in
`W` goes to `Σ_{j ≤ N} (-1)ʲ ([Lⱼ T(F)] - 2 [Lⱼ Λ²(F)])`, for `N` past the vanishing of the derived
squares. -/
def supportedSecondAdams (hY : IsRegular Y) (W : Closeds Y) :
    supportedCoherentKZero W →+ supportedCoherentKZero W :=
  KZero.lift (fun A => secondAdamsSum W A.obj.obj A.property (secondAdamsBound A.obj.obj))
    fun S hS => by
      have hS' := (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf).shortExact_map_ι
        ((coherentSupportedIn (W : Set Y)).shortExact_map_ι hS)
      obtain ⟨N, h₁, h₂, h₃⟩ : ∃ N, secondAdamsBound S.X₁.obj.obj ≤ N ∧
          secondAdamsBound S.X₂.obj.obj ≤ N ∧ secondAdamsBound S.X₃.obj.obj ≤ N :=
        ⟨_, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
          (le_max_right _ _).trans (le_max_right _ _)⟩
      have e₁ := secondAdamsSum_eq_of_secondAdamsBound_le hY S.X₁.obj.obj S.X₁.property
        (M := N + 1) (by omega)
      have e₂ := secondAdamsSum_eq_of_secondAdamsBound_le hY S.X₂.obj.obj S.X₂.property
        (M := N + 1) (by omega)
      have e₃ := secondAdamsSum_eq_of_secondAdamsBound_le hY S.X₃.obj.obj S.X₃.property
        (M := N + 1) (by omega)
      rw [← e₁, ← e₂, ← e₃]
      exact secondAdamsSum_add (F' := S.X₁.obj.obj) (F := S.X₂.obj.obj) (F'' := S.X₃.obj.obj)
        _ _ _ hS' _ _ _ N
        (fun j hj => isZero_of_secondAdamsBound_lt _ hY (by omega))
        (fun j hj => isZero_of_secondAdamsBound_lt _ hY (by omega))
        (fun j hj => isZero_of_secondAdamsBound_lt _ hY (by omega))

/-- The value of `ψ_W` on a class, with the bound `Stacks.Chow.secondAdamsBound`. -/
theorem supportedSecondAdams_mk (hY : IsRegular Y)
    (A : (coherentSupportedIn (W : Set Y)).FullSubcategory) :
    supportedSecondAdams hY W (KZero.mk _ A) =
      secondAdamsSum W A.obj.obj A.property (secondAdamsBound A.obj.obj) :=
  KZero.lift_mk _ _ _

/-- **The value of `ψ_W` on a class** `[F]`: the second Adams sum up to any `N` past which the
derived squares of `F` vanish. -/
theorem supportedSecondAdams_mk_eq_secondAdamsSum (hY : IsRegular Y)
    (A : (coherentSupportedIn (W : Set Y)).FullSubcategory) {N : ℕ}
    (hN : ∀ j, N < j → IsZero (derivedTensorSquareSheaf A.obj.obj j) ∧
      IsZero (derivedExteriorSquareSheaf A.obj.obj j)) :
    supportedSecondAdams hY W (KZero.mk _ A) = secondAdamsSum W A.obj.obj A.property N := by
  rw [supportedSecondAdams_mk hY]
  exact (secondAdamsSum_eq_of_secondAdamsBound_le hY A.obj.obj A.property
    (le_max_left (secondAdamsBound A.obj.obj) N)).symm.trans
      (secondAdamsSum_eq_of_le A.obj.obj A.property hN (le_max_right _ _))

/-- **The value of `ψ_W` on a class** `[F]`: the second Adams sum up to any `N` past the bound
`Stacks.Chow.secondAdamsBound`. -/
theorem supportedSecondAdams_mk_eq_secondAdamsSum_of_le (hY : IsRegular Y)
    (A : (coherentSupportedIn (W : Set Y)).FullSubcategory) {N : ℕ}
    (hN : secondAdamsBound A.obj.obj ≤ N) :
    supportedSecondAdams hY W (KZero.mk _ A) = secondAdamsSum W A.obj.obj A.property N :=
  supportedSecondAdams_mk_eq_secondAdamsSum hY A fun _ hj =>
    isZero_of_secondAdamsBound_lt _ hY (by omega)

/-- **Naturality of `ψ_W`**: it commutes with the maps induced by inclusions `W' ⊆ W`. -/
theorem supportedSecondAdams_comp_supportedCoherentKZeroMap (hY : IsRegular Y) {W' : Closeds Y}
    (h : W' ≤ W) :
    (supportedSecondAdams hY W).comp (supportedCoherentKZeroMap h) =
      (supportedCoherentKZeroMap h).comp (supportedSecondAdams hY W') :=
  KZero.hom_ext fun A => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, supportedCoherentKZeroMap_mk,
      supportedSecondAdams_mk hY, supportedSecondAdams_mk hY]
    exact (supportedCoherentKZeroMap_secondAdamsSum h A.obj.obj A.property _).symm

variable (Y) in
/-- **The second Adams operation `ψ` on `W ↦ 𝐐 ⊗ K₀(Coh_W(Y))`**, the natural endomorphism
`𝐐 ⊗ ψ_W`. -/
def supportedSecondAdamsRat (hY : IsRegular Y) :
    supportedCoherentKZeroRat Y ⟶ supportedCoherentKZeroRat Y where
  app W := ModuleCat.ofHom ((supportedSecondAdams hY W).toIntLinearMap.baseChange ℚ)
  naturality {W' W} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using TensorProduct.inductionOn with
    | tmul q a =>
      change q ⊗ₜ[ℤ] supportedSecondAdams hY W (supportedCoherentKZeroMap (leOfHom f) a) =
        q ⊗ₜ[ℤ] supportedCoherentKZeroMap (leOfHom f) (supportedSecondAdams hY W' a)
      rw [← AddMonoidHom.comp_apply, supportedSecondAdams_comp_supportedCoherentKZeroMap hY,
        AddMonoidHom.comp_apply]
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- `ψ` on a pure tensor. -/
theorem supportedSecondAdamsRat_app_tmul (hY : IsRegular Y) (q : ℚ)
    (a : supportedCoherentKZero W) :
    ((supportedSecondAdamsRat Y hY).app W).hom (q ⊗ₜ[ℤ] a) =
      q ⊗ₜ[ℤ] supportedSecondAdams hY W a :=
  rfl

/-! ### The leading term of `ψ` -/

variable (C : ChowSituation.{u}) (a : Y ⟶ C.S) [LocallyOfFiniteType a]

/-- **The leading term of `ψ_W`**, integrally: at a point `y` of relative dimension `k`, where
`k` bounds the relative dimension on `W`, with local ring of dimension `n`, the coefficient of
the `k`-cycle of `ψ_W b` is `2ⁿ` times that of `b`. -/
theorem cycleCoeffHom_supportedCoherentKZeroCycle_supportedSecondAdams (hY : IsRegular Y)
    (W : Closeds Y) (k : ℤ) (hW : ∀ z ∈ W, relativeDimension C.dimensionFunction a z ≤ k)
    (b : supportedCoherentKZero W) {y : Y} (hy : relativeDimension C.dimensionFunction a y = k)
    {n : ℕ} (hn : ringKrullDim (Y.presheaf.stalk y) = (n : ℕ∞)) :
    cycleCoeffHom C a k y (supportedCoherentKZeroCycle C a W k hW (supportedSecondAdams hY W b)) =
      2 ^ n * cycleCoeffHom C a k y (supportedCoherentKZeroCycle C a W k hW b) := by
  have h : (cycleCoeffHom C a k y).comp ((supportedCoherentKZeroCycle C a W k hW).comp
      (supportedSecondAdams hY W)) =
      (2 ^ n : ℤ) • (cycleCoeffHom C a k y).comp (supportedCoherentKZeroCycle C a W k hW) :=
    KZero.hom_ext fun A => by
      have e₁ := supportedSecondAdams_mk_eq_secondAdamsSum_of_le hY A
        (le_max_left (secondAdamsBound A.obj.obj) (2 * n))
      have e₂ := cycleCoeffHom_supportedCoherentKZeroCycle_secondAdamsSum C a hY W k hW A.obj.obj
        A.property hy hn (le_max_right (secondAdamsBound A.obj.obj) (2 * n))
      have e₃ := supportedCoherentKZeroCycle_mk_apply_of_eq C a W k hW A hy
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, smul_eq_mul, e₁, e₂,
        cycleCoeffHom_apply, e₃]
  have := DFunLike.congr_fun h b
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, smul_eq_mul] using this

/-- **The leading term of `ψ`.** Let `W` be a closed subset of `Y` on which the relative dimension
over the base is at most `k`, and let `y` be a point of relative dimension `k` whose local ring has
dimension `n`. Then for `x ∈ 𝐐 ⊗ K₀(Coh_W(Y))` the coefficient at `y` of the `k`-cycle of `ψ x` is
`2ⁿ` times that of `x`; the point `y` need not lie in `W`. This is the hypothesis of
`Stacks.Chow.injective_liftBaseChange_coherentChowCharacter_of_codimensionWeightOperator` with
`ℓ = 2`, for the identity of `Y`. -/
theorem rationalCycleCoeff_supportedCoherentKZeroRatCycle_supportedSecondAdamsRat
    (hY : IsRegular Y) (W : Closeds Y) (k : ℤ)
    (hW : ∀ z ∈ W, relativeDimension C.dimensionFunction a z ≤ k)
    (x : (supportedCoherentKZeroRat Y).obj W) (y : Y)
    (hy : relativeDimension C.dimensionFunction a y = k) (n : ℕ)
    (hn : ringKrullDim (Y.presheaf.stalk y) = (n : ℕ∞)) :
    rationalCycleCoeff C a k y
        (supportedCoherentKZeroRatCycle C a W k hW (((supportedSecondAdamsRat Y hY).app W).hom x)) =
      2 ^ n * rationalCycleCoeff C a k y (supportedCoherentKZeroRatCycle C a W k hW x) := by
  let G := (rationalCycleCoeff C a k y).comp (supportedCoherentKZeroRatCycle C a W k hW)
  change G (((supportedSecondAdamsRat Y hY).app W).hom x) = 2 ^ n * G x
  induction x using TensorProduct.inductionOn with
  | tmul q b =>
    have h := cycleCoeffHom_supportedCoherentKZeroCycle_supportedSecondAdams C a hY W k hW b hy
      hn
    rw [cycleCoeffHom_apply, cycleCoeffHom_apply] at h
    change rationalCycleCoeff C a k y (q ⊗ₜ[ℤ] supportedCoherentKZeroCycle C a W k hW
        (supportedSecondAdams hY W b)) =
      2 ^ n * rationalCycleCoeff C a k y (q ⊗ₜ[ℤ] supportedCoherentKZeroCycle C a W k hW b)
    rw [rationalCycleCoeff_tmul, rationalCycleCoeff_tmul, h]
    push_cast
    ring
  | add x x' hx hx' =>
    exact (congrArg G (map_add ((supportedSecondAdamsRat Y hY).app W).hom x x')).trans
      ((map_add G _ _).trans ((congrArg₂ (· + ·) hx hx').trans
        ((mul_add _ _ _).symm.trans (congrArg _ (map_add G x x').symm))))

end Stacks.Chow

end
