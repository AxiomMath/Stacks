module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIrreducibleIdealInjection
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSupportSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIdealMeet
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk

/-!
# A dévissage criterion for coherent modules on a Noetherian algebraic space

Stacks 07UT: on a Noetherian algebraic space `X`, a property `P` of coherent modules which is
closed under extensions, descends from finite direct sums of copies, and holds for the direct
images of enough subsheaves of one full-support coherent module on each reduced closed subspace
with irreducible space of points, holds for every coherent module — once it holds for the zero
module, which the source leaves out and cannot do without.

## Main definitions

* `AlgebraicGeometry.Space.HasGenericSubsheaves`: hypothesis (3) of Stacks 07UT.

## Main results

* `CategoryTheory.shortExact_cokernel_comp`: for a monomorphism `g`, the cokernels of `f`,
  `f ≫ g` and `g` form a short exact sequence.
* `AlgebraicGeometry.Space.exists_quasicoherentIdeal_ne_bot_le_annihilatorIdealSheaf`: on a
  Noetherian algebraic space a coherent module with support not everything is killed by a
  nonzero quasi-coherent sheaf of ideals.
* `AlgebraicGeometry.Space.property_idealPushforward_of_hasGenericSubsheaf`: the step at a
  reduced closed subspace with irreducible space of points: `P` holds for the direct image of
  every quasi-coherent sheaf of ideals on it.
* `AlgebraicGeometry.Space.property_of_isIrreducible`: the irreducible-support case.
* `AlgebraicGeometry.Space.property_of_isCoherent_of_hasGenericSubsheaves`: **Stacks 07UT**.
* `AlgebraicGeometry.Space.exists_hasGenericSubsheaves_not_forall`: the property "is nonzero"
  satisfies the source's three hypotheses and fails for the zero module.

## Implementation notes

The source compares a module `H` on `Z` with the module `𝒢` of hypothesis (3) through an
isomorphism `H^{⊕ r₂}|_V ≅ 𝒢^{⊕ r₁}|_V` over a dense open, extended by Stacks 07UM.  Here the
comparison is made through sheaves of ideals instead: Stacks 07UQ embeds `ℐ₂^{⊕ r}` into `𝒢` with
cokernel supported in a proper closed subset, so a nonzero quasi-coherent ideal `ℐ` kills that
cokernel (Stacks 07UK) and every `𝒢' ⊆ ℐ𝒢` embeds into `ℐ₂^{⊕ r}`.  This gives `P` for the direct
image of a nonzero sheaf of ideals on `Z` — first for one contained in `ℐ₂`, through hypothesis
(2), then for all of them — and Stacks 07UQ applied to the module on the scheme-theoretic
support carries it to the module itself, as in the source.

The direct sum `F^{⊕ r}` is the biproduct `⨁ fun _ : Fin r => F`.  The module universe is the
universe of the schemes, which is where the `𝒪_X`-modules form an abelian category.

## References

* [Stacks Project, Tag 07UT](https://stacks.math.columbia.edu/tag/07UT)
* [Stacks Project, Tag 07UP](https://stacks.math.columbia.edu/tag/07UP)
* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 07UK](https://stacks.math.columbia.edu/tag/07UK)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 04ZF](https://stacks.math.columbia.edu/tag/04ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Cokernels of a composite of monomorphisms -/

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

/-- **The cokernels of `f`, `f ≫ g` and `g` form a short exact sequence** when `g` is a
monomorphism: this is the tail `0 = ker g → coker f → coker (f ≫ g) → coker g → 0` of the
kernel–cokernel sequence of a composite. -/
theorem shortExact_cokernel_comp {A B D : C} (f : A ⟶ B) (g : B ⟶ D) [Mono g] :
    (ShortComplex.mk (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
      (cokernel.map (f ≫ g) g f (𝟙 _) (by simp)) (by ext; simp)).ShortExact := by
  have hE := kernelCokernelCompSequence_exact f g
  have h2 := hE.exact 2
  have h3 := hE.exact 3
  have hmono : Mono (cokernel.map f (f ≫ g) (𝟙 _) g (by simp)) :=
    h2.mono_g ((isZero_kernel_of_mono g).eq_of_src _ _)
  exact ShortComplex.ShortExact.mk' h3 hmono
    (inferInstanceAs (Epi ((kernelCokernelCompSequence f g).map' 4 5)))

/-- The inclusion of a monomorphism into its cokernel is a short exact sequence. -/
private theorem shortExact_mk_cokernel_condition {A B : C} (f : A ⟶ B) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **A property closed under extensions and isomorphisms and holding for zero objects holds for
every finite direct sum of copies of an object which has it**: the inclusion of the last summand
of `M^{⊕ (r + 1)}` has cokernel `M^{⊕ r}`. -/
theorem prop_biproductConst (Q : C → Prop) (zero : ∀ Z : C, IsZero Z → Q Z)
    (extension : ∀ T : ShortComplex C, T.ShortExact → Q T.X₁ → Q T.X₃ → Q T.X₂)
    (iso : ∀ {A A' : C}, (A ≅ A') → Q A → Q A') {M : C} (hM : Q M) :
    ∀ r : ℕ, Q (⨁ fun _ : Fin r => M)
  | 0 => zero _ ((IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun j => j.elim0))
  | r + 1 => by
    let ι := biproduct.ι (fun _ : Fin (r + 1) => M) (Fin.last r)
    let e : (⨁ fun _ : Fin r => M) ≅ cokernel ι :=
      biproduct.whiskerEquiv (finSuccAboveEquiv (Fin.last r)) (fun _ => Iso.refl M) ≪≫
        (cokernelBiproductιIso (fun _ : Fin (r + 1) => M) (Fin.last r)).symm
    refine extension (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)) ?_ hM
      (iso e (prop_biproductConst Q zero extension iso hM r))
    exact shortExact_mk_cokernel_condition ι

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Supports

variable (X : AlgebraicSpaces B S hS)

/-- The support of the cokernel of `f ≫ g`, for a monomorphism `g`, lies in the union of the
supports of the cokernels of `f` and of `g`. -/
theorem moduleSupportSet_cokernel_comp_subset {A M N : Modules.{u, u} B S hS X.1 X.2}
    (f : A ⟶ M) (g : M ⟶ N) [Mono g] :
    moduleSupportSet B S hS X (cokernel (C := Modules.{u, u} B S hS X.1 X.2) (f ≫ g)) ⊆
      moduleSupportSet B S hS X (cokernel (C := Modules.{u, u} B S hS X.1 X.2) f) ∪
        moduleSupportSet B S hS X (cokernel (C := Modules.{u, u} B S hS X.1 X.2) g) := by
  let _ := spaceModulesAbelian B S hS X
  have hE := shortExact_cokernel_comp f g
  have h := supportOfSheaf_middle_subset_union B S hS X _ hE
  exact h

/-- The support of the cokernel of `f` lies in that of the cokernel of `f ≫ g`, for a
monomorphism `g`. -/
theorem moduleSupportSet_cokernel_subset_cokernel_comp {A M N : Modules.{u, u} B S hS X.1 X.2}
    (f : A ⟶ M) (g : M ⟶ N) [Mono g] :
    moduleSupportSet B S hS X (cokernel (C := Modules.{u, u} B S hS X.1 X.2) f) ⊆
      moduleSupportSet B S hS X (cokernel (C := Modules.{u, u} B S hS X.1 X.2) (f ≫ g)) :=
  let _ := spaceModulesAbelian B S hS X
  moduleSupportSet_subset_of_mono B S hS X _ (shortExact_cokernel_comp f g).mono_f

end Supports

section Helpers

variable (X : AlgebraicSpaces B S hS)

/-- **A direct sum of copies of a map which is surjective on the sections over a chart is
surjective on the sections there.**  A section of the direct sum is the sum of its components
pushed back in, and each component has a preimage. -/
theorem surjective_val_app_biproduct_map {A C : Modules.{u, u} B S hS X.1 X.2} (f : A ⟶ C)
    (r : ℕ) (W : (SmallEtale B S hS X.1)ᵒᵖ) (hf : Function.Surjective (f.val.app W)) :
    Function.Surjective ((biproduct.map fun _ : Fin r => f).val.app W) := by
  intro y
  choose a ha using fun k : Fin r => hf ((biproduct.π (fun _ : Fin r => C) k).val.app W y)
  refine ⟨∑ k, (biproduct.ι (fun _ : Fin r => A) k).val.app W (a k), ?_⟩
  rw [map_sum]
  have htot : y = (∑ k, biproduct.π (fun _ : Fin r => C) k ≫
      biproduct.ι (fun _ : Fin r => C) k).val.app W y := by
    rw [biproduct.total]
    rfl
  rw [htot, sum_val_app_apply B S hS X Finset.univ _ W y]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : biproduct.ι (fun _ : Fin r => A) k ≫ biproduct.map (fun _ : Fin r => f) =
      f ≫ biproduct.ι (fun _ : Fin r => C) k := biproduct.ι_map _ _
  calc (biproduct.map fun _ : Fin r => f).val.app W
          ((biproduct.ι (fun _ : Fin r => A) k).val.app W (a k))
        = (biproduct.ι (fun _ : Fin r => A) k ≫
            biproduct.map fun _ : Fin r => f).val.app W (a k) := rfl
      _ = (f ≫ biproduct.ι (fun _ : Fin r => C) k).val.app W (a k) := by rw [h1]
      _ = (biproduct.ι (fun _ : Fin r => C) k).val.app W (f.val.app W (a k)) := rfl
      _ = _ := by
        rw [ha k]
        rfl

/-- **If `Kⁿ M = 0` then the ideal `Kⁿ` annihilates `M`**, the ideal `Kⁿ` being read as the
submodule `Kⁿ 𝒪_X` of the structure sheaf. -/
theorem idealPowSubmodule_unit_le_annihilatorIdealSheaf
    (K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) (n : ℕ)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (hn : Stacks.Sites.idealSmul (M := M)
        (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O) K n) ⊤ = ⊥) :
    idealPowSubmodule K n (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ≤
      annihilatorIdealSheaf B S hS X M := by
  refine idealPowSubmodule_le K n fun Y b hb z W g t => ?_
  change ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map g).hom
      (b * (show (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj Y from z)) • t = 0
  rw [map_mul, mul_smul]
  have hb' := (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O) K n).map_mem
    g hb
  have hmem := Stacks.Sites.smul_mem_idealSmul (M := M)
    (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O) K n) hb'
    (Stacks.SheafOfModules.mem_top_obj (((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map g).hom
        (show (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj Y from z) • t))
  rw [hn] at hmem
  have h0 : (⊥ : M.Submodule).obj W = ⊥ := SheafOfModules.Submodule.bot_obj M W
  exact (Submodule.mem_bot _).1 (h0 ▸ hmem)

/-- **A coherent module whose support is not everything is killed by a nonzero quasi-coherent
sheaf of ideals**, on a Noetherian algebraic space: a power of the sheaf of ideals of the reduced
closed subspace on the support kills it by Stacks 07UK, and that power is nonzero because it is
the unit ideal off the support. -/
theorem exists_quasicoherentIdeal_ne_bot_le_annihilatorIdealSheaf
    (noeth : IsNoetherian B S hS B.contains_terminal X.1)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M)
    (hne : moduleSupportSet B S hS X M ≠ Set.univ) :
    ∃ I : QuasicoherentIdeals B S hS X, I.1 ≠ ⊥ ∧ I.1 ≤ annihilatorIdealSheaf B S hS X M := by
  have hT : IsClosed (moduleSupportSet B S hS X M) := isClosed_moduleSupportSet B S hS X M hM
  set T := moduleSupportSet B S hS X M with hTdef
  set K := reducedIdealSheaf B S hS X T hT with hKdef
  have hKq : K.toSheafOfModules.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_reducedIdealSheaf B S hS X T hT
  obtain ⟨n, hn⟩ := (exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus B S hS
    B.contains_terminal X noeth M hM K hKq).2 (idealZeroLocus_reducedIdealSheaf B S hS X T hT).ge
  have hOq : (SheafOfModules.unit (structureRingSheaf B S hS X)).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_unit _
  refine ⟨⟨idealPowSubmodule K n (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))),
    isQuasicoherentOnSite_idealPowSubmodule B S hS X.1 X.2 K _ hOq hKq n⟩, ?_,
    idealPowSubmodule_unit_le_annihilatorIdealSheaf B S hS X K n M hn⟩
  obtain ⟨x, hx⟩ := Set.nonempty_compl.2 hne
  have hxK : x ∈ idealUnitLocus B S hS X K := by
    have h : x ∉ idealZeroLocus B S hS X K := by
      rw [idealZeroLocus_reducedIdealSheaf B S hS X T hT]
      exact hx
    exact not_not.1 h
  obtain ⟨V, hV, hxV⟩ := hxK
  refine ne_bot_of_idealUnitLocus_nonempty B S hS X _ ⟨x, V, ?_, hxV⟩
  exact idealPowSubmodule_obj_eq_top_of_range_subset_idealUnitLocus B S hS X K n _ V
    (range_subset_idealUnitLocus_of_eq_top B S hS X K V hV)

/-- A nonzero sheaf of ideals on a reduced space does not vanish everywhere. -/
private theorem idealZeroLocus_ne_univ_of_ne_bot
    (hred : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsReduced V))
    {K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule} (hK : K ≠ ⊥) :
    idealZeroLocus B S hS X K ≠ Set.univ := fun h => by
  obtain ⟨x, hx⟩ := idealUnitLocus_nonempty_of_ne_bot B S hS X hred K hK
  exact (h ▸ Set.mem_univ x : x ∈ idealZeroLocus B S hS X K) hx

/-- **A submodule contained in `I · G` factors through a monomorphism `j : E ⟶ G` whose cokernel
is killed by `I`**: the submodule `I · G` lies in the kernel of the projection onto the cokernel,
and `j` is the kernel of that projection. -/
theorem exists_comp_eq_ι_of_le_idealSmul {E G : Modules.{u, u} B S hS X.1 X.2} (j : E ⟶ G)
    [mono : Mono j] (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : I ≤ annihilatorIdealSheaf B S hS X (cokernel (C := Modules.{u, u} B S hS X.1 X.2) j))
    (G' : G.Submodule) (hG' : G' ≤ Stacks.Sites.idealSmul (M := G) I ⊤) :
    ∃ φ : G'.toSheafOfModules ⟶ E, φ ≫ j = G'.ι := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  have hker : Stacks.Sites.idealSmul (M := G) I ⊤ ≤
      SheafOfModules.Submodule.ker (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) j) := by
    refine Stacks.SheafOfModules.sheafifySubmodule_le
      (Stacks.Sites.presheafIdealSmul_le I fun V a ha m _ => ?_)
    change (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) j).val.app V (a • m) = 0
    exact (((cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) j).val.app V).hom.map_smul
      a m).trans (smul_eq_zero_of_mem_annihilatorIdealAt B S hS X _ V a
        (SheafOfModules.Submodule.le_iff.1 hI V ha) _)
  have hzero : G'.ι ≫ cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) j = 0 := by
    ext V x
    exact (SheafOfModules.Submodule.mem_ker _ V _).1
      (SheafOfModules.Submodule.le_iff.1 (hG'.trans hker) V x.2)
  exact ⟨_, (KernelFork.IsLimit.lift' (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel j))
    G'.ι hzero).2⟩

end Helpers

/-! ### Hypothesis (3) of Stacks 07UT -/

/-- **Hypothesis (3) of Stacks 07UT.**  For every reduced closed subspace `i : Z → X` with `|Z|`
irreducible there is a coherent `𝒪_Z`-module `𝒢` with `Supp(𝒢) = Z` such that for every nonzero
quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Z` there is a quasi-coherent submodule `𝒢' ⊆ ℐ𝒢` for which
`Supp(𝒢/𝒢')` is a proper closed subset of `|Z|` and `P` holds for `i_*𝒢'`. -/
def HasGenericSubsheaves (X : AlgebraicSpaces B S hS) (P : Modules.{u, u} B S hS X.1 X.2 → Prop) :
    Prop :=
  ∀ (Z : Subfunctor X.1) (closed : IsClosedSubspace B S hS Z), IsReducedIrreducible B S hS Z →
    ∃ G : Modules.{u, u} B S hS Z.toFunctor closed.1,
      IsCoherent B S hS Z.toFunctor closed.1 G ∧
      moduleSupportSet B S hS (closedSubfunctorSpace B S hS closed) G = Set.univ ∧
      ∀ I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS closed), I.1 ≠ ⊥ →
        ∃ G' : G.Submodule, G' ≤ Stacks.Sites.idealSmul (M := G) I.1 ⊤ ∧
          G'.toSheafOfModules.IsQuasicoherentOnSite ∧
          (∃ T : Set (points B S hS Z.toFunctor), IsClosed T ∧ T ≠ Set.univ ∧
            moduleSupportSet B S hS (closedSubfunctorSpace B S hS closed) (cokernel G'.ι) ⊆ T) ∧
          P ((modulePushforward B S hS (closedSubfunctorι B S hS closed)).obj
            G'.toSheafOfModules)

/-! ### The dévissage -/

section Devissage

variable (X : AlgebraicSpaces B S hS) (P : Modules.{u, u} B S hS X.1 X.2 → Prop)

/-- A property holding on zero modules and closed under extensions of coherent modules holds for
every finite direct sum of copies of a coherent module which has it. -/
theorem property_biproductConst
    (zero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (extension : ClosedUnderCoherentExtensions B S hS X P)
    {M : Modules.{u, u} B S hS X.1 X.2} (hM : IsCoherent B S hS X.1 X.2 M) (hPM : P M)
    (r : ℕ) : P (⨁ fun _ : Fin r => M) := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  exact (prop_biproductConst (fun N => IsCoherent B S hS X.1 X.2 N ∧ P N)
    (fun Z hZ => ⟨IsCoherent.of_isZero B S hS X.1 X.2 hZ, zero Z hZ⟩)
    (fun T hT h₁ h₃ => ⟨isCoherent_X₂_of_shortExact B S hS X.1 X.2 hT h₁.1 h₃.1,
      extension T hT h₁.1 (isCoherent_X₂_of_shortExact B S hS X.1 X.2 hT h₁.1 h₃.1) h₃.1
        h₁.2 h₃.2⟩)
    (fun e h => ⟨isCoherent_of_iso B S hS X.2 e h.1,
      property_of_iso B S hS X P zero extension h.1 (isCoherent_of_iso B S hS X.2 e h.1) e h.2⟩)
    ⟨hM, hPM⟩ r).2

/-- **The step at a reduced closed subspace with irreducible space of points.**  Let
`i : Y → X` be a closed immersion from a Noetherian algebraic space which is reduced with `|Y|`
irreducible, carrying a coherent `𝒢` as in hypothesis (3), and suppose `P` known for every
coherent module whose support is strictly smaller than the image of `|Y|`.  Then `P` holds for
`i_*ℒ` for every quasi-coherent sheaf of ideals `ℒ ⊆ 𝒪_Y`.

By Stacks 07UQ, in the case `Z = X`, there is an injection `ψ : ℐ₂^{⊕ r} → 𝒢` with `r > 0` and
cokernel supported in a proper closed subset.  Put `ℒ' = ℒ ∩ ℐ₂`; the composite
`j : ℒ'^{⊕ r} → ℐ₂^{⊕ r} → 𝒢` is injective with cokernel supported in `V(ℒ) ∪ Supp(coker ψ)`, a
proper closed subset of the irreducible `|Y|`, so it is killed by a nonzero quasi-coherent sheaf
of ideals `ℐ` (Stacks 07UK).  Hypothesis (3) gives `𝒢' ⊆ ℐ𝒢` with `P(i_*𝒢')`; as `ℐ` kills the
cokernel of `j`, the inclusion of `𝒢'` factors through `j`, by an injection `𝒢' → ℒ'^{⊕ r}` whose
cokernel embeds in `𝒢/𝒢'`.  Pushing forward, hypothesis (1) and the inductive hypothesis give `P`
for `i_*(ℒ'^{⊕ r}) = (i_*ℒ')^{⊕ r}`, hypothesis (2) gives `P(i_*ℒ')`, and the extension
`0 → i_*ℒ' → i_*ℒ → i_*(ℒ/ℒ') → 0`, whose last term is supported in the image of `V(ℐ₂)`, gives
`P(i_*ℒ)`. -/
theorem property_idealPushforward_of_hasGenericSubsheaf
    (noeth : IsNoetherian B S hS B.contains_terminal X.1)
    (zero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (extension : ClosedUnderCoherentExtensions B S hS X P)
    (ofSum : ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
      ∀ r : ℕ, 1 ≤ r → P (⨁ fun _ : Fin r => F) → P F)
    {Y : AlgebraicSpaces B S hS} (i : Y ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (hNY : IsNoetherian B S hS B.contains_terminal Y.1)
    (hred : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsReduced V))
    (hirr : IrreducibleSpace (points B S hS Y.1))
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : IsCoherent B S hS Y.1 Y.2 G)
    (hGsupp : moduleSupportSet B S hS Y G = Set.univ)
    (hGgen : ∀ I : QuasicoherentIdeals B S hS Y, I.1 ≠ ⊥ →
      ∃ G' : G.Submodule, G' ≤ Stacks.Sites.idealSmul (M := G) I.1 ⊤ ∧
        G'.toSheafOfModules.IsQuasicoherentOnSite ∧
        (∃ T : Set (points B S hS Y.1), IsClosed T ∧ T ≠ Set.univ ∧
          moduleSupportSet B S hS Y (cokernel G'.ι) ⊆ T) ∧
        P ((modulePushforward B S hS i).obj G'.toSheafOfModules))
    (IH : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N →
      moduleSupportSet B S hS X N ⊂ pointsMap B S hS Y.1 i.hom '' Set.univ → P N)
    (L : QuasicoherentIdeals B S hS Y) :
    P ((modulePushforward B S hS i).obj L.1.toSheafOfModules) := by
  by_cases hL : L.1 = ⊥
  · rw [hL]
    exact zero _ (isZero_modulePushforward_of_isZero B S hS _ X i
      (SheafOfModules.Submodule.isZero_toSheafOfModules_bot _))
  have _ : Fact (HasEtaleLocalProperty B S hS Y.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hNY.2.2⟩
  have _ : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨noeth.2.2⟩
  have hinj := pointsMap_hom_injective_of_isClosedImmersion B S hS i hi
  obtain ⟨r, I₂, hI₂q, hr, hI₂ne, ψ, hψ, Q₂, q₂, hq₂, ⟨hcol₂⟩, T₂, hT₂, hT₂ne, hQ₂⟩ :=
    exists_mono_biproduct_idealSheaf_cokernel_support_subset B S hS B.contains_terminal Y hNY
      hred hirr G hG hGsupp
  set L' : QuasicoherentIdeals B S hS Y :=
    ⟨L.1 ⊓ I₂, isQuasicoherentOnSite_idealInf B S hS Y L.1 I₂ L.2 hI₂q⟩ with hL'
  have hcohX : ∀ K : QuasicoherentIdeals B S hS Y,
      IsCoherent B S hS X.1 X.2 ((modulePushforward B S hS i).obj K.1.toSheafOfModules) :=
    fun K => isCoherent_modulePushforward_quasicoherentIdeal B S hS noeth.2.2 i hi K
  have hcohY : ∀ K : QuasicoherentIdeals B S hS Y, IsCoherent B S hS Y.1 Y.2 K.1.toSheafOfModules :=
    fun K => isCoherent_quasicoherentIdeal B S hS Y hNY.2.2 K
  have hmFst : Mono (Stacks.SheafOfModules.submoduleInfFst L.1 I₂) :=
    mono_of_mono_fac (Stacks.SheafOfModules.submoduleInfFst_ι L.1 I₂)
  have hmSnd : Mono (Stacks.SheafOfModules.submoduleInfSnd L.1 I₂) :=
    mono_of_mono_fac (Stacks.SheafOfModules.submoduleInfSnd_ι L.1 I₂)
  -- `P` for `i_*(ℒ ∩ ℐ₂)`
  have hPL' : P ((modulePushforward B S hS i).obj L'.1.toSheafOfModules) := by
    set incl := Stacks.SheafOfModules.submoduleInfSnd L.1 I₂ with hincl
    set j := biproduct.map (fun _ : Fin r => incl) ≫ ψ with hj
    have hjm : Mono j :=
      @mono_comp _ _ _ _ _ (biproduct.map fun _ : Fin r => incl) inferInstance ψ hψ
    have hE := isCoherent_biproductConst B S hS Y.1 Y.2 _ (hcohY L') r
    have hM : IsCoherent B S hS Y.1 Y.2 (cokernel j) := isCoherent_cokernel B S hS Y.1 Y.2 hE hG j
    have hMsupp : moduleSupportSet B S hS Y (cokernel j) ⊆ idealZeroLocus B S hS Y L.1 ∪ T₂ := by
      refine (moduleSupportSet_cokernel_comp_subset B S hS Y _ ψ).trans
        (Set.union_subset_union ?_ ?_)
      · exact supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective B S hS Y L.1 _
          fun V hV => surjective_val_app_biproduct_map B S hS Y incl r (op V)
            (fun s => surjective_submoduleInfSnd_app B S hS Y L.1 I₂ V hV s)
      · exact (supportOfSheaf_eq_of_iso B S hS Y
          ((cokernelIsCokernel ψ).coconePointUniqueUpToIso hcol₂)).trans_le hQ₂
    have hMne : moduleSupportSet B S hS Y (cokernel j) ≠ Set.univ := by
      intro h
      have hcl : IsClosed (idealZeroLocus B S hS Y L.1) :=
        (isOpen_idealUnitLocus B S hS Y L.1).isClosed_compl
      rcases isPreirreducible_iff_isClosed_union_isClosed.1
          (IrreducibleSpace.isIrreducible_univ _).isPreirreducible _ _ hcl hT₂
          (h ▸ hMsupp) with h1 | h1
      · exact idealZeroLocus_ne_univ_of_ne_bot B S hS Y hred hL (Set.eq_univ_of_univ_subset h1)
      · exact hT₂ne (Set.eq_univ_of_univ_subset h1)
    obtain ⟨I, hIne, hIann⟩ :=
      exists_quasicoherentIdeal_ne_bot_le_annihilatorIdealSheaf B S hS Y hNY _ hM hMne
    obtain ⟨G', hG'le, hG'q, ⟨T₃, -, hT₃ne, hG'T⟩, hPG'⟩ := hGgen I hIne
    have hG'ne : moduleSupportSet B S hS Y (cokernel G'.ι) ≠ Set.univ :=
      fun h => hT₃ne (Set.eq_univ_of_univ_subset (h ▸ hG'T))
    obtain ⟨φ, hφ⟩ := exists_comp_eq_ι_of_le_idealSmul B S hS Y j (mono := hjm) I.1 hIann G' hG'le
    have _ : Mono φ := mono_of_mono_fac hφ
    have hG'coh : IsCoherent B S hS Y.1 Y.2 G'.toSheafOfModules :=
      isCoherent_of_mono_of_isQuasicoherentOnSite B S hS Y.1 Y.2 G'.ι hG'q hG
    have hcokφ : IsCoherent B S hS Y.1 Y.2 (cokernel φ) :=
      isCoherent_cokernel B S hS Y.1 Y.2 hG'coh hE φ
    have hsuppφ : moduleSupportSet B S hS Y (cokernel φ) ⊆
        moduleSupportSet B S hS Y (cokernel G'.ι) := by
      refine (@moduleSupportSet_cokernel_subset_cokernel_comp B S hS Y _ _ _ φ j hjm).trans ?_
      rw [moduleSupportSet_congr B S hS Y (cokernelIsoOfEq hφ)]
    have hsumX := isCoherent_biproductConst B S hS X.1 X.2 _ (hcohX L') r
    let e := modulePushforwardBiproductConstIso B S hS X i r L'.1.toSheafOfModules ≪≫
      ((modulePushforward B S hS i).mapIso
        (biproduct.isoProduct fun _ : Fin r => L'.1.toSheafOfModules)).symm
    have hpushE := isCoherent_of_iso B S hS X.2 e hsumX
    have _ : Mono ((modulePushforward B S hS i).map φ) :=
      mono_modulePushforward_map B S hS i φ inferInstance
    have hpushG' : IsCoherent B S hS X.1 X.2
        ((modulePushforward B S hS i).obj G'.toSheafOfModules) :=
      isCoherent_of_mono_of_isQuasicoherentOnSite B S hS X.1 X.2
        ((modulePushforward B S hS i).map φ)
        (isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion B S hS i hi _ hG'q) hpushE
    have hpushQ : IsCoherent B S hS X.1 X.2 (cokernel ((modulePushforward B S hS i).map φ)) :=
      isCoherent_cokernel B S hS X.1 X.2 hpushG' hpushE _
    have hlt : moduleSupportSet B S hS X (cokernel ((modulePushforward B S hS i).map φ)) ⊂
        pointsMap B S hS Y.1 i.hom '' Set.univ := by
      rw [moduleSupportSet_cokernel_modulePushforward B S hS X Y i hi φ hcokφ]
      exact lt_of_le_of_lt (Set.image_mono hsuppφ) (image_ssubset_image_univ hinj hG'ne)
    have hPE := extension _ (shortExact_cokernelSequence_modulePushforward B S hS X Y i φ
      inferInstance) hpushG' hpushE hpushQ hPG' (IH _ hpushQ hlt)
    exact ofSum _ (hcohX L') r hr
      (property_of_iso B S hS X P zero extension hpushE hsumX e.symm hPE)
  -- from `ℒ ∩ ℐ₂` to `ℒ`
  have hcokY : IsCoherent B S hS Y.1 Y.2
      (cokernel (Stacks.SheafOfModules.submoduleInfFst L.1 I₂)) :=
    isCoherent_cokernel B S hS Y.1 Y.2 (hcohY L') (hcohY L) _
  have hcokX : IsCoherent B S hS X.1 X.2 (cokernel
      ((modulePushforward B S hS i).map (Stacks.SheafOfModules.submoduleInfFst L.1 I₂))) :=
    isCoherent_cokernel B S hS X.1 X.2 (hcohX L') (hcohX L) _
  have hlt : moduleSupportSet B S hS X (cokernel
      ((modulePushforward B S hS i).map (Stacks.SheafOfModules.submoduleInfFst L.1 I₂))) ⊂
        pointsMap B S hS Y.1 i.hom '' Set.univ := by
    rw [moduleSupportSet_cokernel_modulePushforward B S hS X Y i hi _ hcokY]
    refine lt_of_le_of_lt (Set.image_mono ?_) (image_ssubset_image_univ hinj
      (idealZeroLocus_ne_univ_of_ne_bot B S hS Y hred hI₂ne))
    exact supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective B S hS Y I₂ _
      fun V hV s => surjective_submoduleInfFst_app B S hS Y L.1 I₂ V hV s
  exact extension _ (shortExact_cokernelSequence_modulePushforward B S hS X Y i _ hmFst)
    (hcohX L') (hcohX L) hcokX hPL' (IH _ hcokX hlt)

/-- **The case of a module killed by the ideal of the reduced closed subspace on an irreducible
closed set containing its support**, granted `P` for every coherent module whose support is
strictly smaller than that set.

If the support is strictly smaller there is nothing to do.  Otherwise the scheme-theoretic
support `Z` of `C` is the reduced closed subspace on that set, which is reduced with `|Z|`
irreducible, and Stacks 07UQ gives an injection `i_*(ℐ^{⊕ r}) → C` whose cokernel is supported in
the image of a proper closed subset of `|Z|`.  The cokernel has `P` by hypothesis,
`i_*(ℐ^{⊕ r}) = (i_*ℐ)^{⊕ r}` has it by
`AlgebraicGeometry.Space.property_idealPushforward_of_hasGenericSubsheaf`, and hypothesis (1)
concludes. -/
theorem property_of_le_annihilatorIdealSheaf
    (noeth : IsNoetherian B S hS B.contains_terminal X.1)
    (zero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (extension : ClosedUnderCoherentExtensions B S hS X P)
    (ofSum : ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
      ∀ r : ℕ, 1 ≤ r → P (⨁ fun _ : Fin r => F) → P F)
    (generic : HasGenericSubsheaves B S hS X P)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTirr : IsIrreducible T)
    (IH : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N →
      moduleSupportSet B S hS X N ⊂ T → P N)
    (C : Modules.{u, u} B S hS X.1 X.2) (hC : IsCoherent B S hS X.1 X.2 C)
    (hann : reducedIdealSheaf B S hS X T hT ≤ annihilatorIdealSheaf B S hS X C)
    (hsupp : moduleSupportSet B S hS X C ⊆ T) : P C := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  rcases hsupp.eq_or_ssubset with heq | hlt
  swap
  · exact IH C hC hlt
  have hint := isReducedIrreducible_schemeTheoreticSupport B S hS X C hC T hT hTirr hann heq
  obtain ⟨hZ, r, I, hIq, hr, hIne, hsum, φ, hφ, Q, q, w, ⟨hcol⟩, T', -, hT'ne, hQsupp⟩ :=
    exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport B S hS
      B.contains_terminal X noeth C hC hint
  let _ := hC
  have hft : SheafOfModules.IsFiniteTypeOnSite C :=
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS X C
  obtain ⟨hZ', hid⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X C
    hC.toIsQuasicoherentOnSite hC.toIsCoherentOnSite.isFiniteType
  have hpts := supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X C
    hC.toIsQuasicoherentOnSite hft
  have himg : pointsMap B S hS _ (closedSubfunctorι B S hS hZ).hom '' Set.univ = T := by
    rw [Set.image_univ, ← heq, moduleSupportSet, hpts]
    rfl
  obtain ⟨G, hG, hGsupp, hGgen⟩ := generic _ hZ hint
  have hPI : P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
      I.toSheafOfModules) :=
    property_idealPushforward_of_hasGenericSubsheaf B S hS X P noeth zero extension ofSum
      (closedSubfunctorι B S hS hZ) hZ.2
      (isNoetherian_closedSubfunctor B S hS B.contains_terminal X noeth hZ) hint.1 hint.2
      G hG hGsupp hGgen (fun N hN hNlt => IH N hN (himg ▸ hNlt)) ⟨I, hIq⟩
  have hIX : IsCoherent B S hS X.1 X.2
      ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.toSheafOfModules) :=
    isCoherent_modulePushforward_quasicoherentIdeal B S hS noeth.2.2 _ hZ.2 ⟨I, hIq⟩
  let e := modulePushforwardBiproductConstIso B S hS X (closedSubfunctorι B S hS hZ) r
    I.toSheafOfModules ≪≫ ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).mapIso
      (biproduct.isoProduct fun _ : Fin r => I.toSheafOfModules)).symm
  have hsumX := isCoherent_biproductConst B S hS X.1 X.2 _ hIX r
  have hPsum := property_of_iso B S hS X P zero extension hsumX hsum e
    (property_biproductConst B S hS X P zero extension hIX hPI r)
  have hQcoh : IsCoherent B S hS X.1 X.2 Q :=
    isCoherent_of_iso B S hS X.2 (hcol.coconePointUniqueUpToIso (colimit.isColimit _)).symm
      (isCoherent_cokernel B S hS X.1 X.2 hsum hC φ)
  have hQlt : moduleSupportSet B S hS X Q ⊂ T := by
    rw [← himg]
    exact lt_of_le_of_lt hQsupp (image_ssubset_image_univ
      (pointsMap_hom_injective_of_isClosedImmersion B S hS (closedSubfunctorι B S hS hZ) hZ.2)
      hT'ne)
  have _ := hφ
  exact extension (ShortComplex.mk φ q w) (ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ hcol) inferInstance (epi_of_isColimit_cofork hcol))
    hsum hC hQcoh hPsum (IH Q hQcoh hQlt)

/-- **The irreducible-support case**, granted `P` for every coherent module of strictly smaller
support.  Let `T` be the support of `F` and `𝒥` the ideal of the reduced closed subspace on `T`.
Some power `𝒥ⁿ` kills `F`, by Stacks 07UK, so `F ⊇ 𝒥F ⊇ 𝒥²F ⊇ … ⊇ 𝒥ⁿF = 0` is a finite filtration
by coherent submodules whose successive quotients are killed by `𝒥`; those have `P` by
`AlgebraicGeometry.Space.property_of_le_annihilatorIdealSheaf`, and hypothesis (1) climbs the
filtration from `𝒥ⁿF` up to `F`. -/
theorem property_of_isIrreducible
    (noeth : IsNoetherian B S hS B.contains_terminal X.1)
    (zero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (extension : ClosedUnderCoherentExtensions B S hS X P)
    (ofSum : ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
      ∀ r : ℕ, 1 ≤ r → P (⨁ fun _ : Fin r => F) → P F)
    (generic : HasGenericSubsheaves B S hS X P)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hirr : IsIrreducible (moduleSupportSet B S hS X F))
    (IH : ∀ G : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 G →
      moduleSupportSet B S hS X G ⊂ moduleSupportSet B S hS X F → P G) :
    P F := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  have _ : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨noeth.2.2⟩
  have hT : IsClosed (moduleSupportSet B S hS X F) := isClosed_moduleSupportSet B S hS X F hF
  set T := moduleSupportSet B S hS X F with hTdef
  set J := reducedIdealSheaf B S hS X T hT with hJdef
  have hJq : J.toSheafOfModules.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_reducedIdealSheaf B S hS X T hT
  obtain ⟨n, hn⟩ := (exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus B S hS
    B.contains_terminal X noeth F hF J hJq).2 (idealZeroLocus_reducedIdealSheaf B S hS X T hT).ge
  have hcoh : ∀ k, IsCoherent B S hS X.1 X.2 (idealPowModule J k F) := fun k =>
    isCoherent_idealPowModule_of_isQuasicoherentOnSite B S hS X.1 X.2 J k F hF hJq
  have hsuppN : ∀ k, moduleSupportSet B S hS X (idealPowModule J k F) ⊆ T := fun k =>
    moduleSupportSet_subset_of_mono B S hS X (idealPowModuleι J k F) inferInstance
  have hann : ∀ C : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 C →
      J ≤ annihilatorIdealSheaf B S hS X C → moduleSupportSet B S hS X C ⊆ T → P C :=
    fun C hC hCJ hCT => property_of_le_annihilatorIdealSheaf B S hS X P noeth zero extension
      ofSum generic T hT hirr IH C hC hCJ hCT
  have hstep : ∀ {A M : Modules.{u, u} B S hS X.1 X.2} (i : A ⟶ M) [Mono i],
      IsCoherent B S hS X.1 X.2 A → IsCoherent B S hS X.1 X.2 M → P A →
      P (cokernel (C := Modules.{u, u} B S hS X.1 X.2) i) → P M := by
    intro A M i _ hA hM hPA hPQ
    exact extension _ (shortExact_mk_cokernel_condition i) hA hM
      (isCoherent_cokernel B S hS X.1 X.2 hA hM i) hPA hPQ
  have chain : ∀ m k : ℕ, k + m = n → P (idealPowModule J (k + 1) F) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      have hbot : idealPowSubmodule J (k + 1) F = ⊥ :=
        eq_bot_iff.2 ((idealPowSubmodule_antitone J F (by omega : n ≤ k + 1)).trans hn.le)
      exact zero _ (SheafOfModules.Submodule.isZero_toSheafOfModules_of_eq_bot hbot)
    | succ m ih =>
      intro k hk
      exact hstep (idealPowModuleSuccHom J (k + 1) F) (hcoh _) (hcoh _) (ih (k + 1) (by omega))
        (hann _ (isCoherent_cokernel B S hS X.1 X.2 (hcoh _) (hcoh _) _)
          (le_annihilatorIdealSheaf_cokernel_idealPowModuleSuccHom B S hS X J F (k + 1))
          ((moduleSupportSet_subset_of_epi B S hS X
            (cokernel.π (idealPowModuleSuccHom J (k + 1) F)) inferInstance).trans (hsuppN _)))
  exact hstep (idealPowModuleι J 1 F) (hcoh _) hF (chain n 0 (by omega))
    (hann _ (isCoherent_cokernel B S hS X.1 X.2 (hcoh _) hF _)
      (le_annihilatorIdealSheaf_cokernel_idealPowModuleι_one B S hS X J F)
      (moduleSupportSet_subset_of_epi B S hS X (cokernel.π (idealPowModuleι J 1 F))
        inferInstance))

/-- **Stacks Project, Tag 07UT.**  Let `X` be a Noetherian algebraic space over a scheme `S` and
let `P` be a property of coherent `𝒪_X`-modules such that

1. for a short exact sequence `0 → F₁ → F → F₂ → 0` of coherent modules, if `F₁` and `F₂` have
   `P` then so does `F`;
2. if `P` holds for `F^{⊕ r}` for some `r ≥ 1`, then it holds for `F`;
3. for every reduced closed subspace `i : Z → X` with `|Z|` irreducible there is a coherent
   `𝒪_Z`-module `𝒢` with `Supp(𝒢) = Z` such that for every nonzero quasi-coherent sheaf of ideals
   `ℐ ⊆ 𝒪_Z` there is a quasi-coherent `𝒢' ⊆ ℐ𝒢` with `Supp(𝒢/𝒢')` a proper closed subset of `|Z|`
   and `P(i_*𝒢')`

and such that `P` holds for the zero module.  Then `P` holds for every coherent `𝒪_X`-module.

The source does not list the zero module among its hypotheses, and its conclusion fails without
it: the property "is nonzero" satisfies (1), (2) and (3) — in (3) take `𝒢 = 𝒪_Z` and `𝒢' = ℐ𝒪_Z`
— and does not hold for the zero module.  The source's proof runs over the nonempty supports
only.

The proof is the source's Noetherian induction on the support of `F`, run over the closed
subsets of `|X|`, a Noetherian topological space by Stacks 04ZF.  A module with empty support is
zero; a reducible support is split by Stacks 07UP and (1) concludes; an irreducible support is
`AlgebraicGeometry.Space.property_of_isIrreducible`. -/
@[stacks 07UT]
theorem property_of_isCoherent_of_hasGenericSubsheaves
    (noeth : IsNoetherian B S hS B.contains_terminal X.1)
    (zero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (extension : ClosedUnderCoherentExtensions B S hS X P)
    (ofSum : ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
      ∀ r : ℕ, 1 ≤ r → P (⨁ fun _ : Fin r => F) → P F)
    (generic : HasGenericSubsheaves B S hS X P)
    (F : Modules.{u, u} B S hS X.1 X.2) (coherent : IsCoherent B S hS X.1 X.2 F) : P F := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  have _ : TopologicalSpace.NoetherianSpace (points B S hS X.1) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS X.1 X.2 noeth.1 noeth.2.2
  have hclosed : ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
      IsClosed (moduleSupportSet B S hS X F) :=
    fun F hF => isClosed_moduleSupportSet B S hS X F hF
  have key : ∀ T : TopologicalSpace.Closeds (points B S hS X.1),
      ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
      moduleSupportSet B S hS X F ⊆ (T : Set (points B S hS X.1)) → P F := by
    intro T
    refine wellFounded_lt.induction
      (C := fun T : TopologicalSpace.Closeds (points B S hS X.1) =>
        ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
          moduleSupportSet B S hS X F ⊆ (T : Set (points B S hS X.1)) → P F) T ?_
    clear T
    intro T IH F hF hFT
    have step : ∀ G : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 G →
        moduleSupportSet B S hS X G ⊂ (T : Set (points B S hS X.1)) → P G := by
      intro G hG hGT
      exact IH ⟨moduleSupportSet B S hS X G, hclosed G hG⟩
        (SetLike.coe_ssubset_coe.mp hGT) G hG Set.Subset.rfl
    rcases Set.eq_empty_or_nonempty (moduleSupportSet B S hS X F) with hempty | hne
    · exact zero F (isZero_of_supportOfSheaf_eq_empty B S hS X F hempty)
    by_cases hpre : IsPreirreducible (moduleSupportSet B S hS X F)
    · exact property_of_isIrreducible B S hS X P noeth zero extension ofSum generic F hF
        ⟨hne, hpre⟩ fun G hG hGF => step G hG (hGF.trans_le hFT)
    simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hpre
    obtain ⟨z₁, z₂, hz₁, hz₂, hcover, hn₁, hn₂⟩ := hpre
    have hunion : moduleSupportSet B S hS X F =
        moduleSupportSet B S hS X F ∩ z₁ ∪ moduleSupportSet B S hS X F ∩ z₂ := by
      rw [← Set.inter_union_distrib_left]
      exact (Set.inter_eq_left.2 hcover).symm
    have hlt₁ : moduleSupportSet B S hS X F ∩ z₁ ⊂ moduleSupportSet B S hS X F :=
      ⟨Set.inter_subset_left, fun h => hn₁ fun x hx => (h hx).2⟩
    have hlt₂ : moduleSupportSet B S hS X F ∩ z₂ ⊂ moduleSupportSet B S hS X F :=
      ⟨Set.inter_subset_left, fun h => hn₂ fun x hx => (h hx).2⟩
    obtain ⟨G', G, i, p, hip, hSE, hG', hG, hsupp', hsupp⟩ :=
      exists_shortExact_coherent_supportOfSheaf_subset B S hS X B.contains_terminal noeth F hF
        (moduleSupportSet B S hS X F ∩ z₁) (moduleSupportSet B S hS X F ∩ z₂)
        ((hclosed F hF).inter hz₁) ((hclosed F hF).inter hz₂) hunion
    exact extension (ShortComplex.mk i p hip) hSE hG' hF hG
      (step G' hG' ((hsupp'.trans_lt hlt₂).trans_le hFT))
      (step G hG ((hsupp.trans_lt hlt₁).trans_le hFT))
  exact key ⟨moduleSupportSet B S hS X F, hclosed F coherent⟩ F coherent Set.Subset.rfl

/-- A module on a closed subspace whose direct image is zero is zero: the inverse image of the
direct image gives the module back, by Stacks 04CJ part (2). -/
theorem isZero_of_isZero_modulePushforward (W Y : AlgebraicSpaces B S hS) (i : W ⟶ Y)
    (hi : IsClosedImmersion B S hS i.hom) {A : Modules.{u, u} B S hS W.1 W.2}
    (h : IsZero ((modulePushforward B S hS i).obj A)) : IsZero A :=
  have _ := (modulePullbackAdjunction B S hS i).isLeftAdjoint
  (Functor.map_isZero (modulePullback B S hS i) h).of_iso
    ((modulePullbackCounitIso B S hS i hi).app A).symm

/-- **The zero module cannot be dropped from Stacks 07UT.**  On every Noetherian algebraic
space the property "is nonzero" satisfies hypotheses (1), (2) and (3) of the lemma — for (3) take
`𝒢 = 𝒪_Z` and `𝒢' = ℐ𝒪_Z`, whose quotient is supported in `V(ℐ)` — while the zero module, which is
coherent, does not have it. -/
theorem exists_hasGenericSubsheaves_not_forall
    (noeth : IsNoetherian B S hS B.contains_terminal X.1) :
    ∃ P : Modules.{u, u} B S hS X.1 X.2 → Prop,
      ClosedUnderCoherentExtensions B S hS X P ∧
      (∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
        ∀ r : ℕ, 1 ≤ r → P (⨁ fun _ : Fin r => F) → P F) ∧
      HasGenericSubsheaves B S hS X P ∧
      ∃ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F ∧ ¬ P F := by
  refine ⟨fun M => ¬ IsZero M, ?_, ?_, ?_, ?_⟩
  · intro E hE _ _ _ h₁ _ h₂
    have _ := hE.mono_f
    exact h₁ (h₂.of_mono E.f)
  · intro F _ r _ hP hF
    refine hP ((IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ fun j => ?_))
    exact hF.eq_of_src _ _
  · intro Z hZ hint
    have hNZ : IsNoetherian B S hS B.contains_terminal (closedSubfunctorSpace B S hS hZ).1 :=
      isNoetherian_closedSubfunctor B S hS B.contains_terminal X noeth hZ
    have _ : Fact (HasEtaleLocalProperty B S hS (closedSubfunctorSpace B S hS hZ).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hNZ.2.2⟩
    set G := structureSheafModule B S hS (closedSubfunctorSpace B S hS hZ) with hGdef
    have hG : IsCoherent B S hS Z.toFunctor hZ.1 G := isCoherent_structureSheaf B S hS _ _
    refine ⟨G, hG, supportOfSheaf_structureSheafModule B S hS (closedSubfunctorSpace B S hS hZ),
      fun I hI => ?_⟩
    have hq : (Stacks.Sites.idealSmul (M := G) I.1 ⊤).toSheafOfModules.IsQuasicoherentOnSite := by
      have h := isQuasicoherentOnSite_idealPowSubmodule B S hS _ _ I.1 G
        (SheafOfModules.isQuasicoherentOnSite_unit _) I.2 1
      change (idealPowSubmodule I.1 1 G).toSheafOfModules.IsQuasicoherentOnSite at h
      exact (idealPowSubmodule_one I.1 G) ▸ h
    have hsub := supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective B S hS
      (closedSubfunctorSpace B S hS hZ) I.1 (Stacks.Sites.idealSmul (M := G) I.1 ⊤).ι
      fun W hW t => by
        refine ⟨⟨t, ?_⟩, rfl⟩
        have htop := idealPowSubmodule_obj_eq_top_of_range_subset_idealUnitLocus B S hS
          (closedSubfunctorSpace B S hS hZ) I.1 1 G W
          (range_subset_idealUnitLocus_of_eq_top B S hS _ I.1 W hW)
        have hmem : t ∈ (idealPowSubmodule I.1 1 G).obj (op W) := htop ▸ Submodule.mem_top
        exact (idealPowSubmodule_one I.1 G) ▸ hmem
    refine ⟨Stacks.Sites.idealSmul (M := G) I.1 ⊤, le_rfl, hq,
      ⟨idealZeroLocus B S hS (closedSubfunctorSpace B S hS hZ) I.1,
        (isOpen_idealUnitLocus B S hS _ I.1).isClosed_compl, fun huniv => ?_, hsub⟩, ?_⟩
    · exact idealZeroLocus_ne_univ_of_ne_bot B S hS _ hint.1 hI huniv
    · intro hz
      have hz' : IsZero (Stacks.Sites.idealSmul (M := G) I.1 ⊤).toSheafOfModules :=
        isZero_of_isZero_modulePushforward B S hS _ X _ hZ.2 hz
      refine hI (eq_bot_iff.2 (SheafOfModules.Submodule.le_iff.2 fun W a ha => ?_))
      let a' : (structureRingSheaf B S hS (closedSubfunctorSpace B S hS hZ)).obj.obj W := a
      have hmem : a' • SheafOfModules.unitOf
          (1 : (structureRingSheaf B S hS (closedSubfunctorSpace B S hS hZ)).obj.obj W) ∈
          (Stacks.Sites.idealSmul (M := G) I.1 ⊤).obj W :=
        Stacks.Sites.smul_mem_idealSmul (M := G) I.1 (a := a') ha
          (Stacks.SheafOfModules.mem_top_obj _)
      have h0 : (⟨_, hmem⟩ : (Stacks.Sites.idealSmul (M := G) I.1 ⊤).toSheafOfModules.val.obj W)
          = 0 :=
        congrArg (fun f => f.val.app W ⟨_, hmem⟩) (hz'.eq_of_src (𝟙 _) 0)
      have h1 : a' * 1 = 0 := congrArg Subtype.val h0
      rw [mul_one] at h1
      rw [SheafOfModules.Submodule.bot_obj _ W]
      exact (Submodule.mem_bot _).2 h1
  · obtain ⟨M, hM⟩ := HasZeroObject.zero (C := Modules.{u, u} B S hS X.1 X.2)
    exact ⟨M, IsCoherent.of_isZero B S hS X.1 X.2 hM, fun h => h hM⟩

end Devissage

end AlgebraicGeometry.Space

end

