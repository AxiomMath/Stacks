module

public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Homs
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Nilpotent
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors
public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.DualBasis
public import StacksFrontier.AlgebraicGeometry.AmpleTensorPower.Basic

/-!
# Twisting a morphism of quasi-coherent modules by a power of a section of an invertible module

Let `X` be a quasi-compact scheme, let `L` be an invertible `𝒪_X`-module and let `s` be a global
section of `L^{⊗ n}`, with nonvanishing open `X_s`. A morphism `α : ℱ ⟶ 𝒢` of quasi-coherent
`𝒪_X`-modules whose source is of finite type and whose restriction to `X_s` vanishes is killed by
a single power of `s`: there is one exponent `e` with `α ⊗ s ^ e = 0`, where `α ⊗ s ^ e` is read
sectionwise as the family `x ↦ α(x) ⊗ s ^ e|_V` of sections of `𝒢 ⊗ L^{⊗ n e}`.

## Main definitions

* `Stacks.SheafOfModules.Invertible.moduleMulOver`: the sectionwise tensor product of a section of
  a sheaf of modules with a section of `L^{⊗ b}` over the same open. This is the module-valued
  companion of `Stacks.SheafOfModules.Invertible.sectionMulOver`, which multiplies two sections of
  tensor powers.
* `AlgebraicGeometry.Scheme.Modules.toRingedSpaceSheaf`: an `𝒪_X`-module read at the ringed-space
  spelling of the structure sheaf, the identity map.
* `AlgebraicGeometry.Scheme.Modules.sectionOfPowerOne`: a global section of `L` read as a global
  section of `L^{⊗ 1}`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.moduleMulOver_app_eq_zero_of_generator`: over an open
  carrying a frame `g` of `L^{⊗ n}` with `s = a • g`, if `a ^ e` annihilates `α` then
  `α ⊗ s ^ e` vanishes.
* `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_app_eq_zero_of_generator`: over a
  quasi-compact open carrying a frame of `L^{⊗ n}`, one power of the coefficient of `s` in the
  frame annihilates `α`.
* `AlgebraicGeometry.Scheme.Modules.exists_forall_moduleMulOver_app_eq_zero`: `α ⊗ s ^ e = 0` for
  a single exponent `e`, for `s` a section of `L^{⊗ n}`.
* `AlgebraicGeometry.Scheme.Modules.exists_forall_moduleMulOver_app_eq_zero_of_sections`: the same
  for a section of `L` itself.

## Implementation notes

The hypothesis on `L` is `Stacks.SheafOfModules.IsInvertible`, the class
`Stacks.SheafOfModules.nonvanishingOpen` and Tag 0B5M key on. The tensor-power API of
`Stacks.SheafOfModules.Invertible.tensorPowerModule'` is stated for the other class of Tag 01CS,
`AlgebraicGeometry.SheafOfModules.IsInvertible`; the two are bridged by the local instance
`AlgebraicGeometry.Scheme.Modules.algebraicGeometryIsInvertible_of_isInvertible`.

## References

* [Stacks Project, Tag 01XQ](https://stacks.math.columbia.edu/tag/01XQ)
* [Stacks Project, Tag 0B5M](https://stacks.math.columbia.edu/tag/0B5M)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/


@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules.Invertible

variable {X : RingedSpace.{u, u}} (L : _root_.SheafOfModules.{u} (structureSheafRing X))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
    (structureSheafRing X).property L]
  (M : _root_.SheafOfModules.{u} (structureSheafRing X)) (b : ℕ)

local notation "Lpow[" n "]" => tensorPowerModule' L ((n : ℕ) : ℤ)

/-- The sectionwise tensor product of a section of a sheaf of modules `M` over an open with a
section of `L^{⊗ b}` over the same open, a section of `M ⊗ L^{⊗ b}`. -/
def moduleMulOver (U : Opens X.carrier) (x : M.val.obj (op U)) (y : Lpow[b].val.obj (op U)) :
    (_root_.SheafOfModules.val (R := structureSheafRing X)
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj M).obj
          Lpow[b])).obj (op U) :=
  TensorStalkRingedSpace.toTensorSheafSection X M Lpow[b] (op U)
    (x ⊗ₜ[X.presheaf.obj (op U)] y)

/-- The sectionwise twist is linear in the section of `M`. -/
theorem moduleMulOver_smul_left (U : Opens X.carrier) (c : X.presheaf.obj (op U))
    (x : M.val.obj (op U)) (y : Lpow[b].val.obj (op U)) :
    moduleMulOver L M b U (c • x) y = c • moduleMulOver L M b U x y :=
  Stacks.Cohomology.Generators.toTensorSheafSection_smul_left X M Lpow[b] U c x y

/-- The sectionwise twist is linear in the section of `L^{⊗ b}`. -/
theorem moduleMulOver_smul_right (U : Opens X.carrier) (c : X.presheaf.obj (op U))
    (x : M.val.obj (op U)) (y : Lpow[b].val.obj (op U)) :
    moduleMulOver L M b U x (c • y) = c • moduleMulOver L M b U x y :=
  Stacks.Cohomology.Generators.toTensorSheafSection_smul_right X M Lpow[b] U c x y

/-- The sectionwise twist of the zero section is zero. -/
theorem moduleMulOver_zero_left (U : Opens X.carrier) (y : Lpow[b].val.obj (op U)) :
    moduleMulOver L M b U 0 y = 0 := by
  rw [moduleMulOver, TensorProduct.zero_tmul]
  exact map_zero _

/-- The sectionwise twist commutes with restriction to a smaller open. -/
theorem moduleMulOver_restrict {U V : Opens X.carrier} (h : V ≤ U) (x : M.val.obj (op U))
    (y : Lpow[b].val.obj (op U)) :
    (_root_.SheafOfModules.val (R := structureSheafRing X)
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj M).obj
            Lpow[b])).map (homOfLE h).op
        (moduleMulOver L M b U x y) =
      moduleMulOver L M b V (M.val.map (homOfLE h).op x) (Lpow[b].val.map (homOfLE h).op y) :=
  Stacks.Cohomology.Generators.toTensorSheafSection_restrict X M Lpow[b] h x y

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.QcohLimits

variable {X : Scheme.{u}}

/-- An `𝒪_X`-module on a scheme, read as a module on the underlying ringed space in the
`Stacks.SheafOfModules.TensorStalkRingedSpace` packaging of the structure sheaf. This is the
identity: both spellings of the structure sheaf are
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf`. -/
abbrev toRingedSpaceSheaf (M : X.Modules) :
    _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace) := M

variable (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [hLinv : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- An invertible module in the sense of `Stacks.SheafOfModules.IsInvertible` is invertible in
the sense of `AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
local instance algebraicGeometryIsInvertible_of_isInvertible :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
  (Stacks.InvertibleLocallyFree.stacksIsInvertible_iff_isInvertible _ _ L).mp hLinv

local notation "Lpow[" n "]" => tensorPowerModule' L ((n : ℕ) : ℤ)

/-- If the section `s` of `L^{⊗ n}` is the multiple `a • g` of a frame `g` over `U`, and the
power `a ^ e` annihilates the morphism `α` over every open inside `U`, then `α ⊗ s ^ e` vanishes
over every open inside `U`. -/
theorem moduleMulOver_app_eq_zero_of_generator {n : ℕ} (s : Lpow[n].sections)
    (F G : X.Modules) (α : F ⟶ G) {U : X.Opens}
    (g : GeneratorSections X.toRingedSpace Lpow[n] U) (a : Γ(X, U))
    (ha : s.eval (op U) = a • g.val) (e : ℕ)
    (he : ∀ (V : X.Opens) (hV : V ≤ U) (x : Γ(F, V)),
      X.presheaf.map (homOfLE hV).op a ^ e • α.app V x = 0)
    (V : X.Opens) (hV : V ≤ U) (x : Γ(F, V)) :
    moduleMulOver L (toRingedSpaceSheaf G) (n * e) V (α.app V x)
      ((sectionPow' L s e).eval (op V)) = 0 := by
  set c := X.presheaf.map (homOfLE hV).op a with hc
  set q := sectionPowOver L (op V) (Lpow[n].val.map (homOfLE hV).op g.val) e with hq
  have h1 : Lpow[n].val.map (homOfLE hV).op (s.eval (op U)) = s.eval (op V) :=
    PresheafOfModules.sections_property s (homOfLE hV).op
  have h2 : s.eval (op V) = c • Lpow[n].val.map (homOfLE hV).op g.val := by
    rw [← h1, ha]
    exact Lpow[n].val.map_smul (homOfLE hV).op a g.val
  have h3 : sectionPowOver L (op V) (s.eval (op V)) e = c ^ e • q :=
    (congrArg (fun z => sectionPowOver L (op V) z e) h2).trans
      (sectionPowOver_smul L (op V) c _ e)
  have hz : (c ^ e • α.app V x : (toRingedSpaceSheaf G).val.obj (op V)) = 0 := he V hV x
  refine ((congrArg (fun z => moduleMulOver L (toRingedSpaceSheaf G) (n * e) V (α.app V x) z)
    ((eval_sectionPow' L s (op V) e).trans h3)).trans ?_)
  refine (moduleMulOver_smul_right L (toRingedSpaceSheaf G) (n * e) V (c ^ e)
    (α.app V x) q).trans ?_
  refine (moduleMulOver_smul_left L (toRingedSpaceSheaf G) (n * e) V (c ^ e)
    (α.app V x) q).symm.trans ?_
  exact (congrArg (fun z => moduleMulOver L (toRingedSpaceSheaf G) (n * e) V z q) hz).trans
    (moduleMulOver_zero_left L (toRingedSpaceSheaf G) (n * e) V q)

/-- On a quasi-compact open `U` over which `L^{⊗ n}` has a frame `g`, a morphism of quasi-coherent
modules with source of finite type vanishing on the nonvanishing open of `s` is annihilated by one
power of the coefficient of `s` in the frame. -/
theorem exists_pow_smul_app_eq_zero_of_generator {n : ℕ} (s : Lpow[n].sections)
    (F G : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent] (α : F ⟶ G)
    (hα : ∀ V ≤ nonvanishingOpen (X := X.toRingedSpace) Lpow[n] s, ∀ x : Γ(F, V),
      α.app V x = 0)
    {U : X.Opens} (hU : IsCompact (U : Set X))
    (g : GeneratorSections X.toRingedSpace Lpow[n] U) :
    ∃ (a : Γ(X, U)) (e : ℕ), s.eval (op U) = a • g.val ∧
      ∀ (V : X.Opens) (hV : V ≤ U) (x : Γ(F, V)),
        X.presheaf.map (homOfLE hV).op a ^ e • α.app V x = 0 := by
  have hbij := g.property U le_rfl
  rw [generator_restrict_self Lpow[n] U g] at hbij
  obtain ⟨a, ha⟩ := hbij.surjective (s.eval (op U))
  have ha' : s.eval (op U) = a • g.val := ha.symm
  have hbasic : X.basicOpen a = nonvanishingOpen (X := X.toRingedSpace) Lpow[n] s ⊓ U :=
    basicOpen_eq_inf_nonvanishingOpen_of_generator L s g a ha'
  have hvanish : ∀ V ≤ X.basicOpen a, ∀ x : Γ(F, V), α.app V x = 0 :=
    fun V hVa x => hα V (hVa.trans (hbasic.le.trans inf_le_left)) x
  obtain ⟨e, he⟩ := exists_pow_smul_app_eq_zero_of_isCompact F G α hU a hvanish
  exact ⟨a, e, ha', he⟩

/-- A section of an `𝒪_X`-module over an open which vanishes on an open cover of that open
vanishes. -/
private theorem eq_zero_of_restrict_eq_zero (M : X.Modules) {ι : Type*} (W : ι → X.Opens)
    (V : X.Opens) (hle : ∀ i, W i ≤ V) (hcov : V ≤ ⨆ i, W i) (z : Γ(M, V))
    (h : ∀ i, M.presheaf.map (homOfLE (hle i)).op z = 0) : z = 0 :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) W V
    (fun i => homOfLE (hle i)) hcov z 0 (fun i => by rw [h i, map_zero])

/-- Let `L` be an invertible `𝒪_X`-module on a quasi-compact scheme `X` and let `s` be a global
section of `L^{⊗ n}`. A morphism `α : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules with `ℱ` of finite
type which vanishes on the open where `s` does not vanish satisfies `α ⊗ s ^ e = 0` for a single
exponent `e`. -/
theorem exists_forall_moduleMulOver_app_eq_zero [CompactSpace X] {n : ℕ} (s : Lpow[n].sections)
    (F G : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent] (α : F ⟶ G)
    (hα : ∀ V ≤ nonvanishingOpen (X := X.toRingedSpace) Lpow[n] s, ∀ x : Γ(F, V),
      α.app V x = 0) :
    ∃ e : ℕ, ∀ (V : X.Opens) (x : Γ(F, V)),
      moduleMulOver L (toRingedSpaceSheaf G) (n * e) V (α.app V x)
        ((sectionPow' L s e).eval (op V)) = 0 := by
  classical
  have hcov : ∀ y : X, ∃ V : X.Opens, y ∈ V ∧ IsCompact (V : Set X) ∧
      Nonempty (GeneratorSections X.toRingedSpace L V) := by
    intro y
    obtain ⟨W, hyW, b, hb⟩ := exists_bijective_smul_of_isInvertible L y
    obtain ⟨V, hVaff, hyV, hVW⟩ := exists_isAffineOpen_mem_and_subset hyW
    have hVW' : V ≤ W := hVW
    exact ⟨V, hyV, hVaff.isCompact, ⟨generatorRestrict L hVW' ⟨b, fun V' h => hb V' h⟩⟩⟩
  choose V hyV hVc hVgen using hcov
  have hAE : ∀ y : X, ∃ (a : Γ(X, V y)) (e : ℕ),
      s.eval (op (V y)) = a • (tensorPowerGenerator L (hVgen y).some n).val ∧
      ∀ (W : X.Opens) (hW : W ≤ V y) (x : Γ(F, W)),
        X.presheaf.map (homOfLE hW).op a ^ e • α.app W x = 0 :=
    fun y => exists_pow_smul_app_eq_zero_of_generator L s F G α hα (hVc y)
      (tensorPowerGenerator L (hVgen y).some n)
  choose aa ee haa hee using hAE
  obtain ⟨σ, hσ⟩ := (CompactSpace.isCompact_univ (X := X)).elim_finite_subcover
    (fun y : X => (V y : Set X)) (fun y => (V y).isOpen)
    (fun z _ => Set.mem_iUnion.2 ⟨z, hyV z⟩)
  refine ⟨σ.sup ee, fun W x => ?_⟩
  refine eq_zero_of_restrict_eq_zero
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
        (toRingedSpaceSheaf G)).obj Lpow[n * σ.sup ee])
    (fun i : (σ : Set X) => W ⊓ V i.1) W (fun _ => inf_le_left) ?_ _ ?_
  · intro z hzW
    obtain ⟨y, hyσ, hzy⟩ : ∃ y ∈ σ, z ∈ V y := by
      have h := hσ (Set.mem_univ z)
      simpa using h
    exact Opens.mem_iSup.2 ⟨⟨y, hyσ⟩, ⟨hzW, hzy⟩⟩
  · intro i
    have h1 : W ⊓ V i.1 ≤ V i.1 := inf_le_right
    have h2 : W ⊓ V i.1 ≤ W := inf_le_left
    have hbump : ∀ (W' : X.Opens) (hW' : W' ≤ V i.1) (y : Γ(F, W')),
        X.presheaf.map (homOfLE hW').op (aa i.1) ^ σ.sup ee • α.app W' y = 0 := by
      intro W' hW' y
      have hle : ee i.1 ≤ σ.sup ee := Finset.le_sup i.2
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hee i.1 W' hW' y, smul_zero]
    have hzero := moduleMulOver_app_eq_zero_of_generator L s F G α
      (tensorPowerGenerator L (hVgen i.1).some n) (aa i.1) (haa i.1) (σ.sup ee) hbump
      (W ⊓ V i.1) h1 (F.presheaf.map (homOfLE h2).op x)
    have hnat : (toRingedSpaceSheaf G).val.map (homOfLE h2).op (α.app W x)
        = α.app (W ⊓ V i.1) (F.presheaf.map (homOfLE h2).op x) :=
      (app_naturality α h2 x).symm
    have hsec : Lpow[n * σ.sup ee].val.map (homOfLE h2).op
          ((sectionPow' L s (σ.sup ee)).eval (op W))
        = (sectionPow' L s (σ.sup ee)).eval (op (W ⊓ V i.1)) :=
      PresheafOfModules.sections_property (sectionPow' L s (σ.sup ee)) (homOfLE h2).op
    change (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
        (toRingedSpaceSheaf G)).obj Lpow[n * σ.sup ee]).val.map (homOfLE h2).op
      (moduleMulOver L (toRingedSpaceSheaf G) (n * σ.sup ee) W (α.app W x)
        ((sectionPow' L s (σ.sup ee)).eval (op W))) = 0
    refine (moduleMulOver_restrict L (toRingedSpaceSheaf G) (n * σ.sup ee) h2
      (α.app W x) ((sectionPow' L s (σ.sup ee)).eval (op W))).trans ?_
    refine Eq.trans ?_ hzero
    exact congrArg₂ (fun u v => moduleMulOver L (toRingedSpaceSheaf G) (n * σ.sup ee)
      (W ⊓ V i.1) u v) hnat hsec

/-- A global section of `L`, read as a global section of the first tensor power `L^{⊗ 1}`. -/
def sectionOfPowerOne (s : L.sections) : Lpow[1].sections :=
  _root_.SheafOfModules.sectionsMap (tensorPowerOneIso _ _ L).symm.hom s

/-- Let `L` be an invertible `𝒪_X`-module on a quasi-compact scheme `X` and let `s ∈ Γ(X, L)`. A
morphism `α : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules with `ℱ` of finite type which vanishes on
`X_s` satisfies `α ⊗ s ^ e = 0` for a single exponent `e`. -/
theorem exists_forall_moduleMulOver_app_eq_zero_of_sections [CompactSpace X] (s : L.sections)
    (F G : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent] (α : F ⟶ G)
    (hα : ∀ V ≤ nonvanishingOpen (X := X.toRingedSpace) L s, ∀ x : Γ(F, V), α.app V x = 0) :
    ∃ e : ℕ, ∀ (V : X.Opens) (x : Γ(F, V)),
      moduleMulOver L (toRingedSpaceSheaf G) (1 * e) V (α.app V x)
        ((sectionPow' L (sectionOfPowerOne L s) e).eval (op V)) = 0 := by
  refine exists_forall_moduleMulOver_app_eq_zero L (sectionOfPowerOne L s) F G α ?_
  have hnv : nonvanishingOpen (X := X.toRingedSpace) Lpow[1] (sectionOfPowerOne L s)
      = nonvanishingOpen (X := X.toRingedSpace) L s :=
    nonvanishingOpen_sectionsMap (tensorPowerOneIso _ _ L).symm s
  exact fun V hV x => hα V (hnv ▸ hV) x

end AlgebraicGeometry.Scheme.Modules

end
