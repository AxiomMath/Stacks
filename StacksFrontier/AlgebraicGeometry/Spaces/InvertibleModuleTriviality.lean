module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandNoSliceSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Triviality of an invertible module with nonzero sections in degrees `1` and `-1`

Let `F` be an integral algebraic space whose ring `H⁰(F, 𝒪_F)` of global regular functions is a
field, and let `L` be an invertible `𝒪_F`-module.  If both `H⁰(F, L)` and `H⁰(F, L^{⊗ -1})` are
nonzero then `L ≅ 𝒪_F`.

## Main results

* `AlgebraicGeometry.Space.unitEndRingEquivGlobalFunctions`: the endomorphism ring of `𝒪_F` is
  `H⁰(F, 𝒪_F)`.
* `AlgebraicGeometry.Space.exists_common_chart_mem_basicOpen`: two nonzero regular functions on
  two étale charts of an integral algebraic space are simultaneously nonvanishing at a point of
  a common chart.
* `AlgebraicGeometry.Space.mono_of_ne_zero`: on an integral algebraic space a nonzero global
  section of an invertible module is a monomorphism `𝒪_F ⟶ L`.
* `AlgebraicGeometry.Space.isTrivial_of_nontrivial_sections` is Stacks 0DMZ: an invertible
  module with nonzero sections in degrees `1` and `-1` is trivial.

## Implementation notes

Stacks 0DMZ is stated for a proper integral algebraic space over a field, and uses properness
only through Tag 0DMY, that the global regular functions then form a field.  Tag 0DMY is not
available in this library, so that conclusion is carried as an explicit hypothesis and the base
is an arbitrary scheme; the attribute on the main theorem discloses this.

## References

* [Stacks Project, Tag 0DMZ](https://stacks.math.columbia.edu/tag/0DMZ)
* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules (IsInvertible IsTrivial)
open Stacks.SheafOfModules.TensorPower (tensorPower tensorPowerSuccIso tensorPowerOneIso
  tensorPowerReindex)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The sheaf of rings `𝒪_F` on the small étale site of an algebraic space `F`, in the spelling
by which the tensor product of `𝒪_F`-modules is indexed.  It is
`AlgebraicGeometry.RingedSite.ringSheaf` of the small étale ringed site, by
`AlgebraicGeometry.Space.ringSheaf_eq_structureSheaf`, and is stated this way so that the
invertibility and tensor-power API — whose instances are keyed on this spelling — applies
without unfolding `AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
abbrev modulesRingSheaf : Sheaf (SmallEtale.topology B S hS F) RingCat.{u} :=
  Stacks.SheafOfModules.TensorSheafification.structureSheaf (structureSheaf B S hS F hF).obj
    (structureRingPresheaf_isSheaf B S hS F hF)

/-- Right tensoring by an invertible `𝒪_F`-module is an equivalence of the category of
`𝒪_F`-modules, which is the hypothesis under which its integer tensor powers are defined.

This is `Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor`, restated at the
small étale site of `F`: instance search does not apply the general form here, because the
ring-sheaf argument of `Stacks.SheafOfModules.Tensor.sheafTensor` does not unify at instance
transparency. -/
instance isEquivalence_tensorRightFunctor (L : SheafOfModules.{u} (modulesRingSheaf B S hS F hF))
    [IsInvertible (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF) L] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨(structureSheaf B S hS F hF).obj, Presheaf.isSheaf_of_isSheaf_comp _
        (structureSheaf B S hS F hF).obj (forget₂ CommRingCat RingCat)
        (structureRingPresheaf_isSheaf B S hS F hF)⟩).flip.obj L).IsEquivalence :=
  Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ L

/-! ### Endomorphisms of the structure sheaf -/

/-- The endomorphism ring of `𝒪_F`, viewed as a module over itself, is the ring
`H⁰(F, 𝒪_F)` of global regular functions: an endomorphism is determined by the image of `1`,
and composition becomes multiplication. -/
noncomputable def unitEndRingEquivGlobalFunctions :
    End (SheafOfModules.unit (modulesRingSheaf B S hS F hF)) ≃+*
      globalFunctions B S hS F where
  toEquiv := End.homEquiv.trans (SheafOfModules.unit
    (modulesRingSheaf B S hS F hF)).unitHomEquiv
  map_mul' f g := by
    apply Subtype.ext
    funext U
    let fU : ((structureSheaf B S hS F hF).obj).obj U →ₗ[((structureSheaf B S hS F hF).obj).obj U]
      ((structureSheaf B S hS F hF).obj).obj U := (f.asHom.val.app U).hom
    let gU : ((structureSheaf B S hS F hF).obj).obj U →ₗ[((structureSheaf B S hS F hF).obj).obj U]
      ((structureSheaf B S hS F hF).obj).obj U := (g.asHom.val.app U).hom
    change fU (gU 1) = fU 1 * gU 1
    have h := fU.map_smul (gU 1) (1 : ((structureSheaf B S hS F hF).obj).obj U)
    simp only [smul_eq_mul, mul_one] at h
    rw [h, mul_comm]
  map_add' _ _ := rfl

/-- If `H⁰(F, 𝒪_F)` is a field then every nonzero endomorphism of `𝒪_F` is an isomorphism. -/
theorem isIso_of_ne_zero (hfield : IsField (globalFunctions B S hS F))
    (f : End (SheafOfModules.unit (modulesRingSheaf B S hS F hF)))
    (hf : f ≠ 0) : IsIso f.asHom := by
  let e := unitEndRingEquivGlobalFunctions B S hS F hF
  let _ := hfield.toField
  have hn : e f ≠ 0 := fun h => hf (e.injective (h.trans e.map_zero.symm))
  have huf : IsUnit f := by
    simpa using (isUnit_iff_ne_zero.mpr hn).map e.symm.toMonoidHom
  exact (CategoryTheory.isUnit_iff_isIso f).mp huf

/-! ### Nonvanishing on a common chart -/

include hF in
/-- On an integral algebraic space two nonzero regular functions on two étale charts are
simultaneously nonvanishing at a point of a common chart.

The charts of a reduced algebraic space are reduced, so each nonvanishing locus is a nonempty
open of its chart; its image in `|F|` is open because a chart is étale, the two images meet
because `|F|` is irreducible, and a common chart through a point of the intersection is
Tag 03H4. -/
theorem exists_common_chart_mem_basicOpen (hint : IsIntegralSpace B S hS F)
    (U V : SmallEtale B S hS F) (a : Γ(chartScheme U, ⊤)) (b : Γ(chartScheme V, ⊤))
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ (W : SmallEtale B S hS F) (p : W ⟶ U) (q : W ⟶ V)
      (w : points B S hS (yoneda.obj W.obj.left)),
      pointsToScheme B S hS W.obj.left w ∈
          (chartScheme W).basicOpen
            (((BigFppfOver.toScheme B S hS).map p.hom.left).appTop a) ∧
        pointsToScheme B S hS W.obj.left w ∈
          (chartScheme W).basicOpen
            (((BigFppfOver.toScheme B S hS).map q.hom.left).appTop b) := by
  classical
  have _ := hint.2.2
  have hred : ∀ Z : SmallEtale B S hS F, IsReduced (chartScheme Z) := fun Z =>
    (exists_atlas_iff_forall_etale B S hS F (fun Y : Scheme.{u} => IsReduced Y) hF).mp hint.1
      Z.obj.left Z.obj.hom Z.property
  have hne : ∀ (Z : SmallEtale B S hS F) (c : Γ(chartScheme Z, ⊤)), c ≠ 0 →
      ((chartScheme Z).basicOpen c : Set (chartScheme Z)).Nonempty := by
    intro Z c hc
    have _ := hred Z
    by_contra hcon
    exact hc (eq_zero_of_basicOpen_eq_bot c
      (by rwa [← TopologicalSpace.Opens.not_nonempty_iff_eq_bot]))
  have hopen : ∀ (Z : SmallEtale B S hS F) (c : Γ(chartScheme Z, ⊤)),
      IsOpen (pointsMap B S hS (yoneda.obj Z.obj.left) Z.obj.hom ''
        (pointsToScheme B S hS Z.obj.left ⁻¹'
          ((chartScheme Z).basicOpen c : Set (chartScheme Z)))) := by
    intro Z c
    refine isOpenMap_pointsMap_of_presheafEtale B S hS Z.obj.hom Z.property _ ?_
    rw [isOpen_pointTopology_yoneda_iff_isOpen_image,
      Set.image_preimage_eq _ (surjective_pointsToScheme B S hS Z.obj.left)]
    exact ((chartScheme Z).basicOpen c).isOpen
  have himg : ∀ (Z : SmallEtale B S hS F) (c : Γ(chartScheme Z, ⊤)), c ≠ 0 →
      (pointsMap B S hS (yoneda.obj Z.obj.left) Z.obj.hom ''
        (pointsToScheme B S hS Z.obj.left ⁻¹'
          ((chartScheme Z).basicOpen c : Set (chartScheme Z)))).Nonempty := by
    intro Z c hc
    obtain ⟨xz, hxz⟩ := hne Z c hc
    obtain ⟨rz, hrz⟩ := surjective_pointsToScheme B S hS Z.obj.left xz
    exact ⟨_, rz, by simpa [hrz] using hxz, rfl⟩
  obtain ⟨z, ⟨p₀, hp₀mem, hp₀⟩, ⟨q₀, hq₀mem, hq₀⟩⟩ :=
    show ((pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom ''
          (pointsToScheme B S hS U.obj.left ⁻¹'
            ((chartScheme U).basicOpen a : Set (chartScheme U)))) ∩
        (pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom ''
          (pointsToScheme B S hS V.obj.left ⁻¹'
            ((chartScheme V).basicOpen b : Set (chartScheme V))))).Nonempty from by
      have h := PreirreducibleSpace.isPreirreducible_univ _ _ (hopen U a) (hopen V b)
        (by simpa using himg U a ha) (by simpa using himg V b hb)
      simpa using h
  obtain ⟨W, p, q, r, hrp, hrq⟩ := exists_common_chart B S hS F U V p₀ q₀ (hp₀.trans hq₀.symm)
  have key : ∀ (Y : SmallEtale B S hS F) (g : W ⟶ Y) (y₀ : points B S hS (yoneda.obj Y.obj.left))
      (c : Γ(chartScheme Y, ⊤)),
      pointsMap B S hS (yoneda.obj W.obj.left) (yoneda.map g.hom.left) r = y₀ →
      pointsToScheme B S hS Y.obj.left y₀ ∈ (chartScheme Y).basicOpen c →
      pointsToScheme B S hS W.obj.left r ∈
        (chartScheme W).basicOpen (((BigFppfOver.toScheme B S hS).map g.hom.left).appTop c) := by
    intro Y g y₀ c hr hmem
    rw [← Scheme.preimage_basicOpen_top]
    change (BigFppfOver.toScheme B S hS).map g.hom.left
      (pointsToScheme B S hS W.obj.left r) ∈ (chartScheme Y).basicOpen c
    rw [← pointsToScheme_pointsMap_yoneda B S hS g.hom.left r, hr]
    exact hmem
  exact ⟨W, p, q, r, key U p p₀ a hrp hp₀mem, key V q q₀ b hrq hq₀mem⟩

/-! ### A nonzero section of an invertible module is a monomorphism -/

/-- **The geometric half of Stacks 0DMZ.**  On an integral algebraic space a nonzero global
section of an invertible `𝒪_F`-module is a monomorphism `𝒪_F ⟶ M`.

By Stacks 0B8N (b) the module is, on a covering of a chart where the section does not vanish, a
sectionwise split summand of a finite free module; one coordinate of that splitting turns the
section into a regular function `b ≠ 0` on a chart, naturally in the charts above it.  Were the
section to kill a nonzero function `x` on some chart, the product of `x` and `b` would vanish on
a common chart, which it cannot: both are nonvanishing at one of its points. -/
theorem mono_of_ne_zero (hint : IsIntegralSpace B S hS F)
    (M : SheafOfModules.{u} (modulesRingSheaf B S hS F hF))
    (hinv : IsInvertible (structureSheaf B S hS F hF).obj
      (structureRingPresheaf_isSheaf B S hS F hF) M)
    (t : SheafOfModules.unit (modulesRingSheaf B S hS F hF) ⟶ M) (ht : t ≠ 0) : Mono t := by
  classical
  obtain ⟨V, hV⟩ : ∃ V : SmallEtale B S hS F,
      t.val.app (op V) (1 : (modulesRingSheaf B S hS F hF).obj.obj (op V)) ≠ 0 := by
    by_contra! hall
    refine ht (M.unitHomEquiv.injective (Subtype.ext (funext fun X => ?_)))
    rw [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe,
      hall X.unop]
    rfl
  have hres : ∀ {U₀ V₀ : SmallEtale B S hS F} (g : V₀ ⟶ U₀),
      M.val.map g.op
          (t.val.app (op U₀) (1 : (modulesRingSheaf B S hS F hF).obj.obj (op U₀))) =
        t.val.app (op V₀) (1 : (modulesRingSheaf B S hS F hF).obj.obj (op V₀)) := by
    intro U₀ V₀ g
    have h := PresheafOfModules.naturality_apply t.val g.op
      (1 : (modulesRingSheaf B S hS F hF).obj.obj (op U₀))
    rw [← h]
    exact congrArg (fun z => t.val.app (op V₀) z)
      (map_one (ConcreteCategory.hom ((modulesRingSheaf B S hS F hF).obj.map g.op)))
  obtain ⟨I, Vi, gi, hcov, hsum⟩ :=
    Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree
      (structureRingPresheaf_isSheaf B S hS F hF) M V
  obtain ⟨i, hi⟩ : ∃ i : I,
      t.val.app (op (Vi i)) (1 : (modulesRingSheaf B S hS F hF).obj.obj (op (Vi i))) ≠ 0 := by
    by_contra! hall
    refine hV (M.isSheaf.isSeparated V _ hcov _ 0 ?_)
    intro Z k hk
    obtain ⟨Y, c, e, he, rfl⟩ := hk
    obtain ⟨i⟩ := he
    change M.val.map (c ≫ gi i).op
        (t.val.app (op V) (1 : (modulesRingSheaf B S hS F hF).obj.obj (op V))) =
      M.val.map (c ≫ gi i).op 0
    rw [map_zero, hres (c ≫ gi i), ← hres c, hall i]
    exact map_zero _
  -- the splitting of Stacks 0B8N (b), read on the charts over `Vi i` instead of on its slice
  -- site, so that the coordinates are regular functions on those charts
  obtain ⟨m, κ, hκ0, hκzero, hκsmul, hκnat⟩ :
      ∃ (m : ℕ) (κ : ∀ Z : SmallEtale B S hS F, (Z ⟶ Vi i) → M.val.obj (op Z) →
            Fin m → (modulesRingSheaf B S hS F hF).obj.obj (op Z)),
        (∀ (Z : SmallEtale B S hS F) (g : Z ⟶ Vi i) (z : M.val.obj (op Z)),
            (∀ k, κ Z g z k = 0) → z = 0) ∧
        (∀ (Z : SmallEtale B S hS F) (g : Z ⟶ Vi i) (k : Fin m), κ Z g 0 k = 0) ∧
        (∀ (Z : SmallEtale B S hS F) (g : Z ⟶ Vi i)
            (a : (modulesRingSheaf B S hS F hF).obj.obj (op Z)) (z : M.val.obj (op Z)) (k : Fin m),
            κ Z g (a • z) k = a * κ Z g z k) ∧
        (∀ (Z Z' : SmallEtale B S hS F) (g : Z ⟶ Vi i) (g' : Z' ⟶ Vi i) (c : Z' ⟶ Z),
            c ≫ g = g' → ∀ (z : M.val.obj (op Z)) (k : Fin m),
            κ Z' g' (M.val.map c.op z) k =
              (modulesRingSheaf B S hS F hF).obj.map c.op (κ Z g z k)) := by
    obtain ⟨n, s, hsplit⟩ := hsum i
    obtain ⟨m, σ, ρ, hsr, hσ, -⟩ :=
      Stacks.SheafOfModules.isRetractOfFiniteFree_of_isSplitMono_pi s hsplit
    refine ⟨m, fun Z g z k => σ (op (Over.mk g)) z k, ?_, ?_, ?_, ?_⟩
    · intro Z g z hz
      have h1 := hsr (op (Over.mk g)) z
      rw [show σ (op (Over.mk g)) z = 0 from Finsupp.ext hz, map_zero] at h1
      exact h1.symm
    · intro Z g k
      exact congrArg (fun c : Fin m →₀ _ => c k) (map_zero (σ (op (Over.mk g))))
    · intro Z g a z k
      exact congrArg (fun c : Fin m →₀ _ => c k) ((σ (op (Over.mk g))).map_smul a z)
    · intro Z Z' g g' c hc z k
      subst hc
      exact hσ (Over.homMk c rfl : Over.mk (c ≫ g) ⟶ Over.mk g).op z k
  have hlin : ∀ {Z : SmallEtale B S hS F}
      (a : (modulesRingSheaf B S hS F hF).obj.obj (op Z)),
      t.val.app (op Z) a =
        a • t.val.app (op Z) (1 : (modulesRingSheaf B S hS F hF).obj.obj (op Z)) := by
    intro Z a
    have h : t.val.app (op Z)
          (a * (1 : (modulesRingSheaf B S hS F hF).obj.obj (op Z))) =
        a • t.val.app (op Z) (1 : (modulesRingSheaf B S hS F hF).obj.obj (op Z)) :=
      (t.val.app (op Z)).hom.map_smul a
        (1 : (modulesRingSheaf B S hS F hF).obj.obj (op Z))
    rwa [mul_one] at h
  obtain ⟨j, hj⟩ : ∃ j : Fin m, κ (Vi i) (𝟙 (Vi i))
      (t.val.app (op (Vi i))
        (1 : (modulesRingSheaf B S hS F hF).obj.obj (op (Vi i)))) j ≠ 0 := by
    by_contra! hall
    exact hi (hκ0 (Vi i) (𝟙 (Vi i)) _ hall)
  refine (SheafOfModules.forget (modulesRingSheaf B S hS F hF)).mono_of_mono_map
    (f := t) (PresheafOfModules.mono_of_injective ?_)
  intro X x y hxy
  have hxy' : t.val.app X x = t.val.app X y := hxy
  suffices hsub : x - y = 0 from sub_eq_zero.mp hsub
  by_contra hxne
  have htx : t.val.app X (x - y) = 0 := by
    have h := (t.val.app X).hom.map_sub x y
    rw [hxy', sub_self] at h
    exact h
  obtain ⟨W, p, q, w, hw1, hw2⟩ := exists_common_chart_mem_basicOpen B S hS F hF hint
    X.unop (Vi i) (x - y)
    (κ (Vi i) (𝟙 (Vi i))
      (t.val.app (op (Vi i))
        (1 : (modulesRingSheaf B S hS F hF).obj.obj (op (Vi i)))) j) hxne hj
  have hnat : κ W q (t.val.app (op W) (1 : (modulesRingSheaf B S hS F hF).obj.obj (op W))) j =
      (modulesRingSheaf B S hS F hF).obj.map q.op
        (κ (Vi i) (𝟙 (Vi i))
          (t.val.app (op (Vi i))
            (1 : (modulesRingSheaf B S hS F hF).obj.obj (op (Vi i)))) j) := by
    have h := hκnat (Vi i) W (𝟙 (Vi i)) q q (by simp)
      (t.val.app (op (Vi i)) (1 : (modulesRingSheaf B S hS F hF).obj.obj (op (Vi i)))) j
    rwa [hres q] at h
  have hzero : (modulesRingSheaf B S hS F hF).obj.map p.op (x - y) *
      (modulesRingSheaf B S hS F hF).obj.map q.op
        (κ (Vi i) (𝟙 (Vi i))
          (t.val.app (op (Vi i))
            (1 : (modulesRingSheaf B S hS F hF).obj.obj (op (Vi i)))) j) = 0 := by
    have hzeroW : ((modulesRingSheaf B S hS F hF).obj.map p.op (x - y)) •
        t.val.app (op W) (1 : (modulesRingSheaf B S hS F hF).obj.obj (op W)) = 0 := by
      rw [← hlin ((modulesRingSheaf B S hS F hF).obj.map p.op (x - y))]
      have h := PresheafOfModules.naturality_apply t.val p.op (x - y)
      rw [htx, map_zero] at h
      exact h
    have h := hκsmul W q ((modulesRingSheaf B S hS F hF).obj.map p.op (x - y))
      (t.val.app (op W) (1 : (modulesRingSheaf B S hS F hF).obj.obj (op W))) j
    rw [hzeroW, hκzero W q j, hnat] at h
    exact h.symm
  have hzero' : ((BigFppfOver.toScheme B S hS).map p.hom.left).appTop (x - y) *
      ((BigFppfOver.toScheme B S hS).map q.hom.left).appTop
        (κ (Vi i) (𝟙 (Vi i))
          (t.val.app (op (Vi i))
            (1 : (modulesRingSheaf B S hS F hF).obj.obj (op (Vi i)))) j) = 0 := hzero
  have hmem : pointsToScheme B S hS W.obj.left w ∈
      (chartScheme W).basicOpen
        (((BigFppfOver.toScheme B S hS).map p.hom.left).appTop (x - y) *
          ((BigFppfOver.toScheme B S hS).map q.hom.left).appTop
            (κ (Vi i) (𝟙 (Vi i))
              (t.val.app (op (Vi i))
                (1 : (modulesRingSheaf B S hS F hF).obj.obj (op (Vi i)))) j)) := by
    rw [Scheme.basicOpen_mul]
    exact ⟨hw1, hw2⟩
  rw [hzero'] at hmem
  simp at hmem

/-! ### Triviality from a monomorphism out of the inverse -/

/-- A module with a nonzero global section receives a nonzero morphism from `𝒪_F`. -/
private theorem exists_ne_zero_unit_hom (L : SheafOfModules.{u} (modulesRingSheaf B S hS F hF))
    (hL : Nontrivial L.sections) :
    ∃ a : SheafOfModules.unit (modulesRingSheaf B S hS F hF) ⟶ L, a ≠ 0 := by
  have _ : Nontrivial (SheafOfModules.unit (modulesRingSheaf B S hS F hF) ⟶ L) :=
    L.unitHomEquiv.nontrivial
  exact exists_ne 0

/-- **The formal half of Stacks 0DMZ.**  Let `H⁰(F, 𝒪_F)` be a field and let `L` be an
invertible `𝒪_F`-module with a nonzero global section.  If some global section of `L^{⊗ -1}` is
a monomorphism `𝒪_F ⟶ L^{⊗ -1}` then `L ≅ 𝒪_F`.

Tensoring the monomorphism by `L` and using `L^{⊗ -1} ⊗ L ≅ 𝒪_F` turns it into a
monomorphism `b : L ⟶ 𝒪_F`; composing a nonzero section `a : 𝒪_F ⟶ L` with it gives a nonzero
endomorphism of `𝒪_F`, hence an isomorphism, and `a` is then a split monomorphism with mono
retraction, so an isomorphism. -/
theorem isTrivial_of_mono_of_isField (hfield : IsField (globalFunctions B S hS F))
    (L : SheafOfModules.{u} (modulesRingSheaf B S hS F hF))
    [IsInvertible (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF) L]
    (hL : Nontrivial L.sections)
    (t : SheafOfModules.unit (modulesRingSheaf B S hS F hF) ⟶
      tensorPower (structureSheaf B S hS F hF).obj
        (structureRingPresheaf_isSheaf B S hS F hF) L (-1))
    [Mono t] :
    IsTrivial (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF) L := by
  let rightTensor : SheafOfModules.{u} (modulesRingSheaf B S hS F hF) ⥤
      SheafOfModules.{u} (modulesRingSheaf B S hS F hF) :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨(structureSheaf B S hS F hF).obj, Presheaf.isSheaf_of_isSheaf_comp _
        (structureSheaf B S hS F hF).obj (forget₂ CommRingCat RingCat)
        (structureRingPresheaf_isSheaf B S hS F hF)⟩).flip.obj L
  let : rightTensor.IsEquivalence :=
    Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible
      (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF) L
  have e : rightTensor.obj
      (SheafOfModules.unit (modulesRingSheaf B S hS F hF)) ≅ L :=
    (tensorPowerSuccIso (structureSheaf B S hS F hF).obj
          (structureRingPresheaf_isSheaf B S hS F hF) L 0).trans
      ((tensorPowerReindex (structureSheaf B S hS F hF).obj
            (structureRingPresheaf_isSheaf B S hS F hF) L (zero_add (1 : ℤ))).trans
        (tensorPowerOneIso (structureSheaf B S hS F hF).obj
          (structureRingPresheaf_isSheaf B S hS F hF) L))
  have d : rightTensor.obj
      (tensorPower (structureSheaf B S hS F hF).obj
        (structureRingPresheaf_isSheaf B S hS F hF) L (-1)) ≅
      SheafOfModules.unit (modulesRingSheaf B S hS F hF) :=
    rightTensor.asEquivalence.counitIso.app
      (SheafOfModules.unit (modulesRingSheaf B S hS F hF))
  let : Mono (rightTensor.map t) := Functor.map_mono rightTensor t
  obtain ⟨b, hb⟩ : ∃ b : L ⟶ SheafOfModules.unit
      (modulesRingSheaf B S hS F hF), Mono b :=
    ⟨e.inv ≫ rightTensor.map t ≫ d.hom, inferInstance⟩
  have _ := hb
  obtain ⟨a, ha⟩ := exists_ne_zero_unit_hom B S hS F hF L hL
  have hab : a ≫ b ≠ 0 := by
    intro h
    exact ha ((cancel_mono b).mp (by simpa using h))
  have _ : IsIso (a ≫ b) :=
    isIso_of_ne_zero B S hS F hF hfield (End.of (a ≫ b)) fun h => hab congr(($h).asHom)
  exact ⟨(Iso.mk a (b ≫ inv (a ≫ b)) (by simp [← Category.assoc])
    (by apply (cancel_mono b).mp; simp [Category.assoc])).symm⟩

/-! ### Triviality of an invertible module with sections in degrees `1` and `-1` -/

/-- **Stacks 0DMZ.**  Let `F` be an integral algebraic space whose ring `H⁰(F, 𝒪_F)` of global
regular functions is a field, and let `L` be an invertible `𝒪_F`-module.  If `H⁰(F, L)` and
`H⁰(F, L^{⊗ -1})` are both nonzero then `L ≅ 𝒪_F`.

The source states this for a proper integral algebraic space over a field `k`, and uses
properness only through Tag 0DMY, that `H⁰(F, 𝒪_F)` is then a field.  That result is not
available in this library, so it is carried here as the hypothesis `hfield`; the base is
correspondingly an arbitrary scheme rather than the spectrum of a field. -/
@[stacks 0DMZ "granted that H⁰(F, 𝒪_F) is a field, which Tag 0DMY draws from properness"]
theorem isTrivial_of_nontrivial_sections (hint : IsIntegralSpace B S hS F)
    (hfield : IsField (globalFunctions B S hS F))
    (L : SheafOfModules.{u} (modulesRingSheaf B S hS F hF))
    [IsInvertible (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF) L]
    (hL : Nontrivial L.sections)
    (hLinv : Nontrivial (tensorPower (structureSheaf B S hS F hF).obj
      (structureRingPresheaf_isSheaf B S hS F hF) L (-1)).sections) :
    IsTrivial (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF) L := by
  classical
  obtain ⟨t, htne⟩ := exists_ne_zero_unit_hom B S hS F hF _ hLinv
  have _ : Mono t :=
    mono_of_ne_zero B S hS F hF hint _
      (Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower
        (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF) L (-1))
      t htne
  exact isTrivial_of_mono_of_isField B S hS F hF hfield L hL t

end AlgebraicGeometry.Space

end
