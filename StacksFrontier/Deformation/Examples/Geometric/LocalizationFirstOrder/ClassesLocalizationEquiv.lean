module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Derivation.ToSquareZero
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Smooth.Locus
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.LocalizedSplitting
public import StacksFrontier.Deformation.SquareZero.AlgebraExtensions
public import StacksFrontier.Deformation.Examples.Geometric.LocalizationFirstOrder.LocalizedExtension
import all StacksFrontier.Deformation.Examples.Geometric.LocalizationFirstOrder.LocalizedExtension
public import StacksFrontier.Deformation.Examples.Geometric.LocalizationFirstOrder.RelationMap
import all StacksFrontier.Deformation.Examples.Geometric.LocalizationFirstOrder.RelationMap

/-!
# First-order extensions and localization

Let `k` be a field, let `B` be a finite type `k`-algebra, and let `S` be a multiplicative subset
of `B` which meets no prime in the non-smooth locus. Localization induces a canonical bijection
between square-zero extensions of `B` by a module `N` and square-zero extensions of `S⁻¹B` by
`S⁻¹N`.

## Main results

* `Deformation.Examples.squareZeroAlgebraExtensionClassesLocalizationEquiv` is the equivalence
  on isomorphism classes of square-zero extensions.
* `Deformation.Examples.squareZeroAlgebraExtensionClassesLocalizationEquiv_apply` says that its
  forward map sends each extension to its localization.

## Implementation notes

The source's `Exal` sets are represented by the isomorphism classes of
`Stacks.Deformation.algebraExtensionProblem`. The chosen models of the two localizations are
`Localization S` and `LocalizedModule S N`. Smoothness at a prime is expressed by Mathlib's
`Algebra.IsSmoothAt`, which lets the field and the algebra live in independent universes.

The finiteness assumption that the source places on `N` is omitted: the argument applies to
every `B`-module, so the statement proved here is more general than the source's.

Projecting a field out of `Stacks.Deformation.algebraExtensionProblem` needs that definition to
be unfolded, which `implicit` transparency does not do, so instance synthesis and the `rfl`
closing `rw` decline on goals that print as `X = X`. The single local attribute below opens that
definition up for the whole file.

## References

* [Stacks Project, Tag 0DZ8](https://stacks.math.columbia.edu/tag/0DZ8)
-/

@[expose] public section

universe uk uB uN uP

namespace Deformation.Examples

open Stacks.Deformation

attribute [local implicit_reducible] Stacks.Deformation.algebraExtensionProblem

/-- A conormal relation map is realized by quotienting the trivial square-zero extension by
its graph. -/
private theorem exists_extension_of_cotangentMap
    {k : Type uk} {B : Type uB} {N : Type uN} [Field k] [CommRing B] [Algebra k B]
    [AddCommGroup N] [Module B N]
    (P : Algebra.Extension.{uP} k B) (l : P.Cotangent →ₗ[B] N) :
    ∃ X : (algebraExtensionProblem k B N).CompatibleExtension.{max uP uN},
      letI : Algebra k X.B' := X.algebraA'B'
      ∃ f : P.Ring →ₐ[k] X.B',
        (∀ p, X.toB (f p) = algebraMap P.Ring B p) ∧
        ∀ p : P.ker,
          (X.kernelEquiv (l (Algebra.Extension.Cotangent.mk p)) : X.B') = f p := by
  classical
  let f : P.Ring →+* B := algebraMap P.Ring B
  let : Module P.Ring N := Module.compHom N f
  let : Module k N := Module.compHom N (algebraMap k B)
  let : IsScalarTower k P.Ring N := IsScalarTower.of_algebraMap_smul (by
    intro a n
    change f (algebraMap k P.Ring a) • n = (algebraMap k B a) • n
    exact congrArg (fun b : B ↦ b • n)
      (IsScalarTower.algebraMap_apply k P.Ring B a).symm)
  let : IsScalarTower P.Ring B N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module P.Ringᵐᵒᵖ N := Module.compHom N
    ({ toFun := MulOpposite.unop
       map_one' := rfl
       map_mul' := by intro x y; exact mul_comm _ _
       map_zero' := rfl
       map_add' := by intro x y; rfl } : P.Ringᵐᵒᵖ →+* P.Ring)
  let : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  let : Algebra k (TrivSqZeroExt P.Ring N) := TrivSqZeroExt.algebra' k P.Ring N
  let lI : P.ker →ₗ[P.Ring] N :=
    (l.restrictScalars P.Ring).comp Algebra.Extension.Cotangent.mk
  have hI (i : P.Ring) (hi : i ∈ P.ker) (n : N) : i • n = 0 := by
    change f i • n = 0
    rw [show f i = 0 from hi, zero_smul]
  have hIop (i : P.Ring) (hi : i ∈ P.ker) (n : N) :
      MulOpposite.op i • n = 0 := hI i hi n
  let J := squareZeroRelationIdeal P.ker lI hIop
  let C := TrivSqZeroExt P.Ring N ⧸ J
  let q : C →+* B := squareZeroRelationQuotientMap P.ker lI hIop f rfl.le
  let : Algebra k C := ((Ideal.Quotient.mk J).comp
    (algebraMap k (TrivSqZeroExt P.Ring N))).toAlgebra
  let qA : C →ₐ[k] B :=
    { toRingHom := q
      commutes' := by
        intro a
        change q (Ideal.Quotient.mk J (algebraMap k (TrivSqZeroExt P.Ring N) a)) =
          algebraMap k B a
        change f ((algebraMap k (TrivSqZeroExt P.Ring N) a).fst) = _
        rw [show (algebraMap k (TrivSqZeroExt P.Ring N) a).fst =
          algebraMap k P.Ring a from rfl]
        exact (IsScalarTower.algebraMap_apply k P.Ring B a).symm }
  let eA := squareZeroRelationKernelAddEquiv P.ker lI hIop f rfl
  let : Module B (RingHom.ker q) := eA.symm.module B
  let e : N ≃ₗ[B] RingHom.ker q :=
    { toFun := eA
      invFun := eA.symm
      left_inv := eA.left_inv
      right_inv := eA.right_inv
      map_add' := eA.map_add
      map_smul' := by
        intro b n
        change eA (b • n) = eA (b • eA.symm (eA n))
        rw [eA.symm_apply_apply] }
  let X : (algebraExtensionProblem k B N).CompatibleExtension := by
    dsimp only [algebraExtensionProblem]
    exact
      { B' := C
        toB := qA
        surjective := squareZeroRelationQuotientMap_surjective P.ker lI hIop f
          rfl.le P.algebraMap_surjective
        sq_zero := squareZeroRelationQuotientMap_sq_zero P.ker lI hI hIop f rfl
        moduleKernel := inferInstance
        toB_smul_kernel := by
          intro c x
          obtain ⟨n, rfl⟩ := e.surjective x
          exact squareZeroRelationKernel_smul P.ker lI hIop f rfl
            (fun _ _ ↦ rfl) c n
        kernelEquiv := e
        map_I := by
          intro i
          have hi : (i : k) = 0 := i.2
          change (e (0 : N) : C) = algebraMap k C i
          simp [hi] }
  let : Algebra k X.B' := X.algebraA'B'
  let fX : P.Ring →ₐ[k] X.B' :=
    { (Ideal.Quotient.mk J).comp (TrivSqZeroExt.inlHom P.Ring N) with
      commutes' := fun _ ↦ rfl }
  refine ⟨X, fX, fun _ ↦ rfl, ?_⟩
  intro p
  change Ideal.Quotient.mk J (TrivSqZeroExt.inr (lI p)) =
    Ideal.Quotient.mk J (TrivSqZeroExt.inl (p : P.Ring))
  apply Ideal.Quotient.eq.mpr
  change TrivSqZeroExt.inr (lI p) - TrivSqZeroExt.inl (p : P.Ring) ∈ J
  refine ⟨-p, ?_⟩
  apply TrivSqZeroExt.ext
  · simp
  · simp [lI]

/-- The identified kernel of an extension turns subtraction into subtraction in the middle ring. -/
private theorem coe_kernelEquiv_sub {P : SquareZeroExtensionProblem} (X : P.CompatibleExtension)
    (a b : P.N) :
    (X.kernelEquiv (a - b) : X.B') = X.kernelEquiv a - X.kernelEquiv b := by
  rw [map_sub, AddSubgroupClass.coe_sub]

/-- A ring map between two localized extensions that is compatible with the maps from a common
extension `X` on the middle rings is also compatible with the identified kernels. -/
private theorem map_kernelEquiv_of_localized
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (X : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)})
    (Y Z : (algebraExtensionProblem k (Localization S)
      (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)})
    (f : X.B' →+* Y.B') (g : X.B' →+* Z.B') (φ : Y.B' →+* Z.B') (hφ : ∀ c, φ (f c) = g c)
    (hfq : ∀ c, Y.toB (f c) = algebraMap B (Localization S) (X.toB c))
    (hgq : ∀ c, Z.toB (g c) = algebraMap B (Localization S) (X.toB c))
    (hfn : ∀ n : N, f (X.kernelEquiv n) =
      (Y.kernelEquiv (LocalizedModule.mkLinearMap S N n) : Y.B'))
    (hgn : ∀ n : N, g (X.kernelEquiv n) =
      (Z.kernelEquiv (LocalizedModule.mkLinearMap S N n) : Z.B'))
    (hu : ∀ c, X.toB c ∈ S → IsUnit (g c)) (n : LocalizedModule S N) :
    φ (Y.kernelEquiv n) = (Z.kernelEquiv n : Z.B') := by
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S N) n
  obtain ⟨c, hc⟩ := X.surjective (s : B)
  have key (W : (algebraExtensionProblem k (Localization S)
      (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)}) (y : W.B')
      (hy : W.toB y = algebraMap B (Localization S) (X.toB c)) :
      (W.kernelEquiv (LocalizedModule.mkLinearMap S N m) : W.B') =
        y * (W.kernelEquiv n : W.B') := by
    rw [← kernelEquiv_smul_toB, hy, hc, ← hs]
    exact congrArg (fun x ↦ (W.kernelEquiv x : W.B'))
      (IsScalarTower.algebraMap_smul (Localization S) (s : B) n).symm
  apply (hu c (by rw [hc]; exact s.property)).mul_right_injective
  calc g c * φ (Y.kernelEquiv n) = φ (f c * (Y.kernelEquiv n : Y.B')) := by rw [map_mul, hφ]
    _ = φ (Y.kernelEquiv (LocalizedModule.mkLinearMap S N m)) := by rw [key Y _ (hfq c)]
    _ = g (X.kernelEquiv m) := by rw [← hfn, hφ]
    _ = (Z.kernelEquiv (LocalizedModule.mkLinearMap S N m) : Z.B') := hgn m
    _ = g c * (Z.kernelEquiv n : Z.B') := key Z _ (hgq c)

/-- Being the localization of an extension only depends on the isomorphism class of the
target extension. -/
private theorem isLocalizedExtension_of_iso_right
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (X : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)})
    (Y Z : (algebraExtensionProblem k (Localization S)
      (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)})
    (h : IsLocalizedExtension k B S N X Y)
    (e : SquareZeroExtensionProblem.CompatibleExtension.Iso Y Z) :
    IsLocalizedExtension k B S N X Z := by
  let : Algebra k X.B' := X.algebraA'B'
  let : Algebra k Y.B' := Y.algebraA'B'
  let : Algebra k Z.B' := Z.algebraA'B'
  obtain ⟨f, hf, hfq, hfn⟩ := h
  let eA : Y.B' ≃ₐ[k] Z.B' := e.toAlgEquiv
  refine ⟨eA.toAlgHom.comp f, hf.mulEquiv_comp eA, ?_, ?_⟩
  · intro c
    exact (DFunLike.congr_fun e.toB_comm (f c)).trans (hfq c)
  · intro n
    change e.toAlgEquiv (f (X.kernelEquiv n)) = _
    rw [hfn, e.kernelEquiv_comm]

/-- Two localizations of the same extension are isomorphic. -/
private theorem isomorphic_of_isLocalizedExtension
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (X : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)})
    (Y Z : (algebraExtensionProblem k (Localization S)
      (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)})
    (hY : IsLocalizedExtension k B S N X Y)
    (hZ : IsLocalizedExtension k B S N X Z) :
    SquareZeroExtensionProblem.CompatibleExtension.Isomorphic Y Z := by
  classical
  let : Algebra k X.B' := X.algebraA'B'
  let : Algebra k Y.B' := Y.algebraA'B'
  let : Algebra k Z.B' := Z.algebraA'B'
  obtain ⟨f, hf, hfq, hfn⟩ := hY
  obtain ⟨g, hg, hgq, hgn⟩ := hZ
  let T : Submonoid X.B' := S.comap X.toB.toRingHom
  let : Algebra X.B' Y.B' := f.toRingHom.toAlgebra
  let : Algebra X.B' Z.B' := g.toRingHom.toAlgebra
  let : IsLocalization T Y.B' := (isLocalization_iff_isLocalizationMap T Y.B').mpr hf
  let : IsLocalization T Z.B' := (isLocalization_iff_isLocalizationMap T Z.B').mpr hg
  let eR : Y.B' ≃ₐ[X.B'] Z.B' := IsLocalization.algEquiv T Y.B' Z.B'
  have hef (c : X.B') : eR (f c) = g c := eR.commutes c
  let e : Y.B' ≃ₐ[k] Z.B' :=
    { eR.toRingEquiv with
      commutes' a := by
        change eR (algebraMap k Y.B' a) = algebraMap k Z.B' a
        rw [← f.commutes, hef, g.commutes] }
  have heq : Z.toB.comp e.toAlgHom = Y.toB := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext T
    ext c
    change Z.toB (eR (f c)) = Y.toB (f c)
    rw [hef, hgq, hfq]
  refine ⟨⟨e, heq, ?_⟩⟩
  exact map_kernelEquiv_of_localized k B S N X Y Z f.toRingHom g.toRingHom eR.toRingEquiv.toRingHom
    hef (fun c ↦ hfq c) (fun c ↦ hgq c) hfn hgn (fun c hc ↦ hg.map_units ⟨c, hc⟩)

/-- A ring element whose image is a unit modulo a square-zero ideal is a unit. -/
private theorem isUnit_of_map_of_ker_sq_zero
    {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A)
    (hf : Function.Surjective f) (hker : (RingHom.ker f) ^ 2 = ⊥)
    (r : R) (hr : IsUnit (f r)) : IsUnit r := by
  obtain ⟨a, ha⟩ := hf (↑hr.unit⁻¹)
  have hmem : r * a - 1 ∈ RingHom.ker f := by
    change f (r * a - 1) = 0
    rw [map_sub, map_mul, map_one, ha, hr.mul_val_inv, sub_self]
  have hnil : IsNilpotent (r * a - 1) := by
    refine ⟨2, ?_⟩
    have hh := Ideal.mul_mem_mul hmem hmem
    rw [← pow_two, hker] at hh
    simpa only [pow_two, Ideal.mem_bot] using hh
  exact (IsUnit.mul_iff.mp (by simpa using hnil.isUnit_add_one)).1

/-- Any map of extensions inducing the localization maps on quotient and kernel already
exhibits the target as the localization of the source. -/
private theorem isLocalizedExtension_of_compatibleAlgHom
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (X : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)})
    (Y : (algebraExtensionProblem k (Localization S)
      (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)}) :
    let : Algebra k X.B' := X.algebraA'B'
    let : Algebra k Y.B' := Y.algebraA'B'
    ∀ (f : X.B' →ₐ[k] Y.B')
    (_ : ∀ c, Y.toB (f c) = algebraMap B (Localization S) (X.toB c))
    (_ : ∀ n : N, f (X.kernelEquiv n) =
      (Y.kernelEquiv (LocalizedModule.mkLinearMap S N n) : Y.B')),
    IsLocalizedExtension k B S N X Y := by
  classical
  let : Algebra k X.B' := X.algebraA'B'
  let : Algebra k Y.B' := Y.algebraA'B'
  intro _ _ f hfq hfn
  obtain ⟨Z, hZ⟩ := exists_localizedExtension k B S N X
  let : Algebra k Z.B' := Z.algebraA'B'
  have hZ' := hZ
  obtain ⟨a, ha, haq, han⟩ := hZ'
  let T : Submonoid X.B' := S.comap X.toB.toRingHom
  have hfu (t : T) : IsUnit (f t) := by
    apply isUnit_of_map_of_ker_sq_zero Y.toB.toRingHom Y.surjective Y.sq_zero
    rw [show Y.toB.toRingHom (f t) = algebraMap B (Localization S) (X.toB t) from hfq t]
    exact IsLocalization.map_units (Localization S) (⟨X.toB t, t.property⟩ : S)
  let : Algebra X.B' Z.B' := a.toRingHom.toAlgebra
  let : IsLocalization T Z.B' := (isLocalization_iff_isLocalizationMap T Z.B').mpr ha
  let gR : Z.B' →+* Y.B' := IsLocalization.lift (g := f.toRingHom) hfu
  have hga (c : X.B') : gR (a c) = f c := IsLocalization.lift_eq hfu c
  let g : Z.B' →ₐ[k] Y.B' :=
    { gR with
      commutes' c := by
        rw [← a.commutes c]
        exact (hga _).trans (f.commutes c) }
  have hgq : Y.toB.comp g = Z.toB := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext T
    ext c
    change Y.toB (gR (a c)) = Z.toB (a c)
    rw [hga, hfq, haq]
  have hgn (n : LocalizedModule S N) :
      g (Z.kernelEquiv n) = (Y.kernelEquiv n : Y.B') :=
    map_kernelEquiv_of_localized k B S N X Z Y a.toRingHom f.toRingHom gR hga
      (fun c ↦ haq c) (fun c ↦ hfq c) han hfn (fun c hc ↦ hfu ⟨c, hc⟩) n
  obtain ⟨e⟩ := isomorphic_of_compatibleAlgHom Z Y g hgq hgn
  exact isLocalizedExtension_of_iso_right k B S N X Z Y hZ e

/-- Two extensions with the same localization are isomorphic, provided localization is
injective on the relevant cokernel of the dual cotangent differential. -/
private theorem isomorphic_of_common_localization
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (P : Algebra.Extension k B) [Algebra.FormallySmooth k P.Ring]
    (hcot : Function.Injective (precompCokernelMap P.cotangentComplex
      (LocalizedModule.mkLinearMap S N)))
    (X X' : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)})
    (Y : (algebraExtensionProblem k (Localization S)
      (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)})
    (hX : IsLocalizedExtension k B S N X Y)
    (hX' : IsLocalizedExtension k B S N X' Y) :
    SquareZeroExtensionProblem.CompatibleExtension.Isomorphic X X' := by
  classical
  let : Algebra k X.B' := X.algebraA'B'
  let : Algebra k X'.B' := X'.algebraA'B'
  let : Algebra k Y.B' := Y.algebraA'B'
  let j : N →ₗ[B] LocalizedModule S N := LocalizedModule.mkLinearMap S N
  obtain ⟨a, _, haq, han⟩ := hX
  obtain ⟨a', _, haq', han'⟩ := hX'
  obtain ⟨f, l, hf, hl⟩ := exists_lift_and_cotangentMap P X
  obtain ⟨f', l', hf', hl'⟩ := exists_lift_and_cotangentMap P X'
  let g : P.Ring →ₐ[k] Y.B' := a.comp f
  let g' : P.Ring →ₐ[k] Y.B' := a'.comp f'
  have hg (p : P.Ring) : Y.toB (g p) =
      algebraMap B (Localization S) (algebraMap P.Ring B p) := by
    change Y.toB (a (f p)) = _
    rw [haq, hf]
  have hg' (p : P.Ring) : Y.toB (g' p) =
      algebraMap B (Localization S) (algebraMap P.Ring B p) := by
    change Y.toB (a' (f' p)) = _
    rw [haq', hf']
  have hlg (p : P.ker) :
      (Y.kernelEquiv (j (l (Algebra.Extension.Cotangent.mk p))) : Y.B') = g p :=
    (han (l (Algebra.Extension.Cotangent.mk p))).symm.trans (congrArg a (hl p))
  have hlg' (p : P.ker) :
      (Y.kernelEquiv (j (l' (Algebra.Extension.Cotangent.mk p))) : Y.B') = g' p :=
    (han' (l' (Algebra.Extension.Cotangent.mk p))).symm.trans (congrArg a' (hl' p))
  obtain ⟨t, ht⟩ := exists_cotangentSpaceMap_of_lift_difference P Y g g' hg hg'
  have hcomp : j.comp (l - l') = t.comp P.cotangentComplex := by
    ext x
    obtain ⟨p, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    apply Y.kernelEquiv.injective
    apply Subtype.ext
    change (Y.kernelEquiv (j (l (Algebra.Extension.Cotangent.mk p) -
      l' (Algebra.Extension.Cotangent.mk p))) : Y.B') =
        (Y.kernelEquiv (t (1 ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring p)) : Y.B')
    rw [map_sub, coe_kernelEquiv_sub, hlg p, hlg' p, ht p]
  have heq : precompCokernelMap P.cotangentComplex j (Submodule.Quotient.mk l) =
      precompCokernelMap P.cotangentComplex j (Submodule.Quotient.mk l') := by
    simp only [precompCokernelMap_mk]
    rw [LinearMap.comp_sub] at hcomp
    exact (Submodule.Quotient.eq _).2 ⟨t, hcomp.symm⟩
  obtain ⟨v, hv⟩ := (Submodule.Quotient.eq _).1 (hcot heq)
  obtain ⟨f'', hf'', hff''⟩ :=
    exists_lift_adjusted_by_cotangentSpaceMap P X' f' hf' v
  have hl'' (p : P.ker) :
      (X'.kernelEquiv (l (Algebra.Extension.Cotangent.mk p)) : X'.B') = f'' p := by
    have hvp : v (P.cotangentComplex (Algebra.Extension.Cotangent.mk p)) =
        l (Algebra.Extension.Cotangent.mk p) - l' (Algebra.Extension.Cotangent.mk p) :=
      DFunLike.congr_fun hv _
    rw [Algebra.Extension.cotangentComplex_mk] at hvp
    rw [hff'' p, ← hl' p, hvp, coe_kernelEquiv_sub]
    abel
  exact isomorphic_of_equal_cotangentMap P X X' f f'' hf hf'' l hl hl''

/-- Every extension of `S⁻¹B` by `S⁻¹N` is the localization of an extension of `B` by `N`,
provided localization is surjective on the relevant cokernel of the dual cotangent
differential. -/
private theorem exists_original_of_localizedExtension
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (P : Algebra.Extension.{max uk uB} k B) [Algebra.FormallySmooth k P.Ring]
    (hcot : Function.Surjective (precompCokernelMap P.cotangentComplex
      (LocalizedModule.mkLinearMap S N)))
    (Y : (algebraExtensionProblem k (Localization S)
      (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)}) :
    ∃ X : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)},
      IsLocalizedExtension k B S N X Y := by
  classical
  let : Algebra k Y.B' := Y.algebraA'B'
  let j : N →ₗ[B] LocalizedModule S N := LocalizedModule.mkLinearMap S N
  let h : P.Ring →ₐ[k] Localization S :=
    (IsScalarTower.toAlgHom k B (Localization S)).comp
      (IsScalarTower.toAlgHom k P.Ring B)
  let g : P.Ring →ₐ[k] Y.B' := Algebra.FormallySmooth.liftOfSurjective
    h Y.toB Y.surjective ⟨2, Y.sq_zero⟩
  have hg (p : P.Ring) : Y.toB (g p) =
      algebraMap B (Localization S) (algebraMap P.Ring B p) :=
    Algebra.FormallySmooth.liftOfSurjective_apply h Y.toB Y.surjective
      ⟨2, Y.sq_zero⟩ p
  obtain ⟨m, hm⟩ := exists_cotangentMap_of_lift_localized S P Y g hg
  obtain ⟨c, hc⟩ := hcot (Submodule.Quotient.mk m)
  obtain ⟨l, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (LinearMap.lcomp B N P.cotangentComplex)) c
  let Q := (P.Cotangent →ₗ[B] LocalizedModule S N) ⧸
    LinearMap.range (LinearMap.lcomp B (LocalizedModule S N) P.cotangentComplex)
  have heq : (Submodule.Quotient.mk (j.comp l) : Q) =
      (Submodule.Quotient.mk m : Q) := by
    change precompCokernelMap P.cotangentComplex j (Submodule.Quotient.mk l) =
      Submodule.Quotient.mk m at hc
    rw [precompCokernelMap_mk] at hc
    exact hc
  obtain ⟨t, ht⟩ := (Submodule.Quotient.eq _).1 heq
  obtain ⟨g', hg', hgg'⟩ :=
    exists_lift_adjusted_by_cotangentSpaceMap P Y g hg t
  have hrel (p : P.ker) :
      (Y.kernelEquiv (j (l (Algebra.Extension.Cotangent.mk p))) : Y.B') = g' p := by
    have htp : t (P.cotangentComplex (Algebra.Extension.Cotangent.mk p)) =
        j (l (Algebra.Extension.Cotangent.mk p)) - m (Algebra.Extension.Cotangent.mk p) :=
      DFunLike.congr_fun ht _
    rw [Algebra.Extension.cotangentComplex_mk] at htp
    rw [hgg' p, ← hm p, htp, coe_kernelEquiv_sub]
    abel
  obtain ⟨X, fX, hfX, hlX⟩ := exists_extension_of_cotangentMap P l
  obtain ⟨F, hq, hn⟩ :=
    exists_compatibleAlgHom_of_cotangentMap P X Y j fX g' hfX hg' l hlX hrel
  exact ⟨X, isLocalizedExtension_of_compatibleAlgHom k B S N X Y F hq hn⟩

/-- Localization as a map on isomorphism classes of square-zero extensions. -/
private noncomputable def localizationMap
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N] :
    SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB, uN,
        max uk (max uB uN)} (algebraExtensionProblem k B N) →
      SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB,
        max uB uN, max uk (max uB uN)}
        (algebraExtensionProblem k (Localization S) (LocalizedModule S N)) :=
  Quotient.map (fun X ↦ (exists_localizedExtension k B S N X).choose) (by
    rintro X X' ⟨e⟩
    exact isomorphic_of_isLocalizedExtension k B S N X _ _
      (exists_localizedExtension k B S N X).choose_spec
      (isLocalizedExtension_of_iso k B S N X X' _ e
        (exists_localizedExtension k B S N X').choose_spec))

/-- `Deformation.Examples.localizationMap` sends the class of `X` to the class of any
localization of `X`. -/
private theorem localizationMap_mk
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (X : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)})
    (Y : (algebraExtensionProblem k (Localization S)
      (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)})
    (hY : IsLocalizedExtension k B S N X Y) :
    localizationMap k B S N ⟦X⟧ = ⟦Y⟧ :=
  Quotient.sound (isomorphic_of_isLocalizedExtension k B S N X _ Y
    (exists_localizedExtension k B S N X).choose_spec hY)

/-- `Deformation.Examples.localizationMap` is bijective exactly when every extension of
`S⁻¹B` by `S⁻¹N` comes from an extension of `B` by `N`, uniquely up to isomorphism. -/
private theorem bijective_localizationMap_iff
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N] :
    Function.Bijective (localizationMap k B S N) ↔
      (∀ X X' Y, IsLocalizedExtension k B S N X Y → IsLocalizedExtension k B S N X' Y →
        SquareZeroExtensionProblem.CompatibleExtension.Isomorphic X X') ∧
      (∀ Y, ∃ X, IsLocalizedExtension k B S N X Y) := by
  constructor
  · intro h
    constructor
    · intro X X' Y hX hX'
      exact Quotient.exact (h.injective ((localizationMap_mk k B S N X Y hX).trans
        (localizationMap_mk k B S N X' Y hX').symm))
    · intro Y
      obtain ⟨x, hx⟩ := h.surjective ⟦Y⟧
      obtain ⟨X, rfl⟩ := Quotient.exists_rep x
      obtain ⟨Z, hZ⟩ := exists_localizedExtension k B S N X
      have hZY : (⟦Z⟧ : SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses
          (algebraExtensionProblem k (Localization S) (LocalizedModule S N))) = ⟦Y⟧ :=
        (localizationMap_mk k B S N X Z hZ).symm.trans hx
      obtain ⟨e⟩ := Quotient.exact hZY
      exact ⟨X, isLocalizedExtension_of_iso_right k B S N X Z Y hZ e⟩
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro x x' hxx'
      obtain ⟨X, rfl⟩ := Quotient.exists_rep x
      obtain ⟨X', rfl⟩ := Quotient.exists_rep x'
      obtain ⟨Y, hY⟩ := exists_localizedExtension k B S N X
      obtain ⟨Y', hY'⟩ := exists_localizedExtension k B S N X'
      have hYY' : (⟦Y⟧ : SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses
          (algebraExtensionProblem k (Localization S) (LocalizedModule S N))) = ⟦Y'⟧ :=
        (localizationMap_mk k B S N X Y hY).symm.trans
          (hxx'.trans (localizationMap_mk k B S N X' Y' hY'))
      obtain ⟨e⟩ := Quotient.exact hYY'
      exact Quotient.sound (hinj X X' Y'
        (isLocalizedExtension_of_iso_right k B S N X Y Y' hY e) hY')
    · intro y
      obtain ⟨Y, rfl⟩ := Quotient.exists_rep y
      obtain ⟨X, hX⟩ := hsurj Y
      exact ⟨⟦X⟧, localizationMap_mk k B S N X Y hX⟩

/-- A bijective `Deformation.Examples.localizationMap` is an equivalence sending each class
to the class of its localization. -/
private theorem exists_equiv_of_bijective_localizationMap
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (h : Function.Bijective (localizationMap k B S N)) :
    ∃ e : SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB, uN,
        max uk (max uB uN)} (algebraExtensionProblem k B N) ≃
      SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB,
        max uB uN, max uk (max uB uN)}
        (algebraExtensionProblem k (Localization S) (LocalizedModule S N)),
      ∀ X Y, IsLocalizedExtension k B S N X Y → e ⟦X⟧ = ⟦Y⟧ :=
  ⟨Equiv.ofBijective (localizationMap k B S N) h,
    fun X Y hY ↦ localizationMap_mk k B S N X Y hY⟩

/-- **Stacks 0DZ8.** If a multiplicative subset `S` of a finite type algebra `B` over a field
`k` is disjoint from every prime in the non-smooth locus of `B`, then localization at `S` is a
bijection from the isomorphism classes of square-zero extensions of `B` by `N` to those of
square-zero extensions of `S⁻¹B` by `S⁻¹N`.

The companion lemma
`Deformation.Examples.squareZeroAlgebraExtensionClassesLocalizationEquiv_apply` identifies the
forward map with localization. -/
@[stacks 0DZ8 "localization equivalence"]
noncomputable def squareZeroAlgebraExtensionClassesLocalizationEquiv
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (S : Submonoid B)
    (hS : ∀ q : PrimeSpectrum B,
      ¬ Algebra.IsSmoothAt k q.asIdeal →
        Disjoint (S : Set B) (q.asIdeal : Set B))
    (N : Type uN) [AddCommGroup N] [Module B N] :
    SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB, uN,
        max uk (max uB uN)} (algebraExtensionProblem k B N) ≃
      SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB,
        max uB uN, max uk (max uB uN)}
        (algebraExtensionProblem k (Localization S) (LocalizedModule S N)) :=
  Classical.choose (show ∃ e :
    SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB, uN,
        max uk (max uB uN)} (algebraExtensionProblem k B N) ≃
      SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB,
        max uB uN, max uk (max uB uN)}
        (algebraExtensionProblem k (Localization S) (LocalizedModule S N)),
      ∀ X Y, IsLocalizedExtension k B S N X Y → e ⟦X⟧ = ⟦Y⟧ from by
    apply exists_equiv_of_bijective_localizationMap k B S N
    let : Algebra.FinitePresentation k B :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
    let P₀ := Algebra.Presentation.ofFinitePresentation k B
    let P := P₀.reindex (Equiv.ulift.{uB}) (Equiv.refl _)
    let : Module.Finite B P.toExtension.Cotangent :=
      Algebra.Extension.Cotangent.finite P.fg_ker
    let : Module.Finite B P.toExtension.CotangentSpace :=
      Module.Finite.of_basis P.toGenerators.cotangentSpaceBasis
    let : Module.FinitePresentation B P.toExtension.CotangentSpace :=
      Module.finitePresentation_of_projective B P.toExtension.CotangentSpace
    let : Algebra.FormallySmooth k P.toExtension.Ring :=
      inferInstanceAs (Algebra.FormallySmooth k (MvPolynomial _ k))
    have hcot := bijective_cotangentCokernelMap_of_disjoint_nonsmoothLocus P.toExtension S hS N
    rw [bijective_localizationMap_iff]
    refine ⟨fun X X' Y hX hX' ↦ isomorphic_of_common_localization k B S N P.toExtension
      hcot.injective X X' Y hX hX', fun Y ↦ exists_original_of_localizedExtension k B S N
        P.toExtension hcot.surjective Y⟩)

/-- **Stacks 0DZ8.** The forward map of
`Deformation.Examples.squareZeroAlgebraExtensionClassesLocalizationEquiv` is localization of an
extension at the inverse image of `S` in its middle ring. -/
@[stacks 0DZ8 "forward map is localization"]
theorem squareZeroAlgebraExtensionClassesLocalizationEquiv_apply
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (S : Submonoid B)
    (hS : ∀ q : PrimeSpectrum B,
      ¬ Algebra.IsSmoothAt k q.asIdeal →
        Disjoint (S : Set B) (q.asIdeal : Set B))
    (N : Type uN) [AddCommGroup N] [Module B N]
    (X : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)}) :
    ∃ Y : (algebraExtensionProblem k (Localization S)
        (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)},
      squareZeroAlgebraExtensionClassesLocalizationEquiv k B S hS N
          (Quotient.mk
            (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
              (algebraExtensionProblem k B N)) X) =
        Quotient.mk
          (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
            (algebraExtensionProblem k (Localization S)
              (LocalizedModule S N))) Y ∧
      IsLocalizedExtension k B S N X Y := by
  obtain ⟨Y, hY⟩ := exists_localizedExtension k B S N X
  refine ⟨Y, ?_, hY⟩
  unfold squareZeroAlgebraExtensionClassesLocalizationEquiv
  generalize_proofs h
  exact h.choose_spec X Y hY

end Deformation.Examples

end
