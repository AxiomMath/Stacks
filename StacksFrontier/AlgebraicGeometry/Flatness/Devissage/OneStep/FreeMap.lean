module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent.Affine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Flat.CompleteDevissageStep
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# A generically invertible free map in a one-step dévissage

Let `(Z, Y, i, π, G)` be a one-step dévissage of `F/X/S` over `s`, and let `ξ` be a point of the
fibre of the smooth morphism `g : Y ⟶ S` over `s`. There is a free `𝒪_Y`-module of positive
finite rank and a map from it to the direct image `π_* G` which becomes an isomorphism after
base change to the residue field of the image of `ξ` in `Y`. Conversely, for *any* map into
`π_* G` which is invertible over that residue field, the fibre over `s` of the support of the
cokernel has strictly smaller dimension than the fibre over `s` of the support of `F`.

## Main results

* `AlgebraicGeometry.exists_freeMap_isIso_residueField`: on an affine scheme a quasi-coherent
  module of finite type receives a map from a finite free module which becomes an isomorphism
  over the residue field at a given point. This is the construction of the map `α` of the
  induction step of [Stacks, Tag 0815], and the reason the statement is public.
* `AlgebraicGeometry.exists_freeMap_isIso_genericFiber`: the free map exists and has positive
  rank.
* `AlgebraicGeometry.dim_support_cokernel_fiber_lt`: the dimension drop for the cokernel of any
  such map.
* `AlgebraicGeometry.supp_tilde`: the support of the sheaf associated with a module is the
  support of the module.
* `AlgebraicGeometry.topologicalKrullDim_supp_eq_supportDim`: on an affine scheme the dimension
  of the support of a quasi-coherent module with finite global sections is the support dimension
  of those sections.
* `AlgebraicGeometry.isIso_pullback_map_tilde`: a map of modules whose base change to a field is
  bijective becomes an isomorphism of associated sheaves after pullback to the spectrum of that
  field. This is the criterion in which `AlgebraicGeometry.DevissageStage` records its
  generic-fibre condition, so it is the translation between that condition and the bijectivity
  that `Module.CompleteDevissage.fiber_bijective` asks for.

## Implementation notes

The free module is `SheafOfModules.free (ULift (Fin r))`, the form in which
`AlgebraicGeometry.DevissageStage` records it, rather than a coproduct indexed by `Fin r`; the
index type of a free sheaf of modules must live in the universe of the sheaf of rings.

The second result is stated for a map out of an arbitrary `𝒪_Y`-module: freeness of the source
plays no part in the argument, which only needs the target to be of finite type. It therefore
applies verbatim to the map produced by the first result.

Positivity of the rank and the dimension drop are both instances of the same elementary fact:
the support of a module of finite type is closed, so a point of an irreducible finite
dimensional space outside it witnesses that the support has strictly smaller dimension. For
positivity, the dimension of the fibre support of `F` is by definition the dimension of the
fibre of `g`, so no point of that fibre can be missing from the support of `π_* G`.

Dimensions of supports are compared on affine schemes through global sections, where the
support of a quasi-coherent module of finite type is the support of a finite module over the
ring of sections and its dimension is `Module.supportDim`. Along a finite morphism of affine
schemes, both the ring and the module of sections change by an integral extension, which leaves
`Module.supportDim` unchanged.

## References

* [Stacks Project, Tag 05HF](https://stacks.math.columbia.edu/tag/05HF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Order TopologicalSpace

universe u

namespace AlgebraicGeometry

open scoped TensorProduct

/-! ### Dimension of a proper closed subset of an irreducible space -/

/-- A closed subset properly contained in an irreducible set of finite dimension has strictly
smaller dimension: every chain of irreducible closed subsets of the smaller set extends by the
larger set itself. -/
private theorem topologicalKrullDim_lt_of_isClosed_ssubset {T : Type*} [TopologicalSpace T]
    {V C : Set T} (hV : IsClosed V) (hC : IsIrreducible C) (hVC : V ⊂ C)
    (hfin : topologicalKrullDim (↥C) ≠ ⊤) :
    topologicalKrullDim (↥V) < topologicalKrullDim (↥C) := by
  obtain ⟨c, hc⟩ := hC.nonempty
  have hCne : Nonempty (IrreducibleCloseds (↥C)) :=
    ⟨⟨closure {(⟨c, hc⟩ : ↥C)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim (↥C) = (n : WithBot ℕ∞) := by
    have hbot : topologicalKrullDim (↥C) ≠ ⊥ := by
      rw [topologicalKrullDim, Ne, Order.krullDim_eq_bot_iff]
      simp
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
    have hmt : m ≠ ⊤ := fun h => hfin (by rw [← hm, h]; rfl)
    obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hmt
    exact ⟨k, hm.symm⟩
  rcases isEmpty_or_nonempty (IrreducibleCloseds (↥V)) with hE | hne
  · have hbot : topologicalKrullDim (↥V) = ⊥ := by
      rw [topologicalKrullDim, Order.krullDim_eq_bot_iff]
      exact hE
    rw [hbot, hn]
    exact bot_lt_iff_ne_bot.mpr (by simp)
  · obtain ⟨q⟩ := hne
    have h1 : 1 ≤ n := by
      have hq := succ_le_topologicalKrullDim_of_ssubset hV hC hVC (RelSeries.singleton _ q)
      rw [hn] at hq
      simp only [RelSeries.singleton_length, Nat.zero_add] at hq
      exact_mod_cast hq
    rw [hn]
    refine lt_of_le_of_lt (topologicalKrullDim_le_pred_of_ssubset hV hC hVC (le_of_eq hn)) ?_
    have hlt : (n - 1 : ℕ) < n := by omega
    exact_mod_cast hlt

/-- A proper closed subset of an irreducible space of finite dimension has strictly smaller
dimension. -/
private theorem topologicalKrullDim_lt_of_isClosed_ne_univ {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {V : Set T} (hV : IsClosed V) (hne : V ≠ Set.univ)
    (hfin : topologicalKrullDim T ≠ ⊤) :
    topologicalKrullDim (↥V) < topologicalKrullDim T := by
  have huniv : topologicalKrullDim (↥(Set.univ : Set T)) = topologicalKrullDim T :=
    (Homeomorph.Set.univ T).isHomeomorph.topologicalKrullDim_eq
  rw [← huniv] at hfin ⊢
  exact topologicalKrullDim_lt_of_isClosed_ssubset hV (IrreducibleSpace.isIrreducible_univ T)
    (lt_of_le_of_ne (Set.subset_univ V) hne) hfin

/-- A point of an irreducible space of finite dimension that is outside the support of a module
of finite type witnesses that the support has strictly smaller dimension than the space. -/
public theorem topologicalKrullDim_supp_lt_of_notMem {X : Scheme.{u}} [IrreducibleSpace X]
    (hfin : topologicalKrullDim X ≠ ⊤) (M : X.Modules) [M.IsFiniteType] {x : X}
    (hx : x ∉ SheafOfModules.supp M) :
    topologicalKrullDim (SheafOfModules.supp M) < topologicalKrullDim X :=
  topologicalKrullDim_lt_of_isClosed_ne_univ (SheafOfModules.isClosed_supp M)
    (fun h => hx (h ▸ Set.mem_univ x)) hfin

/-- The fibres of a morphism between affine schemes which is locally of finite type have finite
dimension. -/
private theorem topologicalKrullDim_fiber_ne_top {Y S : Scheme.{u}} (g : Y ⟶ S) [IsAffine Y]
    [IsAffine S] [LocallyOfFiniteType g] (s : S) :
    topologicalKrullDim (g.fiber s) ≠ ⊤ := by
  have : IsAffineHom g := isAffineHom_of_isAffine g
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_fiber_le g
  refine ne_top_of_le_ne_top ?_ (hn s)
  change ((n : ℕ∞) : WithBot ℕ∞) ≠ ((⊤ : ℕ∞) : WithBot ℕ∞)
  exact fun he => ENat.natCast_ne_top n (WithBot.coe_eq_coe.mp he)

/-! ### Elementary properties of the support -/

/-- A zero sheaf of modules has empty support. -/
private theorem supp_eq_empty_of_isZero {Y : Scheme.{u}} {M : Y.Modules} (hM : IsZero M) :
    SheafOfModules.supp M = ∅ := by
  ext y
  refine ⟨?_, by simp⟩
  rintro ⟨a, ha⟩
  let T : Y.Modules ⥤ Ab.{u} :=
    Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y
  have hid := (IsZero.iff_id_eq_zero (T.obj M)).mp (Functor.map_isZero T hM)
  exact ha (congrArg (fun k : T.obj M ⟶ T.obj M => k a) hid)

/-- A point lies outside the support of a module of finite type as soon as the pullback of the
module to the spectrum of the residue field at that point vanishes. -/
private theorem notMem_supp_of_isZero_pullback {Y : Scheme.{u}} (M : Y.Modules) [M.IsFiniteType]
    (y : Y) (h : IsZero ((Scheme.Modules.pullback (Y.fromSpecResidueField y)).obj M)) :
    y ∉ SheafOfModules.supp M := by
  intro hy
  obtain ⟨t⟩ : Nonempty (Spec (Y.residueField y)) :=
    ⟨IsLocalRing.closedPoint (Y.residueField y)⟩
  have hmem : t ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (Y.fromSpecResidueField y)).obj M) := by
    rw [Stacks.Modules.supp_pullback]
    change Y.fromSpecResidueField y t ∈ SheafOfModules.supp M
    rw [Scheme.fromSpecResidueField_apply]
    exact hy
  rw [supp_eq_empty_of_isZero h] at hmem
  exact hmem

/-- A functor inverts a composite whenever it inverts both factors. -/
private theorem isIso_map_comp {C D : Type*} [Category C] [Category D] (T : C ⥤ D) {A B E : C}
    (u : A ⟶ B) (v : B ⟶ E) (hu : IsIso (T.map u)) (hv : IsIso (T.map v)) :
    IsIso (T.map (u ≫ v)) := by
  rw [T.map_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hu hv

/-- Pullback of modules along a morphism of schemes preserves cokernels, being a left adjoint. -/
private noncomputable def pullbackCokernelIso {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules}
    (α : M ⟶ N) :
    (Scheme.Modules.pullback f).obj (cokernel α) ≅
      cokernel ((Scheme.Modules.pullback f).map α) :=
  haveI : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  PreservesCokernel.iso (Scheme.Modules.pullback f) α

/-- If a map of `𝒪_Y`-modules becomes an isomorphism over the residue field of a point `y`, then
`y` lies outside the support of its cokernel. -/
theorem notMem_supp_cokernel_of_isIso {Y : Scheme.{u}} {M N : Y.Modules} (α : M ⟶ N)
    [(cokernel α).IsFiniteType] (y : Y)
    (hα : IsIso ((Scheme.Modules.pullback (Y.fromSpecResidueField y)).map α)) :
    y ∉ SheafOfModules.supp (cokernel α) := by
  have := hα
  refine notMem_supp_of_isZero_pullback (cokernel α) y ?_
  exact IsZero.of_iso
    (isZero_cokernel_of_epi ((Scheme.Modules.pullback (Y.fromSpecResidueField y)).map α))
    (pullbackCokernelIso (Y.fromSpecResidueField y) α)

/-! ### Dimension of the support on an affine scheme -/

/-- Along an integral extension of rings, a module finite over both has the same support
dimension over each. -/
theorem supportDim_eq_of_isIntegral (A B M : Type*) [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra A B] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite A M] [Module.Finite B M] [Algebra.IsIntegral A B] :
    Module.supportDim A M = Module.supportDim B M := by
  set J := Module.annihilator B M with hJ
  have hIJ : Module.annihilator A M = J.comap (algebraMap A B) := by
    ext a
    simp [hJ, Module.mem_annihilator]
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator, hIJ]
  have : FaithfulSMul (A ⧸ J.comap (algebraMap A B)) (B ⧸ J) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    rintro ⟨a⟩ ⟨b⟩ h
    refine Quotient.eq.mpr ((J.comap (algebraMap A B)).quotientRel_def.mpr ?_)
    have hab : algebraMap A B a - algebraMap A B b ∈ J :=
      J.quotientRel_def.mp (Quotient.eq.mp h)
    change algebraMap A B (a - b) ∈ J
    rw [map_sub]
    exact hab
  exact Algebra.IsIntegral.ringKrullDim_eq (A ⧸ J.comap (algebraMap A B)) (B ⧸ J)

/-- The support of a finite module, as a subspace of the prime spectrum, has the module's
support dimension: it is homeomorphic to the spectrum of the quotient by the annihilator. -/
theorem topologicalKrullDim_support (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] :
    topologicalKrullDim (Module.support R M) = Module.supportDim R M := by
  set I := Module.annihilator R M with hI
  set f : R →+* R ⧸ I := Ideal.Quotient.mk I with hf
  have hclosed := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (R ⧸ I) f
    Ideal.Quotient.mk_surjective
  have hrange : Set.range (PrimeSpectrum.comap f) = Module.support R M := by
    rw [Module.support_eq_zeroLocus,
      range_comap_of_surjective (R ⧸ I) f Ideal.Quotient.mk_surjective]
    simp [hf, hI]
  calc
    topologicalKrullDim (Module.support R M)
        = topologicalKrullDim (Set.range (PrimeSpectrum.comap f)) :=
      congrArg (fun Z : Set (PrimeSpectrum R) => topologicalKrullDim Z) hrange.symm
    _ = topologicalKrullDim (PrimeSpectrum (R ⧸ I)) :=
      (hclosed.toHomeomorph.isHomeomorph.topologicalKrullDim_eq).symm
    _ = ringKrullDim (R ⧸ I) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ = Module.supportDim R M := (Module.supportDim_eq_ringKrullDim_quotient_annihilator R M).symm

/-- The support of the sheaf associated with a module over a commutative ring is the support of
the module. -/
theorem supp_tilde (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    SheafOfModules.supp (tilde M) = (Module.support R M : Set (Spec R)) := by
  ext p
  let x : PrimeSpectrum.Top R := p
  have : x.asIdeal.IsPrime := x.isPrime
  change (∃ a : (tilde M).presheaf.stalk x, a ≠ 0) ↔
    (⟨x.asIdeal, x.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M
  rw [Module.mem_support_iff]
  have e : LocalizedModule x.asIdeal.primeCompl M ≃ₗ[R] (tilde M).presheaf.stalk x :=
    IsLocalizedModule.linearEquiv x.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M) (tilde.toStalk M x).hom
  exact ⟨fun ⟨a, ha⟩ ↦ (Equiv.nontrivial_congr e.toEquiv).mpr (nontrivial_of_ne a 0 ha),
    fun hn ↦ have := (Equiv.nontrivial_congr e.toEquiv).mp hn; exists_ne 0⟩

/-- On an affine scheme, the support of a quasi-coherent module whose global sections are finite
has the support dimension of those global sections. -/
theorem topologicalKrullDim_supp_eq_supportDim (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R (moduleSpecΓFunctor.obj M)] :
    topologicalKrullDim (SheafOfModules.supp M) =
      Module.supportDim R (moduleSpecΓFunctor.obj M) := by
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  rw [← SheafOfModules.supp_eq_of_iso (asIso M.fromTildeΓ), supp_tilde]
  exact topologicalKrullDim_support R (moduleSpecΓFunctor.obj M)

/-! ### Dimension of the support of a direct image -/

/-- The support dimension is unchanged by direct image along an isomorphism of schemes. -/
private theorem topologicalKrullDim_supp_pushforward_of_isIso {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : X.Modules) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pushforward e.hom).obj M)) =
      topologicalKrullDim (SheafOfModules.supp M) := by
  set N := (Scheme.Modules.pushforward e.hom).obj M with hN
  have hs (x : X) : e.hom x ∈ SheafOfModules.supp N ↔ x ∈ SheafOfModules.supp M := by
    have hiso : IsIso (TopCat.Presheaf.stalkPushforward Ab.{u} e.hom.base M.presheaf x) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        Ab.{u} e.hom.homeomorph.isInducing M.presheaf x
    have ht := ConcreteCategory.bijective_of_isIso
      (TopCat.Presheaf.stalkPushforward Ab.{u} e.hom.base M.presheaf x)
    change (∃ a : N.presheaf.stalk (e.hom x), a ≠ 0) ↔ ∃ a : M.presheaf.stalk x, a ≠ 0
    rw [← nontrivial_iff_exists_ne 0, ← nontrivial_iff_exists_ne 0]
    exact (Equiv.ofBijective _ ht).nontrivial_congr
  have ehomeo : SheafOfModules.supp M ≃ₜ SheafOfModules.supp N :=
    { toEquiv :=
        { toFun := fun x => ⟨e.hom x.1, (hs x.1).mpr x.2⟩
          invFun := fun y => ⟨e.inv y.1, (hs (e.inv y.1)).mp (by simp)⟩
          left_inv := fun x => Subtype.ext (by simp)
          right_inv := fun y => Subtype.ext (by simp) }
      continuous_toFun := (e.hom.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.inv.continuous.comp continuous_subtype_val).subtype_mk _ }
  exact ehomeo.isHomeomorph.topologicalKrullDim_eq.symm

/-- The support dimension is unchanged by direct image along a finite morphism of spectra: on
global sections the direct image is restriction of scalars along a finite, hence integral, ring
map. -/
private theorem topologicalKrullDim_supp_pushforward_specMap (R S : CommRingCat.{u}) (f : R ⟶ S)
    (M : (Spec S).Modules) [IsFinite (Spec.map f)] [M.IsQuasicoherent] [M.IsFiniteType] :
    topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pushforward (Spec.map f)).obj M)) =
      topologicalKrullDim (SheafOfModules.supp M) := by
  have hfin : f.hom.Finite := (IsFinite.SpecMap_iff f).mp inferInstance
  let : Algebra R S := f.hom.toAlgebra
  have : Module.Finite R S := hfin
  set N := moduleSpecΓFunctor.obj M with hNdef
  have : Module.Finite S N := Stacks.AlgebraicGeometry.PushforwardCoherent.finite_moduleSpecΓ M
  let : Module R N := Module.compHom N f.hom
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite R N := Module.Finite.trans S N
  set P := (Scheme.Modules.pushforward (Spec.map f)).obj M with hP
  have : P.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_specMap f M
  have : P.IsFiniteType :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_specMap f hfin M
  have : Module.Finite R (moduleSpecΓFunctor.obj P) :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.finite_moduleSpecΓ P
  rw [topologicalKrullDim_supp_eq_supportDim R P, topologicalKrullDim_supp_eq_supportDim S M]
  calc
    Module.supportDim R (moduleSpecΓFunctor.obj P)
        = Module.supportDim R N :=
      Module.supportDim_eq_of_equiv ((pushforwardΓIso R S f).app M).toLinearEquiv
    _ = Module.supportDim S N := supportDim_eq_of_isIntegral R S N

/-- The support dimension is unchanged by direct image along a finite morphism of affine
schemes. -/
private theorem topologicalKrullDim_supp_pushforward_of_isFinite {X Y : Scheme.{u}} [IsAffine X]
    [IsAffine Y] (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsQuasicoherent]
    [M.IsFiniteType] :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pushforward f).obj M)) =
      topologicalKrullDim (SheafOfModules.supp M) := by
  set P := (Scheme.Modules.pushforward X.isoSpec.hom).obj M with hP
  have : P.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isIso X.isoSpec M
  have : P.IsFiniteType :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isIso X.isoSpec M
  have : IsFinite (Spec.map f.appTop) := (IsFinite.SpecMap_iff f.appTop).mpr f.finite_appTop
  have e : (Scheme.Modules.pushforward Y.isoSpec.hom).obj
      ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward (Spec.map f.appTop)).obj P :=
    (Scheme.Modules.pushforwardComp f Y.isoSpec.hom).app M ≪≫
      (Scheme.Modules.pushforwardCongr (Scheme.isoSpec_hom_naturality f).symm).app M ≪≫
      ((Scheme.Modules.pushforwardComp X.isoSpec.hom (Spec.map f.appTop)).app M).symm
  calc
    _ = topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pushforward Y.isoSpec.hom).obj
          ((Scheme.Modules.pushforward f).obj M))) :=
      (topologicalKrullDim_supp_pushforward_of_isIso Y.isoSpec _).symm
    _ = topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pushforward (Spec.map f.appTop)).obj P)) := by
      rw [SheafOfModules.supp_eq_of_iso e]
    _ = topologicalKrullDim (SheafOfModules.supp P) :=
      topologicalKrullDim_supp_pushforward_specMap _ _ _ P
    _ = _ := topologicalKrullDim_supp_pushforward_of_isIso X.isoSpec M

/-- The fibre support dimension of a finite direct image is that of the base change of the module
to any pullback of the composite `i ≫ f` along the residue field map. -/
private theorem topologicalKrullDim_supp_pullback_fiberι_pushforward {X S Z W : Scheme.{u}}
    [IsAffine X] [IsAffine S] [IsAffine Z] [IsAffine W] (f : X ⟶ S) (i : Z ⟶ X) [IsFinite i]
    (G : Z.Modules) [G.IsQuasicoherent] [G.IsFiniteType] (s : S) (a : W ⟶ Z)
    (b : W ⟶ Spec (S.residueField s)) (hW : IsPullback a b (i ≫ f) (S.fromSpecResidueField s)) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj
        ((Scheme.Modules.pushforward i).obj G))) =
      topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback a).obj G)) := by
  have hf : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (S.fromSpecResidueField s) :=
    IsPullback.of_hasPullback _ _
  have hi' : IsPullback a (hf.lift (a ≫ i) b (by simpa [Category.assoc] using hW.w)) i
      (f.fiberι s) := hW.of_bot' hf
  have : IsFinite (hf.lift (a ≫ i) b (by simpa [Category.assoc] using hW.w)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) hi' inferInstance
  have : IsAffineHom f := isAffineHom_of_isAffine f
  have : IsAffineHom i := isAffineHom_of_isAffine i
  have : IsAffine (f.fiber s) := isAffine_of_isAffineHom (f.fiberToSpecResidueField s)
  have : ((Scheme.Modules.pullback a).obj G).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ a.toLRSHom.toShHom G ‹G.IsQuasicoherent›
  have : ((Scheme.Modules.pullback a).obj G).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType a.toLRSHom.toShHom G
  have := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    hi' G
  have ei : (Scheme.Modules.pullback (f.fiberι s)).obj ((Scheme.Modules.pushforward i).obj G) ≅
      (Scheme.Modules.pushforward
          (hf.lift (a ≫ i) b (by simpa [Category.assoc] using hW.w))).obj
        ((Scheme.Modules.pullback a).obj G) :=
    asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hi'.w).app G)
  rw [SheafOfModules.supp_eq_of_iso ei]
  exact topologicalKrullDim_supp_pushforward_of_isFinite _ _

/-- For a module on a scheme finite over two affine schemes over a common affine base, the two
direct images have fibre supports of the same dimension: both fibres are base changes of the
fibre of the composite, and the comparison is affine base change followed by invariance of the
support dimension under a finite direct image. -/
private theorem topologicalKrullDim_supp_pullback_fiberι_eq {X S Y Z : Scheme.{u}} [IsAffine X]
    [IsAffine Y] [IsAffine Z] [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ X) (π : Z ⟶ Y)
    [IsFinite i] [IsFinite π] (hc : i ≫ f = π ≫ g) (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFiniteType] (s : S) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj
        ((Scheme.Modules.pushforward i).obj G))) =
      topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (g.fiberι s)).obj
        ((Scheme.Modules.pushforward π).obj G))) := by
  have hW : IsPullback ((i ≫ f).fiberι s) ((i ≫ f).fiberToSpecResidueField s) (i ≫ f)
      (S.fromSpecResidueField s) := IsPullback.of_hasPullback _ _
  have : IsAffineHom (i ≫ f) := by
    have : IsAffineHom i := isAffineHom_of_isAffine i
    have : IsAffineHom f := isAffineHom_of_isAffine f
    infer_instance
  have : IsAffine ((i ≫ f).fiber s) := isAffine_of_isAffineHom ((i ≫ f).fiberToSpecResidueField s)
  have hW' : IsPullback ((i ≫ f).fiberι s) ((i ≫ f).fiberToSpecResidueField s) (π ≫ g)
      (S.fromSpecResidueField s) := by
    rw [← hc]
    exact hW
  exact (topologicalKrullDim_supp_pullback_fiberι_pushforward f i G s _ _ hW).trans
    (topologicalKrullDim_supp_pullback_fiberι_pushforward g π G s _ _ hW').symm

/-! ### Construction of the free map -/

/-- The free sheaf of modules on the lift of a type to the universe of the structure sheaf is the
coproduct of copies of the unit indexed by the type itself. -/
private noncomputable def freeULiftIso {X : Scheme.{u}} (ι : Type) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} ι) ≅
      ∐ fun _ : ι => SheafOfModules.unit X.ringCatSheaf :=
  Sigma.whiskerEquiv (J := ULift.{u} ι) (K := ι)
    (f := fun _ => SheafOfModules.unit X.ringCatSheaf)
    (g := fun _ => SheafOfModules.unit X.ringCatSheaf) Equiv.ulift fun _ => Iso.refl _

/-- The coproduct of `r` copies of the unit on an affine scheme is the sheaf associated with the
free module of rank `r`. -/
public noncomputable def freeTildeIso (R : CommRingCat.{u}) (r : ℕ) :
    (∐ fun _ : Fin r => SheafOfModules.unit (Spec R).ringCatSheaf) ≅
      tilde (ModuleCat.of R (Fin r → R)) :=
  let q : Fin r → ModuleCat.{u} R := fun _ => ModuleCat.of R R
  (Sigma.mapIso fun _ : Fin r => (tildeSelf (R := R)).symm) ≪≫
    (PreservesCoproduct.iso (tilde.functor R) q).symm ≪≫
    (tilde.functor R).mapIso ((biproduct.isoCoproduct q).symm ≪≫ ModuleCat.biproductIsoPi q)

/-- A map of modules whose base change to a field is bijective induces an isomorphism of the
associated sheaves after pullback to the spectrum of that field. -/
theorem isIso_pullback_map_tilde (R K : Type u) [CommRing R] [Field K] (f : R →+* K)
    (M N : ModuleCat.{u} R) (g : M ⟶ N)
    (hg : letI : Algebra R K := f.toAlgebra; Function.Bijective (g.hom.rTensor K)) :
    IsIso ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom f))).map
      ((tilde.functor (CommRingCat.of R)).map g)) := by
  let : Algebra R K := f.toAlgebra
  set f' : R →+* K := (CommRingCat.ofHom f).hom with hf'
  set η := pullbackTildeIso (CommRingCat.of R) (CommRingCat.of K) (CommRingCat.ofHom f') with hη
  have : IsIso ((ModuleCat.extendScalars f').map g) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (g.hom.baseChange K)
    rw [LinearMap.baseChange_eq_lTensor]
    exact (LinearMap.lTensor_bij_iff_rTensor_bij K g.hom).2 hg
  have hT : IsIso ((ModuleCat.extendScalars (CommRingCat.Hom.hom (CommRingCat.ofHom f')) ⋙
      tilde.functor (CommRingCat.of K)).map g) := by
    change IsIso ((tilde.functor (CommRingCat.of K)).map ((ModuleCat.extendScalars f').map g))
    infer_instance
  have hcomp : IsIso (((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom f'))).map
      ((tilde.functor (CommRingCat.of R)).map g)) ≫ η.hom.app N) := by
    change IsIso (((tilde.functor (CommRingCat.of R) ⋙
      Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom f'))).map g) ≫ η.hom.app N)
    rw [η.hom.naturality g]
    exact IsIso.comp_isIso' (by infer_instance) hT
  exact IsIso.of_isIso_comp_right
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom f'))).map
      ((tilde.functor (CommRingCat.of R)).map g)) (η.hom.app N)

/-- Pullback along a composite inverts whatever pullback along the second factor inverts. -/
private theorem isIso_pullback_map_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Z.Modules} (α : M ⟶ N) (hα : IsIso ((Scheme.Modules.pullback g).map α)) :
    IsIso ((Scheme.Modules.pullback (f ≫ g)).map α) := by
  have := hα
  exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp f g) α).mp
    (Functor.map_isIso (Scheme.Modules.pullback f) _)

/-- On the spectrum of a ring, a quasi-coherent module of finite type receives a map from a
finite free module which becomes an isomorphism over the residue field at a given point. -/
private theorem exists_freeMap_isIso_residueField_spec (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (p : Spec R) :
    ∃ (r : ℕ) (α : (∐ fun _ : Fin r => SheafOfModules.unit (Spec R).ringCatSheaf) ⟶ M),
      IsIso ((Scheme.Modules.pullback ((Spec R).fromSpecResidueField p)).map α) := by
  have : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.finite_moduleSpecΓ M
  have : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨r, α, hα⟩ := Module.freeMapAtResidueField R p.asIdeal (moduleSpecΓFunctor.obj M)
  refine ⟨r, (freeTildeIso R r).hom ≫ (tilde.functor R).map (ModuleCat.ofHom α) ≫
    M.fromTildeΓ, ?_⟩
  have : IsIso ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)))).map
      ((tilde.functor R).map (ModuleCat.ofHom α))) :=
    isIso_pullback_map_tilde R p.asIdeal.ResidueField
      (algebraMap R p.asIdeal.ResidueField) _ _ _ (by
        dsimp only
        have hm : @Algebra.toModule R p.asIdeal.ResidueField _ _
            (algebraMap R p.asIdeal.ResidueField).toAlgebra =
            (inferInstance : Module R p.asIdeal.ResidueField) :=
          Module.ext' _ _ fun b x => (Algebra.smul_def b x).symm
        rw [hm]
        exact hα)
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  refine isIso_pullback_map_comp _ _ _ ?_
  set T := Scheme.Modules.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))) with hT
  have hΓ : IsIso (T.map M.fromTildeΓ) := inferInstance
  have hα' : IsIso (T.map ((tilde.functor R).map (ModuleCat.ofHom α))) := ‹_›
  exact isIso_map_comp T _ _ (T.mapIso (freeTildeIso R r)).isIso_hom
    (isIso_map_comp T _ _ hα' hΓ)

/-- On an affine scheme, a quasi-coherent module of finite type receives a map from a finite free
module which becomes an isomorphism over the residue field at a given point. -/
theorem exists_freeMap_isIso_residueField {Y : Scheme.{u}} [IsAffine Y] (M : Y.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (y : Y) :
    ∃ (r : ℕ) (α : (∐ fun _ : Fin r => SheafOfModules.unit Y.ringCatSheaf) ⟶ M),
      IsIso ((Scheme.Modules.pullback (Y.fromSpecResidueField y)).map α) := by
  set e := Y.isoSpec with he
  set Q := Scheme.Modules.pullback e.inv with hQ
  set P := Scheme.Modules.pullback e.hom with hP
  have : (Q.obj M).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(Y, ⊤)).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback e.inv).app M) inferInstance
  have : (Q.obj M).IsFiniteType := SheafOfModules.pullback_isFiniteType e.inv.toLRSHom.toShHom M
  obtain ⟨r, a, ha⟩ := exists_freeMap_isIso_residueField_spec _ (Q.obj M) (e.hom y)
  have eu : P.obj (SheafOfModules.unit (Spec Γ(Y, ⊤)).ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback e.hom).app _).symm ≪≫
      Scheme.Modules.restrictUnitIso e.hom
  have ef : P.obj (∐ fun _ : Fin r => SheafOfModules.unit (Spec Γ(Y, ⊤)).ringCatSheaf) ≅
      ∐ fun _ : Fin r => SheafOfModules.unit Y.ringCatSheaf :=
    PreservesCoproduct.iso P (fun _ : Fin r => SheafOfModules.unit (Spec Γ(Y, ⊤)).ringCatSheaf) ≪≫
      Sigma.mapIso fun _ => eu
  have ec : P.obj (Q.obj M) ≅ M :=
    (Scheme.Modules.pullbackComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pullbackCongr e.hom_inv_id).app M ≪≫ (Scheme.Modules.pullbackId Y).app M
  refine ⟨r, ef.inv ≫ P.map a ≫ ec.hom, ?_⟩
  set T := Scheme.Modules.pullback (Y.fromSpecResidueField y) with hT
  have hPa : IsIso (T.map (P.map a)) :=
    (NatIso.isIso_map_iff
      (Scheme.Modules.pullbackComp (Y.fromSpecResidueField y) e.hom) a).mpr (by
        rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
        exact isIso_pullback_map_comp _ _ a ha)
  have hef : IsIso (T.map ef.inv) := inferInstance
  have hec : IsIso (T.map ec.hom) := inferInstance
  exact isIso_map_comp T _ _ hef (isIso_map_comp T _ _ hPa hec)

/-! ### The free map of a one-step dévissage -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S) [LocallyOfFiniteType f]
  [F.IsQuasicoherent] [F.IsFiniteType] (D : OneStepDevissage f F s) (ξ : D.g.fiber s)

/-- If a point of the fibre of `g` is outside the support of the base change of a module of finite
type on `Y`, then that support has strictly smaller dimension than the fibre. -/
private theorem topologicalKrullDim_supp_pullback_fiberι_lt (N : D.Y.Modules) [N.IsFiniteType]
    (hmiss : ξ ∉ SheafOfModules.supp ((Scheme.Modules.pullback (D.g.fiberι s)).obj N)) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (D.g.fiberι s)).obj N)) <
      topologicalKrullDim (D.g.fiber s) := by
  have : IsAffine S := D.affine_S
  have : IsAffine D.Y := D.affine_Y
  have : Smooth D.g := D.smooth
  have : GeometricallyIrreducible D.g := D.geometrically_irreducible
  have : IsAffineHom D.g := isAffineHom_of_isAffine D.g
  have : IsAffine (D.g.fiber s) := isAffine_of_isAffineHom (D.g.fiberToSpecResidueField s)
  have : ((Scheme.Modules.pullback (D.g.fiberι s)).obj N).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (D.g.fiberι s).toLRSHom.toShHom N
  exact topologicalKrullDim_supp_lt_of_notMem (topologicalKrullDim_fiber_ne_top D.g s) _ hmiss

/-- **Stacks 05HF**, first assertion. For a one-step dévissage, a free `𝒪_Y`-module of positive
finite rank maps to the direct image `π_* G` by a map that becomes an isomorphism over the
residue field of the image in `Y` of a point of the fibre of `g` over `s`. -/
@[stacks 05HF "existence of the generically invertible map"]
theorem exists_freeMap_isIso_genericFiber :
    ∃ (r : ℕ) (_ : 0 < r)
      (α : SheafOfModules.free (R := D.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
        (Scheme.Modules.pushforward D.π).obj D.G),
      IsIso ((Scheme.Modules.pullback
        (D.Y.fromSpecResidueField (D.g.fiberι s ξ))).map α) := by
  have : IsAffine X := D.affine_X
  have : IsAffine S := D.affine_S
  have : IsAffine D.Y := D.affine_Y
  have : IsAffine D.Z := D.affine_Z
  have : IsClosedImmersion D.i := D.closed_immersion
  have : IsFinite D.π := D.finite
  have : IsFinite D.i := inferInstance
  have : Smooth D.g := D.smooth
  have : GeometricallyIrreducible D.g := D.geometrically_irreducible
  have : D.G.IsQuasicoherent := D.quasi_coherent_G
  have : D.G.IsFiniteType := D.finite_type_G
  set N := (Scheme.Modules.pushforward D.π).obj D.G with hN
  have : N.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom D.π D.G
  have : N.IsFiniteType :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isAffine D.π
      D.π.finite_appTop D.G
  obtain ⟨r, α, hα⟩ := exists_freeMap_isIso_residueField N (D.g.fiberι s ξ)
  refine ⟨r, ?_, (freeULiftIso (X := D.Y) (Fin r)).hom ≫ α, ?_⟩
  · by_contra hr
    obtain rfl : r = 0 := Nat.eq_zero_of_not_pos hr
    have := hα
    have hsrc : IsZero (∐ fun _ : Fin 0 => SheafOfModules.unit D.Y.ringCatSheaf) :=
      (IsZero.iff_id_eq_zero _).mpr (Sigma.hom_ext _ _ fun i => Fin.elim0 i)
    have hy : D.g.fiberι s ξ ∉ SheafOfModules.supp N :=
      notMem_supp_of_isZero_pullback N _
        ((Functor.map_isZero (Scheme.Modules.pullback
          (D.Y.fromSpecResidueField (D.g.fiberι s ξ))) hsrc).of_iso
          (asIso ((Scheme.Modules.pullback
            (D.Y.fromSpecResidueField (D.g.fiberι s ξ))).map α)).symm)
    have hmiss : ξ ∉ SheafOfModules.supp ((Scheme.Modules.pullback (D.g.fiberι s)).obj N) := by
      rw [Stacks.Modules.supp_pullback]
      exact hy
    have hlt := topologicalKrullDim_supp_pullback_fiberι_lt f F s D ξ N hmiss
    rw [D.fiber_dimension s,
      SheafOfModules.supp_eq_of_iso ((Scheme.Modules.pullback (f.fiberι s)).mapIso D.module_iso),
      ← topologicalKrullDim_supp_pullback_fiberι_eq f D.g D.i D.π D.over_base D.G s] at hlt
    exact lt_irrefl _ hlt
  · exact isIso_map_comp _ _ _
      ((Scheme.Modules.pullback
        (D.Y.fromSpecResidueField (D.g.fiberι s ξ))).mapIso (freeULiftIso (Fin r))).isIso_hom hα

/-- **Stacks 05HF**, second assertion. If a map into the direct image `π_* G` of a one-step
dévissage becomes an isomorphism over the residue field of the image in `Y` of a point of the
fibre of `g` over `s`, then the fibre over `s` of the support of its cokernel has strictly
smaller dimension than the fibre over `s` of the support of `F`. -/
@[stacks 05HF "dimension of the cokernel support"]
theorem dim_support_cokernel_fiber_lt {P : D.Y.Modules}
    (α : P ⟶ (Scheme.Modules.pushforward D.π).obj D.G)
    (hα : IsIso ((Scheme.Modules.pullback
      (D.Y.fromSpecResidueField (D.g.fiberι s ξ))).map α)) :
    topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (D.g.fiberι s)).obj (cokernel α))) <
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) := by
  have : IsAffine S := D.affine_S
  have : IsAffine D.Y := D.affine_Y
  have : IsAffine D.Z := D.affine_Z
  have : IsFinite D.π := D.finite
  have : Smooth D.g := D.smooth
  have : D.G.IsQuasicoherent := D.quasi_coherent_G
  have : D.G.IsFiniteType := D.finite_type_G
  have : ((Scheme.Modules.pushforward D.π).obj D.G).IsFiniteType :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isAffine D.π
      D.π.finite_appTop D.G
  have hepi : Epi (cokernel.π α) := inferInstance
  have hcoker : (cokernel α).IsFiniteType :=
    @Stacks.SheafOfModules.isFiniteType_of_epi'.{u} _ _ _ _ _ _ _ _ _ (cokernel.π α)
      inferInstance hepi
  have hmiss : ξ ∉ SheafOfModules.supp
      ((Scheme.Modules.pullback (D.g.fiberι s)).obj (cokernel α)) := by
    rw [Stacks.Modules.supp_pullback]
    exact notMem_supp_cokernel_of_isIso α _ hα
  rw [← D.fiber_dimension s]
  exact topologicalKrullDim_supp_pullback_fiberι_lt f F s D ξ _ hmiss

end AlgebraicGeometry

end
