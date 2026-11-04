module

public import StacksFrontier.Algebra.Module.FinitePresentation.Transport
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout08KU
public import StacksFrontier.RingTheory.MilnorPatching.RelativeProperties

/-!
# Milnor patching over a cube of rings

The affine-local content of Stacks 08KV is [Stacks Project, Tag 07RW], which
`MilnorPatching.relativelyFlatModulesEquivalenceOverFibreProduct` states for the rings
`D = D' ⊗_{B'} B`, `C' = D' ⊗_{B'} A'` and `C = D' ⊗_{B'} A` *themselves*.  Over an affine chart
of an algebraic space these rings arrive instead as the rings of functions of three charts, which
are those tensor products only up to isomorphism.  This file states 07RW for such a *cube of
rings*: a fibre product square `B' = B ×_A A'` with `A' ⟶ A` surjective, a `B'`-algebra `D'`, and
three rings `D`, `C'`, `C` with maps making the three squares over `B'` pushouts and the two
squares over `C` commute.

## Main results

* `Stacks.Pushout.exists_situation_of_cube`: the relative Milnor patching situation of a cube,
  with the three ring isomorphisms of its base-change rings with `D`, `C'` and `C`, compatible
  with all the maps.
* `Stacks.Pushout.cube_counit_bijective`: the two components of the counit of 07RW, for a pair of
  modules over `D` and `C'` glued along an isomorphism of their base changes to `C` — the
  restrictions of the module of compatible pairs are the two given modules.
* `Stacks.Pushout.cube_flat`: the module of compatible pairs of two relatively flat modules is
  flat over `B'`.
* `Stacks.Pushout.cube_unit_bijective`: a `D'`-module flat over `B'` is the module of compatible
  pairs of its two base changes.
* `Stacks.Pushout.cube_finite`: the module of compatible pairs of two finite modules is finite
  over `D'` ([Stacks Project, Tag 08IH]).
* `Stacks.Pushout.cube_finitePresentation`: the module of compatible pairs of two relatively flat
  modules of finite presentation is of finite presentation over `D'` when `B' ⟶ D'` is of finite
  presentation ([Stacks Project, Tag 08KP]).

## References

* [Stacks Project, Tag 07RW](https://stacks.math.columbia.edu/tag/07RW)
* [Stacks Project, Tag 08IH](https://stacks.math.columbia.edu/tag/08IH)
* [Stacks Project, Tag 08KP](https://stacks.math.columbia.edu/tag/08KP)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace Stacks.Pushout

variable {B' B A' A D' D C' C : Type u} [CommRing B'] [CommRing B] [CommRing A'] [CommRing A]
  [CommRing D'] [CommRing D] [CommRing C'] [CommRing C]
  (bB : B' →+* B) (bA' : B' →+* A') (tB : B →+* A) (tA' : A' →+* A)
  (σ : B' →+* D') (σB : B →+* D) (σA' : A' →+* C') (σA : A →+* C)
  (dD : D' →+* D) (dC' : D' →+* C') (eD : D →+* C) (eC' : C' →+* C)

/-- **A cube of rings for Milnor patching.**  The bottom face is a fibre product
`B' = B ×_A A'` with `A' ⟶ A` surjective; the three faces through `B' ⟶ D'` are pushouts, so
that `D`, `C'` and `C` are the base changes of `D'` to `B`, `A'` and `A`; and the faces over `C`
commute. -/
structure IsMilnorCube : Prop where
  base : IsPullback (CommRingCat.ofHom bB) (CommRingCat.ofHom bA') (CommRingCat.ofHom tB)
    (CommRingCat.ofHom tA')
  surj : Function.Surjective tA'
  pushD : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom bB) (CommRingCat.ofHom dD)
    (CommRingCat.ofHom σB)
  pushC' : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom bA') (CommRingCat.ofHom dC')
    (CommRingCat.ofHom σA')
  pushC : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom (tB.comp bB))
    (CommRingCat.ofHom (eD.comp dD)) (CommRingCat.ofHom σA)
  top : eD.comp dD = eC'.comp dC'
  sideD : eD.comp σB = σA.comp tB
  sideC' : eC'.comp σA' = σA.comp tA'

variable {bB bA' tB tA' σ σB σA' σA dD dC' eD eC'}

/-- **The relative Milnor patching situation of a cube of rings**, with its three base-change
rings identified with `D`, `C'` and `C` compatibly with every map of the cube. -/
theorem exists_situation_of_cube
    (h : IsMilnorCube bB bA' tB tA' σ σB σA' σA dD dC' eD eC') :
    ∃ (I : Ideal A') (base : RingFibreProduct.Situation tB tA' I)
      (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := D') base)
      (eB : B' ≃+* base.fibreProduct) (kD : s.D ≃+* D) (kC' : s.C' ≃+* C') (kC : s.C ≃+* C),
      s.toD'.comp eB.toRingHom = σ ∧
        (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).comp
          eB.toRingHom = bB ∧
        (MilnorPatching.RelativeModuleFibreProductSituation.toA' (base := base)).comp
          eB.toRingHom = bA' ∧
        (∀ d, kD (s.toD d) = dD d) ∧ (∀ x, kD (s.BtoD x) = σB x) ∧
        (∀ d, kC' (s.toC' d) = dC' d) ∧ (∀ x, kC' (s.A'toC' x) = σA' x) ∧
        (∀ z, kC (s.DtoC z) = eD (kD z)) ∧ (∀ z, kC (s.C'toC z) = eC' (kC' z)) := by
  let base : RingFibreProduct.Situation tB tA' (RingHom.ker tA') := ⟨h.surj, rfl⟩
  have hcan := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit
    (CommRingCat.ofHom tB) (CommRingCat.ofHom tA'))
  let E := h.base.isoIsPullback _ _ hcan
  let eB : B' ≃+* base.fibreProduct := E.commRingCatIsoToRingEquiv
  let s : MilnorPatching.RelativeModuleFibreProductSituation (D' := D') base :=
    ⟨σ.comp eB.symm.toRingHom⟩
  have hD' : s.toD'.comp eB.toRingHom = σ :=
    RingHom.ext fun r ↦ congrArg σ (eB.symm_apply_apply r)
  have heB : (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).comp
      eB.toRingHom = bB :=
    congrArg CommRingCat.Hom.hom (h.base.isoIsPullback_hom_fst _ _ hcan)
  have heA' : (MilnorPatching.RelativeModuleFibreProductSituation.toA' (base := base)).comp
      eB.toRingHom = bA' :=
    congrArg CommRingCat.Hom.hom (h.base.isoIsPullback_hom_snd _ _ hcan)
  have heA : (MilnorPatching.RelativeModuleFibreProductSituation.toA (base := base)).comp
      eB.toRingHom = tB.comp bB := by
    rw [← heB]
    rfl
  obtain ⟨kD, hkD1, hkD2⟩ := exists_tensorEquiv_of_isPushout σ bB dD σB h.pushD eB s.toD'
    (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)) hD' heB
  obtain ⟨kC', hkC'1, hkC'2⟩ := exists_tensorEquiv_of_isPushout σ bA' dC' σA' h.pushC' eB s.toD'
    (MilnorPatching.RelativeModuleFibreProductSituation.toA' (base := base)) hD' heA'
  obtain ⟨kC, hkC1, hkC2⟩ := exists_tensorEquiv_of_isPushout σ (tB.comp bB) (eD.comp dD) σA
    h.pushC eB s.toD' (MilnorPatching.RelativeModuleFibreProductSituation.toA (base := base))
    hD' heA
  let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
  let : Algebra base.fibreProduct B :=
    (MilnorPatching.RelativeModuleFibreProductSituation.toB (base := base)).toAlgebra
  let : Algebra base.fibreProduct A' :=
    (MilnorPatching.RelativeModuleFibreProductSituation.toA' (base := base)).toAlgebra
  let : Algebra base.fibreProduct A :=
    (MilnorPatching.RelativeModuleFibreProductSituation.toA (base := base)).toAlgebra
  have htD : ∀ d, (s.toD d : s.D) = d ⊗ₜ[base.fibreProduct] (1 : B) := fun _ ↦ rfl
  have htC' : ∀ d, (s.toC' d : s.C') = d ⊗ₜ[base.fibreProduct] (1 : A') := fun _ ↦ rfl
  have hBD : ∀ x, (s.BtoD x : s.D) = (1 : D') ⊗ₜ[base.fibreProduct] x := fun _ ↦ rfl
  have hA'C' : ∀ x, (s.A'toC' x : s.C') = (1 : D') ⊗ₜ[base.fibreProduct] x := fun _ ↦ rfl
  have hAC : ∀ x, (s.AtoC x : s.C) = (1 : D') ⊗ₜ[base.fibreProduct] x := fun _ ↦ rfl
  have hDCt : ∀ d, s.DtoC (s.toD d) = d ⊗ₜ[base.fibreProduct] (1 : A) :=
    fun d ↦ tensorMap_includeLeft _ d
  have kDtoD : ∀ d, kD (s.toD d) = dD d := fun d ↦ (congrArg kD (htD d)).trans (hkD1 d)
  have kDBtoD : ∀ x, kD (s.BtoD x) = σB x := fun x ↦ (congrArg kD (hBD x)).trans (hkD2 x)
  have kC'toC' : ∀ d, kC' (s.toC' d) = dC' d := fun d ↦ (congrArg kC' (htC' d)).trans (hkC'1 d)
  have kC'A' : ∀ x, kC' (s.A'toC' x) = σA' x := fun x ↦ (congrArg kC' (hA'C' x)).trans (hkC'2 x)
  have kCD : ∀ d, kC (s.DtoC (s.toD d)) = eD (dD d) := fun d ↦
    (congrArg kC (hDCt d)).trans (hkC1 d)
  have kCA : ∀ x, kC (s.AtoC x) = σA x := fun x ↦ (congrArg kC (hAC x)).trans (hkC2 x)
  have hDtoC : ∀ z, kC (s.DtoC z) = eD (kD z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul d x =>
      have hmul : (d ⊗ₜ[base.fibreProduct] x : s.D) = s.toD d * s.BtoD x := by
        rw [htD, hBD, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have hright : s.DtoC (s.BtoD x) = s.AtoC (tB x) :=
        congrArg (fun k : B →+* s.C ↦ k x) s.DtoC_BtoD
      rw [hmul, map_mul, map_mul, map_mul, map_mul, hright, kCD, kCA, kDtoD, kDBtoD]
      exact congrArg (eD (dD d) * ·) (congrArg (fun k : B →+* C ↦ k x) h.sideD).symm
    | add z w hz hw => simp only [map_add, hz, hw]
  have hC'toC : ∀ z, kC (s.C'toC z) = eC' (kC' z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul d x =>
      have hmul : (d ⊗ₜ[base.fibreProduct] x : s.C') = s.toC' d * s.A'toC' x := by
        rw [htC', hA'C', Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have hleft : s.C'toC (s.toC' d) = s.DtoC (s.toD d) :=
        (congrArg (fun k : D' →+* s.C ↦ k d) s.relativeSquare_comm).symm
      have hright : s.C'toC (s.A'toC' x) = s.AtoC (tA' x) :=
        congrArg (fun k : A' →+* s.C ↦ k x) s.C'toC_A'toC'
      rw [hmul, map_mul, map_mul, map_mul, map_mul, hleft, hright, kCD, kCA, kC'toC', kC'A']
      exact congrArg₂ (· * ·) (congrArg (fun k : D' →+* C ↦ k d) h.top)
        (congrArg (fun k : A' →+* C ↦ k x) h.sideC').symm
    | add z w hz hw => simp only [map_add, hz, hw]
  exact ⟨_, base, s, eB, kD, kC', kC, hD', heB, heA', kDtoD, kDBtoD, kC'toC', kC'A', hDtoC,
    hC'toC⟩

/-! ### Modules over a cube of rings -/

/-- **Finiteness transports along a bijection that is additive and semilinear over a ring
isomorphism.** -/
theorem finite_of_equiv_ringEquiv {R S M N : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module S N] (k : R ≃+* S) (e : M ≃ N)
    (hadd : ∀ x y : M, e (x + y) = e x + e y) (hsmul : ∀ (r : R) (x : M), e (r • x) = k r • e x)
    [Module.Finite S N] : Module.Finite R M :=
  Module.Finite.of_surjective (σ := k.symm.toRingHom)
    { toFun := e.symm
      map_add' := equivSymm_add e hadd
      map_smul' := fun r y => equivSymm_smul e (z := k.symm r) (w := r)
        (fun x => (hsmul _ x).trans (congrArg (· • e x) (k.apply_symm_apply r))) y }
    e.symm.surjective

/-- Finite presentation transports along a bijection that is additive and semilinear over a ring
isomorphism. -/
private theorem finitePresentation_of_equiv_ringEquiv {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (k : R ≃+* S) (e : M ≃ N)
    (hadd : ∀ x y : M, e (x + y) = e x + e y) (hsmul : ∀ (r : R) (x : M), e (r • x) = k r • e x)
    [Module.FinitePresentation S N] : Module.FinitePresentation R M :=
  finitePresentation_of_ringEquiv S R k.symm N M
    { toFun := e.symm, invFun := e, left_inv := e.right_inv, right_inv := e.left_inv,
      map_add' := equivSymm_add e hadd }
    (fun r y => equivSymm_smul e (z := k.symm r) (w := r)
      (fun x => (hsmul _ x).trans (congrArg (· • e x) (k.apply_symm_apply r))) y)
    inferInstance

/-- Flatness over `R` of a module over `T` transports to the restriction along `f : R ⟶ S` of a
module `M` over `S`, given a bijection `M ≃ N` that is semilinear over `k : S ≃+* T`. -/
private theorem flat_restrictScalars_of_equiv_ringEquiv {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] (f : R →+* S) (g : R →+* T) (k : S ≃+* T) (hk : ∀ b, k (f b) = g b)
    {M : ModuleCat.{u} S} {N : ModuleCat.{u} T} (e : M ≃ N)
    (hadd : ∀ x y : M, e (x + y) = e x + e y) (hsmul : ∀ (z : S) (x : M), e (z • x) = k z • e x)
    (hN : @Module.Flat R N _ _ (Module.compHom N g)) :
    Module.Flat R ((ModuleCat.restrictScalars f).obj M) :=
  flat_of_equiv_semilinear f g e hadd
    (fun b n => (hsmul (f b) n).trans (congrArg (fun r => r • e n) (hk b))) hN

/-- Precomposing with the inverse of a ring isomorphism undoes a precomposition. -/
private theorem comp_symm_eq_of_comp_eq {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S) (f : R →+* T) (g : S →+* T) (h : g.comp e.toRingHom = f) :
    f.comp e.symm.toRingHom = g :=
  RingHom.ext fun x => by
    rw [← h]
    exact congrArg g (e.apply_symm_apply x)

section Modules

variable (h : IsMilnorCube bB bA' tB tA' σ σB σA' σA dD dC' eD eC')
  (Gm : ModuleCat.{u} D) (Fm : ModuleCat.{u} C')
  (γ : (ModuleCat.extendScalars eD).obj Gm ≅ (ModuleCat.extendScalars eC').obj Fm)
  {P : Type u} [AddCommGroup P] [Module D' P] (π₁ : P → Gm) (π₂ : P → Fm)
  (hπ₁add : ∀ p q, π₁ (p + q) = π₁ p + π₁ q) (hπ₁smul : ∀ (d : D') p, π₁ (d • p) = dD d • π₁ p)
  (hπ₂add : ∀ p q, π₂ (p + q) = π₂ p + π₂ q) (hπ₂smul : ∀ (d : D') p, π₂ (d • p) = dC' d • π₂ p)
  (hπ : ∀ p, γ.hom ((1 : C) ⊗ₜ[D,eD] π₁ p) = (1 : C) ⊗ₜ[C',eC'] π₂ p)
  (hinj : ∀ p q, π₁ p = π₁ q → π₂ p = π₂ q → p = q)
  (hsurj : ∀ (x : Gm) (y : Fm), γ.hom ((1 : C) ⊗ₜ[D,eD] x) = (1 : C) ⊗ₜ[C',eC'] y →
    ∃ p, π₁ p = x ∧ π₂ p = y)

include h hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj in
/-- **The module of compatible pairs over a cube, as the compatible pairs of its Milnor patching
situation.**  The module `P` of pairs of an element of `Gm` and an element of `Fm` compatible
under `γ` is, `D'`-linearly, the module of compatible pairs of an object of the categorical
pullback of the situation of `Stacks.Pushout.exists_situation_of_cube`, whose two components are
`Gm` and `Fm` read over the base-change rings. -/
theorem exists_cubeCompatiblePairs :
    ∃ (I : Ideal A') (base : RingFibreProduct.Situation tB tA' I)
      (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := D') base)
      (eB : B' ≃+* base.fibreProduct) (kD : s.D ≃+* D) (kC' : s.C' ≃+* C')
      (Xc : MilnorPatching.RelativeModuleFibreProductSituation.CompatibleModules.{u, u, u, u, u} s)
      (eDx : Xc.fst ≃ Gm) (eAx : Xc.snd ≃ Fm)
      (E : P ≃ₗ[D'] MilnorPatching.compatiblePairsModule.{u} s.toD s.toC' s.DtoC s.C'toC
        s.relativeSquare_comm Xc),
      s.toD'.comp eB.toRingHom = σ ∧
        (∀ d, kD (s.toD d) = dD d) ∧ (∀ x, kD (s.BtoD x) = σB x) ∧
        (∀ d, kC' (s.toC' d) = dC' d) ∧ (∀ x, kC' (s.A'toC' x) = σA' x) ∧
        (∀ n n' : Xc.fst, eDx (n + n') = eDx n + eDx n') ∧
        (∀ (z : s.D) (n : Xc.fst), eDx (z • n) = kD z • eDx n) ∧
        (∀ m m' : Xc.snd, eAx (m + m') = eAx m + eAx m') ∧
        (∀ (z : s.C') (m : Xc.snd), eAx (z • m) = kC' z • eAx m) ∧
        (∀ p, eDx (E p).1.1 = π₁ p) ∧ (∀ p, eAx (E p).1.2 = π₂ p) := by
  obtain ⟨I, base, s, eB, kD, kC', kC, hD', -, -, hkD1, hkD2, hkC'1, hkC'2, hDC, hC'C⟩ :=
    exists_situation_of_cube h
  obtain ⟨Xc, eDx, eAx, hDadd, hDsmul, hAadd, hAsmul, hiff⟩ :=
    Stacks.ModuleCat.exists_categoricalPullback_of_ringEquivSquare kD kC' kC s.DtoC s.C'toC eD eC'
      hDC hC'C Gm Fm γ
  have hmem : ∀ p : P, Xc.iso.hom ((1 : s.C) ⊗ₜ[s.D,s.DtoC] eDx.symm (π₁ p)) =
      (1 : s.C) ⊗ₜ[s.C',s.C'toC] eAx.symm (π₂ p) := fun p => (hiff _ _).2 (by
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hπ p)
  let toFun : P → MilnorPatching.compatiblePairsModule.{u} s.toD s.toC' s.DtoC s.C'toC
      s.relativeSquare_comm Xc := fun p => ⟨(eDx.symm (π₁ p), eAx.symm (π₂ p)), hmem p⟩
  have hbij : Function.Bijective toFun := by
    refine ⟨fun p q hpq => hinj p q ?_ ?_, fun q => ?_⟩
    · have := congrArg (fun z => eDx z.1.1) hpq
      simpa [toFun] using this
    · have := congrArg (fun z => eAx z.1.2) hpq
      simpa [toFun] using this
    · obtain ⟨p, hp1, hp2⟩ := hsurj (eDx q.1.1) (eAx q.1.2) ((hiff _ _).1 q.2)
      refine ⟨p, Subtype.ext (Prod.ext ?_ ?_)⟩
      · change eDx.symm (π₁ p) = q.1.1
        rw [hp1, Equiv.symm_apply_apply]
      · change eAx.symm (π₂ p) = q.1.2
        rw [hp2, Equiv.symm_apply_apply]
  let E : P ≃ₗ[D'] MilnorPatching.compatiblePairsModule.{u} s.toD s.toC' s.DtoC s.C'toC
      s.relativeSquare_comm Xc := LinearEquiv.ofBijective
    { toFun := toFun
      map_add' := fun p q => Subtype.ext (Prod.ext
        ((congrArg eDx.symm (hπ₁add p q)).trans (equivSymm_add eDx hDadd _ _))
        ((congrArg eAx.symm (hπ₂add p q)).trans (equivSymm_add eAx hAadd _ _)))
      map_smul' := fun d p => Subtype.ext (Prod.ext
        ((congrArg eDx.symm ((hπ₁smul d p).trans
            (congrArg (· • π₁ p) (hkD1 d).symm))).trans
          (equivSymm_smul eDx (fun x => hDsmul (s.toD d) x) _))
        ((congrArg eAx.symm ((hπ₂smul d p).trans
            (congrArg (· • π₂ p) (hkC'1 d).symm))).trans
          (equivSymm_smul eAx (fun x => hAsmul (s.toC' d) x) _))) } hbij
  exact ⟨I, base, s, eB, kD, kC', Xc, eDx, eAx, E, hD', hkD1, hkD2, hkC'1, hkC'2, hDadd, hDsmul,
    hAadd, hAsmul, fun p => eDx.apply_symm_apply _, fun p => eAx.apply_symm_apply _⟩

include h hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj in
/-- **The first component of the counit of 07RW over a cube.**  A morphism `c` out of the base
change `D ⊗_{D'} P` (spelled `Q` through `aff`) into `Gm` which sends `1 ⊗ p` to the first
coordinate of `p` is bijective. -/
theorem cube_counit_fst_bijective (Q : ModuleCat.{u} D)
    (aff : (ModuleCat.extendScalars dD).obj (ModuleCat.of D' P) ≅ Q) (c : Q ⟶ Gm)
    (hval : ∀ p : P, c (aff.hom ((1 : D) ⊗ₜ[D',dD] p)) = π₁ p) :
    Function.Bijective c := by
  obtain ⟨I, base, s, eB, kD, kC', Xc, eDx, eAx, E, -, hkD1, -, -, -, hDadd, hDsmul, -, -, hE1,
    -⟩ := exists_cubeCompatiblePairs h Gm Fm γ π₁ π₂ hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj
  obtain ⟨F, e07, adj, form, -, hcounit⟩ := exists_relativeFlatAdjunction s
  obtain ⟨δ, -, hδ, -, hδval, -⟩ :=
    exists_counitChartHom s.toD s.toC' s.DtoC s.C'toC s.relativeSquare_comm e07 adj form
      hcounit Xc E
  exact Stacks.ModuleCat.bijective_of_extendScalarsTargetOut kD s.toD dD hkD1
    (ModuleCat.of D' P) Q aff Gm c Xc.fst eDx hDadd hDsmul δ hδ
    (fun p => ((congrArg eDx (hδval p)).trans (hE1 p)).trans (hval p).symm)

include h hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj in
/-- **The second component of the counit of 07RW over a cube.** -/
theorem cube_counit_snd_bijective (Q : ModuleCat.{u} C')
    (aff : (ModuleCat.extendScalars dC').obj (ModuleCat.of D' P) ≅ Q) (c : Q ⟶ Fm)
    (hval : ∀ p : P, c (aff.hom ((1 : C') ⊗ₜ[D',dC'] p)) = π₂ p) :
    Function.Bijective c := by
  obtain ⟨I, base, s, eB, kD, kC', Xc, eDx, eAx, E, -, -, -, hkC'1, -, -, -, hAadd, hAsmul, -,
    hE2⟩ := exists_cubeCompatiblePairs h Gm Fm γ π₁ π₂ hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj
  obtain ⟨F, e07, adj, form, -, hcounit⟩ := exists_relativeFlatAdjunction s
  obtain ⟨-, δ', -, hδ', -, hδ'val⟩ :=
    exists_counitChartHom s.toD s.toC' s.DtoC s.C'toC s.relativeSquare_comm e07 adj form
      hcounit Xc E
  exact Stacks.ModuleCat.bijective_of_extendScalarsTargetOut kC' s.toC' dC' hkC'1
    (ModuleCat.of D' P) Q aff Fm c Xc.snd eAx hAadd hAsmul δ' hδ'
    (fun p => ((congrArg eAx (hδ'val p)).trans (hE2 p)).trans (hval p).symm)

include h hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj in
/-- **The module of compatible pairs of two relatively flat modules over a cube is flat over
`B'`** ([Stacks Project, Tag 07RW]). -/
theorem cube_flat
    (hG : @Module.Flat B Gm _ _ (Module.compHom Gm σB))
    (hF : @Module.Flat A' Fm _ _ (Module.compHom Fm σA')) :
    @Module.Flat B' P _ _ (Module.compHom P σ) := by
  obtain ⟨I, base, s, eB, kD, kC', Xc, eDx, eAx, E, hD', -, hkD2, -, hkC'2, hDadd, hDsmul, hAadd,
    hAsmul, -, -⟩ :=
    exists_cubeCompatiblePairs h Gm Fm γ π₁ π₂ hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj
  have hXfst : Module.Flat B ((ModuleCat.restrictScalars s.BtoD).obj Xc.fst) :=
    flat_restrictScalars_of_equiv_ringEquiv s.BtoD σB kD hkD2 eDx hDadd hDsmul hG
  have hXsnd : Module.Flat A' ((ModuleCat.restrictScalars s.A'toC').obj Xc.snd) :=
    flat_restrictScalars_of_equiv_ringEquiv s.A'toC' σA' kC' hkC'2 eAx hAadd hAsmul hF
  obtain ⟨F, e07, adj, form, -, -, hflat07, -, -⟩ :=
    MilnorPatching.relativelyFlatModulesEquivalenceOverFibreProduct s
  have hFflat := hflat07 Xc ⟨hXfst, hXsnd⟩
  have h1 : @Module.Flat B' (F.obj Xc) _ _ (Module.compHom _ (s.toD'.comp eB.toRingHom)) :=
    flat_of_ringEquiv_base eB s.toD' hFflat
  rw [hD'] at h1
  exact flat_of_equiv_semilinear σ σ (E ≪≫ₗ (e07 Xc).symm).toEquiv
    (fun x y => map_add (E ≪≫ₗ (e07 Xc).symm) x y)
    (fun r x => (E ≪≫ₗ (e07 Xc).symm).map_smul _ x) h1

include h hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj in
/-- **A module flat over `B'` is the module of compatible pairs of its two base changes**
([Stacks Project, Tag 07RW]).  If `M` is a `D'`-module flat over `B'`, `Gm` and `Fm` are its two
base changes (through `aff₁` and `aff₂`) and `u : M ⟶ P` sends `m` to the pair of its two base
changes, then `u` is bijective. -/
theorem cube_unit_bijective (M : ModuleCat.{u} D')
    (hM : @Module.Flat B' M _ _ (Module.compHom M σ))
    (aff₁ : (ModuleCat.extendScalars dD).obj M ≅ Gm)
    (aff₂ : (ModuleCat.extendScalars dC').obj M ≅ Fm)
    (u : M →ₗ[D'] P) (hu₁ : ∀ m, π₁ (u m) = aff₁.hom ((1 : D) ⊗ₜ[D',dD] m))
    (hu₂ : ∀ m, π₂ (u m) = aff₂.hom ((1 : C') ⊗ₜ[D',dC'] m)) :
    Function.Bijective u := by
  obtain ⟨I, base, s, eB, kD, kC', Xc, eDx, eAx, E, hD', hkD1, -, hkC'1, -, hDadd, hDsmul, hAadd,
    hAsmul, hE1, hE2⟩ :=
    exists_cubeCompatiblePairs h Gm Fm γ π₁ π₂ hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj
  obtain ⟨F, e07, adj, form, hunit07, -⟩ := exists_relativeFlatAdjunction s
  obtain ⟨β, hβ, hβval⟩ := Stacks.ModuleCat.exists_extendScalarsTargetHom kD s.toD dD hkD1 M Gm
    aff₁ Xc.fst eDx hDadd hDsmul
  obtain ⟨β', hβ', hβ'val⟩ := Stacks.ModuleCat.exists_extendScalarsTargetHom kC' s.toC' dC' hkC'1
    M Fm aff₂ Xc.snd eAx hAadd hAsmul
  have hMflat :
      Module.Flat base.fibreProduct ((ModuleCat.restrictScalars.{u, u, u} s.toD').obj M) := by
    have h1 := flat_of_ringEquiv_base eB.symm σ hM
    rw [comp_symm_eq_of_comp_eq eB σ s.toD' hD'] at h1
    exact h1
  exact bijective_of_components s.toD s.toC' s.DtoC s.C'toC s.relativeSquare_comm e07 adj form
    M Xc (hunit07 M hMflat) E u β β' hβ hβ'
    (fun m => eDx.injective (((hE1 (u m)).trans (hu₁ m)).trans (hβval m).symm))
    (fun m => eAx.injective (((hE2 (u m)).trans (hu₂ m)).trans (hβ'val m).symm))

include h hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj in
/-- **The module of compatible pairs of two finite modules over a cube is finite over `D'`**
([Stacks Project, Tag 08IH], through [Stacks Project, Tag 07RW]). -/
theorem cube_finite [Module.Finite D Gm] [Module.Finite C' Fm] : Module.Finite D' P := by
  obtain ⟨I, base, s, eB, kD, kC', Xc, eDx, eAx, E, -, -, -, -, -, hDadd, hDsmul, hAadd,
    hAsmul, -, -⟩ :=
    exists_cubeCompatiblePairs h Gm Fm γ π₁ π₂ hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj
  obtain ⟨F, e07, adj, -, -, hcounit⟩ := exists_relativeFlatAdjunction s
  have hXfst : Module.Finite s.D Xc.fst := finite_of_equiv_ringEquiv kD eDx hDadd hDsmul
  have hXsnd : Module.Finite s.C' Xc.snd := finite_of_equiv_ringEquiv kC' eAx hAadd hAsmul
  have hF := MilnorPatching.finite_relativeRightAdjoint_obj_of_finite_components s F adj
    hcounit Xc hXfst hXsnd
  exact Module.Finite.equiv (E ≪≫ₗ (e07 Xc).symm).symm

include h hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj in
/-- **The module of compatible pairs of two relatively flat modules of finite presentation over
a cube whose ring map `B' ⟶ D'` is of finite presentation is of finite presentation over `D'`**
([Stacks Project, Tag 08KP], through [Stacks Project, Tag 07RW]). -/
theorem cube_finitePresentation [Module.FinitePresentation D Gm]
    [Module.FinitePresentation C' Fm]
    (hG : @Module.Flat B Gm _ _ (Module.compHom Gm σB))
    (hF : @Module.Flat A' Fm _ _ (Module.compHom Fm σA'))
    (hσ : σ.FinitePresentation) : Module.FinitePresentation D' P := by
  obtain ⟨I, base, s, eB, kD, kC', Xc, eDx, eAx, E, hD', -, hkD2, -, hkC'2, hDadd, hDsmul, hAadd,
    hAsmul, -, -⟩ :=
    exists_cubeCompatiblePairs h Gm Fm γ π₁ π₂ hπ₁add hπ₁smul hπ₂add hπ₂smul hπ hinj hsurj
  obtain ⟨F, e07, adj, -, -, hcounit⟩ := exists_relativeFlatAdjunction s
  have hXfst : Module.Flat B ((ModuleCat.restrictScalars s.BtoD).obj Xc.fst) :=
    flat_restrictScalars_of_equiv_ringEquiv s.BtoD σB kD hkD2 eDx hDadd hDsmul hG
  have hXsnd : Module.Flat A' ((ModuleCat.restrictScalars s.A'toC').obj Xc.snd) :=
    flat_restrictScalars_of_equiv_ringEquiv s.A'toC' σA' kC' hkC'2 eAx hAadd hAsmul hF
  have hXfpD : Module.FinitePresentation s.D Xc.fst :=
    finitePresentation_of_equiv_ringEquiv kD eDx hDadd hDsmul
  have hXfpC' : Module.FinitePresentation s.C' Xc.snd :=
    finitePresentation_of_equiv_ringEquiv kC' eAx hAadd hAsmul
  have hfp : s.toD'.FinitePresentation := by
    rw [← comp_symm_eq_of_comp_eq eB σ s.toD' hD']
    exact hσ.comp (RingHom.FinitePresentation.of_bijective eB.symm.bijective)
  have hflatId : @Module.Flat base.fibreProduct base.fibreProduct _ _
      (Module.compHom base.fibreProduct (RingHom.id base.fibreProduct)) :=
    Module.Flat.self
  have hFfp := MilnorPatching.finitePresentation_rightAdjoint_obj_of_factorization s F adj
    hcounit Xc hXfpD hXfst hXfpC' hXsnd (RingHom.id _) s.toD' (RingHom.comp_id _) hflatId hfp
  exact Module.FinitePresentation.of_equiv (E ≪≫ₗ (e07 Xc).symm).symm

end Modules

end Stacks.Pushout

end
