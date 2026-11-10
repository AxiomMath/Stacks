module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentImmersionFormallySmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeComparisonMap
public import StacksFrontier.RingTheory.NaiveCotangent.TwoTermProjectiveBaseChange
public import StacksFrontier.Algebra.Homology.DoubleQuasiIso
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentTowerPresentation
public import StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkTargetAction
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackTwoStep
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# `H^{-1}` of the pullback of `NL_{X/Y}` for a morphism factored through a formally smooth scheme

Let `f : X ⟶ Y` be a morphism of schemes which factors as `f = i ≫ h` with `i : X ⟶ P` an
immersion and `h : P ⟶ Y` formally smooth, and let `g' : X' ⟶ X` be any morphism of schemes.
By [Stacks Project, Tag 0FV4], `NL_{X/Y}` is the two-term complex `(𝒞_{X/P} ⟶ i^*Ω_{P/Y})` in
`D(𝒪_X)`.  This file pulls that identification back along `g'` *termwise* — inverse image along
`g'` followed by extension of scalars to `𝒪_{X'}`, the pullback
`Stacks.NaiveCotangentFlatBaseChange.pulledComplex` that [Stacks Project, Tag 0FV9] uses — and
deduces

`H^{-1}((g')^*NL_{X/Y}) ≅ Ker((g')^*𝒞_{X/P} ⟶ (g')^*i^*Ω_{P/Y})`.

Termwise pullback does not preserve quasi-isomorphisms in general, since the degree `-1` terms
are not flat.  The identification of [Stacks Project, Tag 0FV4] is, however, built from a
zig-zag of chain maps

`NL_{X/Y} ≅ NL' ⟵ NL(i⁻¹h⁻¹𝒪_Y[i⁻¹𝒪_P] ⟶ 𝒪_X) ⟶ (I/I² ⟶ 𝒪_X ⊗ Ω) ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})`

(`NL'` is `NL_{X/Y}` written over the iterated inverse image `i⁻¹h⁻¹𝒪_Y`)

whose two non-invertible arrows are, at every point `x` of `X`, the chain maps of naive
cotangent complexes induced by a morphism of extensions of `𝒪_{X,x}` whose rings are formally
smooth over the base.  Such a chain map is a quasi-isomorphism onto a two-term complex with
*projective* degree-`0` term, hence a homotopy equivalence
(`NaiveCotangent.isHomotopyEquiv_of_isQuasiIso_of_projective`), and so stays a
quasi-isomorphism after any base change.  At a point `x'` of `X'` the stalk of the termwise
pullback is the base change `𝒪_{X',x'} ⊗_{𝒪_{X,g'(x')}} (-)` of the stalk at `g'(x')`
([Stacks Project, Tag 0098]), so the two pulled-back arrows are quasi-isomorphisms stalkwise,
hence quasi-isomorphisms.  Taking `H^{-1}` of the pulled-back zig-zag gives the isomorphism.

## Main definitions

* `Stacks.NaiveCotangentPulledImmersion.pulledComplexFunctor`: the termwise pullback of complexes
  of sheaves of modules along a morphism of ringed spaces.
* `Stacks.NaiveCotangentPulledImmersion.pulledConormalHomologyNegOneIso`:
  `H^{-1}((g')^*(𝒞_{X/P} ⟶ i^*Ω_{P/Y})) ≅ Ker((g')^*𝒞_{X/P} ⟶ (g')^*i^*Ω_{P/Y})`.
* `Stacks.NaiveCotangentPulledImmersion.pulledPresentationHomologyNegOneIso`: the isomorphism
  for `NL_{X/Y}` written over the iterated inverse image `i⁻¹h⁻¹𝒪_Y`.
* `Stacks.NaiveCotangentPulledImmersion.pulledComplexHomologyNegOneIso`: **the isomorphism**
  `H^{-1}((g')^*NL_{X/Y}) ≅ Ker((g')^*𝒞_{X/P} ⟶ (g')^*i^*Ω_{P/Y})`.

## Main results

* `Stacks.NaiveCotangentPulledImmersion.quasiIso_extendScalars_map`: base change of a
  quasi-isomorphism of complexes of modules in degrees `-1` and `0` onto a complex with
  projective degree-`0` term is a quasi-isomorphism.
* `Stacks.NaiveCotangentPulledImmersion.projective_stalk_towerNaiveCotangentComplex_X_zero`: the
  degree-`0` stalks of the two-term complex of a presentation `A ⟶ B` over `R` are projective
  where `A` is formally smooth over `R`.
* `Stacks.NaiveCotangentPulledImmersion.quasiIso_pulledComplexFunctor_map`: the termwise pullback
  of a quasi-isomorphism of two-term complexes onto a complex with stalkwise projective
  degree-`0` term is a quasi-isomorphism.
* `Stacks.NaiveCotangentPulledImmersion.quasiIso_pulled_presentationComparison` and
  `quasiIso_pulled_conormalComparison`: the two arrows of the zig-zag of
  [Stacks Project, Tag 0FV4], pulled back along any `g'`, are quasi-isomorphisms.
* `Stacks.NaiveCotangentPulledImmersion.homologyMap_comp_pulledPresentationHomologyNegOneIso`:
  the compatibility of the isomorphism with the two pulled-back chain maps it is built from.

## Implementation notes

The isomorphism is not obtained from the isomorphism of [Stacks Project, Tag 0FV4] in `D(𝒪_X)`,
which cannot be pulled back termwise, but from the chain maps of its zig-zag; that is why it is
stated together with its compatibility with those chain maps.  Its target is the kernel of the
pullback along `g'` of the first arrow of the conormal sequence, the pullback being the two-step
model `RingedSpaceModuleAdjunction.twoStepPullback` (inverse image, then extension of scalars),
which is the one the termwise pullback of complexes is made of.

No cartesian square is involved: `g'` is arbitrary.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9), where the statement is
  used.
* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098), the stalk of a pullback.
* [Stacks Project, Tag 031J](https://stacks.math.columbia.edu/tag/031J), projectivity of the
  module of differentials of a formally smooth algebra.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct
open AlgebraicGeometry NaiveCotangent
open Stacks.Sites.Conormal Stacks.SheafOfModules
open AlgebraicGeometry.SheafOfModules (inverseImageRingHom stalkFunctor)
open Stacks.RelativeDifferentialStalk (algebraStalk)

universe u v

noncomputable section

namespace Stacks.NaiveCotangentPulledImmersion

section Algebra

variable {S : Type u} [CommRing S] {K L : CochainComplex (ModuleCat.{v} S) ℤ}

/-- The two-term complex of `S`-modules underlying a cochain complex in degrees `-1` and `0`. -/
def twoTerm (K : CochainComplex (ModuleCat.{v} S) ℤ) : TwoTerm S where
  X₁ := K.X (-1)
  X₀ := K.X 0
  d := (K.d (-1) 0).hom

/-- The chain map of two-term complexes underlying a morphism of cochain complexes. -/
def twoTermMap (φ : K ⟶ L) : ChainMap (twoTerm K) (twoTerm L) where
  f₁ := (φ.f (-1)).hom
  f₀ := (φ.f 0).hom
  comm := congrArg ModuleCat.Hom.hom (φ.comm (-1) 0)

/-- In degree `-1`, with nothing in degree `-2`, a quasi-isomorphism is an isomorphism on
cycles. -/
theorem isIso_cyclesMap_of_quasiIsoAt (φ : K ⟶ L) [QuasiIsoAt φ (-1)]
    (hK : IsZero (K.X (-2))) (hL : IsZero (L.X (-2))) :
    IsIso (HomologicalComplex.cyclesMap φ (-1)) := by
  have hprev : (ComplexShape.up ℤ).prev (-1) = -2 := by rw [CochainComplex.prev]; norm_num
  have h₁ := K.isIso_homologyπ (-2) (-1) hprev (hK.eq_of_src _ _)
  have h₂ := L.isIso_homologyπ (-2) (-1) hprev (hL.eq_of_src _ _)
  have e : HomologicalComplex.cyclesMap φ (-1) =
      K.homologyπ (-1) ≫ HomologicalComplex.homologyMap φ (-1) ≫ inv (L.homologyπ (-1)) := by
    rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [e]
  infer_instance

/-- In degree `0`, with nothing in degree `1`, a quasi-isomorphism is an isomorphism on
opcycles. -/
theorem isIso_opcyclesMap_of_quasiIsoAt (φ : K ⟶ L) [QuasiIsoAt φ 0]
    (hK : IsZero (K.X 1)) (hL : IsZero (L.X 1)) :
    IsIso (HomologicalComplex.opcyclesMap φ 0) := by
  have hnext : (ComplexShape.up ℤ).next 0 = 1 := by rw [CochainComplex.next]; norm_num
  have h₁ := K.isIso_homologyι 0 1 hnext (hK.eq_of_tgt _ _)
  have h₂ := L.isIso_homologyι 0 1 hnext (hL.eq_of_tgt _ _)
  have e : HomologicalComplex.opcyclesMap φ 0 =
      inv (K.homologyι 0) ≫ HomologicalComplex.homologyMap φ 0 ≫ L.homologyι 0 := by
    rw [HomologicalComplex.homologyι_naturality, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- **A quasi-isomorphism of complexes of modules in degrees `-1` and `0` is a
quasi-isomorphism of the underlying two-term complexes.** -/
theorem isQuasiIso_twoTermMap (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i)) :
    IsQuasiIso (twoTermMap φ) := by
  have hc := isIso_cyclesMap_of_quasiIsoAt φ (hK (-2) (by decide) (by decide))
    (hL (-2) (by decide) (by decide))
  have ho := isIso_opcyclesMap_of_quasiIsoAt φ (hK 1 (by decide) (by decide))
    (hL 1 (by decide) (by decide))
  have hcb := (ConcreteCategory.isIso_iff_bijective _).mp hc
  have hob := (ConcreteCategory.isIso_iff_bijective _).mp ho
  have hi : ∀ M : CochainComplex (ModuleCat.{v} S) ℤ, Function.Injective (M.iCycles (-1)) :=
    fun M => (ModuleCat.mono_iff_injective _).mp inferInstance
  have hmap : ∀ a : K.cycles (-1), L.iCycles (-1) (HomologicalComplex.cyclesMap φ (-1) a) =
      φ.f (-1) (K.iCycles (-1) a) :=
    fun a => congr($(HomologicalComplex.cyclesMap_i φ (-1)) a)
  have hp : ∀ M : CochainComplex (ModuleCat.{v} S) ℤ, Function.Surjective (M.pOpcycles 0) :=
    fun M => (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hpmap : ∀ x : K.X 0, HomologicalComplex.opcyclesMap φ 0 (K.pOpcycles 0 x) =
      L.pOpcycles 0 (φ.f 0 x) :=
    fun x => congr($(HomologicalComplex.p_opcyclesMap φ 0) x)
  have hKd : ∀ a : K.cycles (-1), K.d (-1) 0 (K.iCycles (-1) a) = 0 :=
    fun a => congr($(K.iCycles_d (-1) 0) a)
  have hcyc : ∀ (M : CochainComplex (ModuleCat.{v} S) ℤ) (x : M.X (-1)),
      M.d (-1) 0 x = 0 → ∃ a : M.cycles (-1), M.iCycles (-1) a = x := by
    intro M x hx
    refine HomologicalComplex.exists_iCycles_eq M (-1) x ?_
    rw [show (ComplexShape.up ℤ).next (-1) = 0 by rw [CochainComplex.next]; norm_num]
    exact hx
  have hbd : ∀ (M : CochainComplex (ModuleCat.{v} S) ℤ) (x : M.X 0),
      M.pOpcycles 0 x = 0 → ∃ y : M.X (-1), M.d (-1) 0 y = x := by
    intro M x hx
    obtain ⟨y, hy⟩ := HomologicalComplex.exists_d_eq_of_pOpcycles_eq_zero M 0 x hx
    revert y
    rw [show (ComplexShape.up ℤ).prev 0 = -1 by rw [CochainComplex.prev]; norm_num]
    exact fun y hy => ⟨y, hy⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine (injective_iff_map_eq_zero (twoTermMap φ).onH₁).mpr fun x hx => ?_
    obtain ⟨a, ha⟩ := hcyc K x.1 x.2
    have h0 : HomologicalComplex.cyclesMap φ (-1) a = 0 := by
      refine hi L ?_
      rw [hmap, ha, map_zero]
      exact congrArg Subtype.val hx
    have ha0 : a = 0 := hcb.1 (h0.trans (map_zero _).symm)
    refine Subtype.ext ?_
    rw [← ha, ha0, map_zero]
    rfl
  · intro y
    obtain ⟨b, hb⟩ := hcyc L y.1 y.2
    obtain ⟨a, rfl⟩ := hcb.2 b
    refine ⟨⟨K.iCycles (-1) a, hKd a⟩, Subtype.ext ?_⟩
    exact (hmap a).symm.trans hb
  · refine (injective_iff_map_eq_zero (twoTermMap φ).onH₀).mpr fun x hx => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [onH₀_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨m, hm⟩ := hx
    have h1 : L.pOpcycles 0 (φ.f 0 x) = 0 := by
      show L.pOpcycles 0 (φ.f 0 x) = 0
      rw [← (show (twoTerm L).d m = φ.f 0 x from hm)]
      exact congr($(L.d_pOpcycles (-1) 0) m)
    have h2 : K.pOpcycles 0 x = 0 :=
      hob.1 (((hpmap x).trans h1).trans (map_zero _).symm)
    obtain ⟨y, hy⟩ := hbd K x h2
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, hy⟩
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨t, ht⟩ := hob.2 (L.pOpcycles 0 y)
    obtain ⟨x, rfl⟩ := hp K t
    rw [hpmap] at ht
    have h0 : L.pOpcycles 0 (φ.f 0 x - (show L.X 0 from y)) = 0 := by
      rw [map_sub, ht, sub_self]
    obtain ⟨z, hz⟩ := hbd L _ h0
    exact ⟨Submodule.Quotient.mk x, (Submodule.Quotient.eq _).mpr ⟨z, hz⟩⟩

/-- **Base change of a quasi-isomorphism of complexes in degrees `-1` and `0` onto a complex
with projective degree-`0` term.** -/
theorem quasiIso_extendScalars_map {T : Type u} [CommRing T] (ρ : S →+* T) (φ : K ⟶ L)
    [hφ : QuasiIso φ] (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i)) [hP : Module.Projective S (L.X 0)] :
    QuasiIso (((ModuleCat.extendScalars.{u, u, v} ρ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ) := by
  let _ := ρ.toAlgebra
  have : Module.Projective S (twoTerm L).X₀ := hP
  have hq := IsQuasiIso.baseChange_of_projective T (isQuasiIso_twoTermMap φ hK hL)
  refine CochainComplex.quasiIso_of_isZero_X_of_bijective _
    (fun i h1 h2 => (ModuleCat.extendScalars.{u, u, v} ρ).map_isZero (hK i h1 h2))
    (fun i h1 h2 => (ModuleCat.extendScalars.{u, u, v} ρ).map_isZero (hL i h1 h2)) ?_ ?_ ?_ ?_
  · exact hq.eq_zero_of_d_eq_zero
  · exact hq.exists_of_d_eq_zero
  · exact hq.exists_d_eq
  · exact hq.exists_add_d_eq

end Algebra

section Stalk

variable {T : TopCat.{u}} (R A B : CategoryTheory.Sheaf (Opens.grothendieckTopology T)
    CommRingCat.{u}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ.hom] (x : T)

/-- **The stalk identification of `B ⊗_A Ω[A/R]` is semilinear over the `RingCat`-valued stalk
of `B`**: a scalar `s` acts on the cotangent space of the stalk extension through
`SemilinearStalk.commStalkRingEquiv`. -/
theorem cotangentSpaceStalkLinearEquiv_ringCat_smul [DecidableEq (OrderDual (OpenNhds x))]
    (s : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology T) R A B a φ).val.presheaf x)) :
    letI := algebraStalk a.hom x
    letI := algebraStalk φ.hom x
    cotangentSpaceStalkLinearEquiv R A B a φ x (s • ξ) =
      SemilinearStalk.commStalkRingEquiv B.obj x s •
        cotangentSpaceStalkLinearEquiv R A B a φ x ξ := by
  let := algebraStalk a.hom x
  let := algebraStalk φ.hom x
  obtain ⟨r, hr⟩ : ∃ r : ToType (TopCat.Presheaf.stalk A.obj x),
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom).hom r =
        SemilinearStalk.commStalkRingEquiv B.obj x s :=
    stalkMap_surjective φ.hom x (SemilinearStalk.commStalkRingEquiv B.obj x s)
  have hs : (SemilinearStalk.commStalkRingEquiv B.obj x).symm
      (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom).hom r) = s :=
    Eq.trans (congrArg (SemilinearStalk.commStalkRingEquiv B.obj x).symm hr)
      ((SemilinearStalk.commStalkRingEquiv B.obj x).symm_apply_apply s)
  have h1 : s • ξ = r • ξ := by
    rw [tensorDifferentialsSheafStalk_ringCat_smul_eq R A B a φ x r ξ, hs]
  rw [h1, LinearEquiv.map_smul, ← hr]
  exact (algebraMap_smul (ToType (TopCat.Presheaf.stalk B.obj x)) r _).symm

/-- **The stalk of `B ⊗_A Ω[A/R]` is projective when `A` is formally smooth over `R` at `x`**,
as a module over the `RingCat`-valued stalk of `B`: it is the base change `Bₓ ⊗_{Aₓ} Ω[Aₓ/Rₓ]`
of the projective `Aₓ`-module `Ω[Aₓ/Rₓ]`. -/
theorem projective_stalk_tensorDifferentialsSheaf
    (hfs : letI := algebraStalk a.hom x
      Algebra.FormallySmooth (ToType (TopCat.Presheaf.stalk R.obj x))
        (ToType (TopCat.Presheaf.stalk A.obj x))) :
    Module.Projective (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x))
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) x).obj
          (tensorDifferentialsSheaf (Opens.grothendieckTopology T) R A B a φ)) := by
  let := algebraStalk a.hom x
  let := algebraStalk φ.hom x
  let _ : DecidableEq (OrderDual (OpenNhds x)) := Classical.decEq _
  let e : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x) ≃+*
        ToType (TopCat.Presheaf.stalk B.obj x) :=
    SemilinearStalk.commStalkRingEquiv B.obj x
  have : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  have : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let E : ↑((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) x).obj
          (tensorDifferentialsSheaf (Opens.grothendieckTopology T) R A B a φ))
      ≃ₛₗ[e.toRingHom] (ToType (TopCat.Presheaf.stalk B.obj x) ⊗[ToType
        (TopCat.Presheaf.stalk A.obj x)] KaehlerDifferential
          (ToType (TopCat.Presheaf.stalk R.obj x)) (ToType (TopCat.Presheaf.stalk A.obj x))) :=
    { (cotangentSpaceStalkLinearEquiv R A B a φ x).toAddEquiv with
      map_smul' := fun s ξ => cotangentSpaceStalkLinearEquiv_ringCat_smul R A B a φ x s ξ }
  have : Module.Projective (ToType (TopCat.Presheaf.stalk B.obj x))
      (ToType (TopCat.Presheaf.stalk B.obj x) ⊗[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x))) :=
    Module.Projective.tensorProduct
  exact Module.Projective.of_equiv E.symm

/-- **The degree-`0` stalks of the two-term complex of a presentation are projective** when the
presenting ring is formally smooth over the base at the point. -/
theorem projective_stalk_towerNaiveCotangentComplex_X_zero
    (hfs : letI := algebraStalk a.hom x
      Algebra.FormallySmooth (ToType (TopCat.Presheaf.stalk R.obj x))
        (ToType (TopCat.Presheaf.stalk A.obj x))) :
    Module.Projective (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x))
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) x).obj
          ((towerNaiveCotangentComplex R A B a φ).X 0)) := by
  rw [towerNaiveCotangentComplex_X_zero]
  exact projective_stalk_tensorDifferentialsSheaf R A B a φ x hfs

end Stalk

section Pulled

/-- Quasi-isomorphy of the termwise image of a morphism under a composite of additive functors is
transported along an isomorphism of composites. -/
theorem quasiIso_map_map_of_iso {C D M N : Type*} [Category C] [Category D] [Category M]
    [Category N] [Preadditive C] [Preadditive D] [Preadditive M] [Abelian N] {ι : Type*}
    {c : ComplexShape ι} (F : C ⥤ D) (S : D ⥤ N) (S₀ : C ⥤ M) (B : M ⥤ N) [hF : F.Additive]
    [hS : S.Additive] [hS₀ : S₀.Additive] [hB : B.Additive] (e : F ⋙ S ≅ S₀ ⋙ B)
    {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (h : QuasiIso ((B.mapHomologicalComplex c).map ((S₀.mapHomologicalComplex c).map φ))) :
    QuasiIso ((S.mapHomologicalComplex c).map ((F.mapHomologicalComplex c).map φ)) :=
  (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex e c) (Arrow.mk φ))).mpr h


variable {X X' : RingedSpace.{u, u}} (g' : X' ⟶ X)

/-- The termwise pullback of complexes along `g'`: the inverse image of sheaves of modules
followed by extension of scalars along `g'⁻¹𝒪_X ⟶ 𝒪_{X'}`, applied in each degree. -/
abbrev pulledComplexFunctor :
    CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ ⥤
      CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X'.carrier) X'.sheaf)) ℤ :=
  (_root_.SheafOfModules.pullback.{u}
      (inverseImageRingHom g'.hom.base X.sheaf)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    inverseImageExtendScalarsComplexes g'

/-- The stalk at `x'` of the two-step pullback is the base change of the stalk at `g' x'`. -/
def stalkTwoStepPullbackIso (x' : X'.carrier) :
    RingedSpaceModuleAdjunction.twoStepPullback g' ⋙
        stalkFunctor (structureSheafRing X') x' ≅
      stalkFunctor (structureSheafRing X) (g'.hom.base x') ⋙
        Stacks.RingedSpace.stalkBaseChange g' x' :=
  Functor.isoWhiskerRight (RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep g').symm _ ≪≫
    Stacks.RingedSpace.stalkModulePullbackFunctorIso g' x'

/-- The termwise pullback of a complex vanishes in every degree in which the complex does. -/
theorem isZero_pulledComplexFunctor_obj_X
    (K : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ) (n : ℤ) (hK : IsZero (K.X n)) :
    IsZero (((pulledComplexFunctor g').obj K).X n) := by
  have h₁ := Functor.map_isZero
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom g'.hom.base X.sheaf)) hK
  have := towerExtendScalars_additive (Opens.grothendieckTopology X'.carrier)
    (inverseImageMiddleRing g') X'.sheaf (ringedSpaceStructureMap g')
  exact Functor.map_isZero
    (towerExtendScalars (Opens.grothendieckTopology X'.carrier) (inverseImageMiddleRing g')
      X'.sheaf (ringedSpaceStructureMap g')) h₁

/-- **The termwise pullback of a quasi-isomorphism of two-term complexes onto a complex with
stalkwise projective degree-`0` term is a quasi-isomorphism.** -/
theorem quasiIso_pulledComplexFunctor_map
    {K L : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i))
    (hproj : ∀ x : X.carrier, Module.Projective
      (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf).obj x))
      ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf) x).obj (L.X 0))) :
    QuasiIso ((pulledComplexFunctor g').map φ) := by
  refine (AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso _ _).mpr
    fun x' => ?_
  have hφx : QuasiIso (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf)
        (g'.hom.base x')).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) :=
    (AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso _ _).mp
      inferInstance (g'.hom.base x')
  let := Stacks.RingedSpace.structureStalkCommRing X (g'.hom.base x')
  let := Stacks.RingedSpace.structureStalkCommRing X' x'
  have h := quasiIso_extendScalars_map (Stacks.RingedSpace.stalkRingMap g' x').hom
    _
    (fun i h1 h2 => AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ _ _ (hK i h1 h2))
    (fun i h1 h2 => AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ _ _ (hL i h1 h2))
    (hφ := hφx) (hP := hproj (g'.hom.base x'))
  exact quasiIso_map_map_of_iso (hS := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive _ x')
    (hS₀ := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive _ _)
    (hB := Stacks.RingedSpace.stalkBaseChange_additive g' x')
    (RingedSpaceModuleAdjunction.twoStepPullback g') (stalkFunctor (structureSheafRing X') x')
    (stalkFunctor (structureSheafRing X) (g'.hom.base x'))
    (Stacks.RingedSpace.stalkBaseChange g' x') (stalkTwoStepPullbackIso g' x') φ h

end Pulled

/-! ### Homology in degree `-1` of a complex with nothing in degree `-2` -/

section HomologyNegOne

universe w₁ w₂

variable {C : Type w₂} [Category.{w₁} C] [Abelian C]

/-- The homology in degree `-1` of a cochain complex with zero term in degree `-2` is the kernel
of its differential `d : X⁻¹ ⟶ X⁰`. -/
def homologyNegOneIsoKernel (M : CochainComplex C ℤ) (h : IsZero (M.X (-2))) :
    M.homology (-1) ≅ kernel (M.d (-1) 0) :=
  M.homologyIsoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
    (ShortComplex.asIsoHomologyπ _ (h.eq_of_src _ _)).symm ≪≫ ShortComplex.cyclesIsoKernel _

/-- The kernel of a morphism conjugated by two isomorphisms is the kernel of the morphism. -/
def kernelConjIso {A A' B B' : C} (e₁ : A ≅ A') (f : A' ⟶ B') (e₀ : B ≅ B') :
    kernel (e₁.hom ≫ f ≫ e₀.inv) ≅ kernel f :=
  kernelIsIsoComp _ _ ≪≫ kernelCompMono _ _

omit [Abelian C] in
/-- A functor carries a triple composite to the triple composite of the images. -/
private theorem map_comp_comp {D : Type*} [Category D] (F : C ⥤ D) {A B B' A' : C} (a : A ⟶ B)
    (b : B ⟶ B') (c : B' ⟶ A') : F.map (a ≫ b ≫ c) = F.map a ≫ F.map b ≫ F.map c := by
  simp

omit [Abelian C] in
/-- Precomposing `e.symm ≪≫ g` with `e` gives `g`. -/
private theorem hom_comp_symm_trans {A B D : C} (e : A ≅ B) (g : A ≅ D) :
    e.hom ≫ (e.symm ≪≫ g).hom = g.hom := by
  simp

end HomologyNegOne

/-! ### The zig-zag of `[Stacks Project, Tag 0FV4]`, pulled back -/

section Scheme

open Stacks.Sites.FreeAlgebra
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)

variable {X P Y X' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) [IsImmersion i] (g' : X' ⟶ X)

/-- The comparison of [Stacks Project, Tag 08TL] between the naive cotangent complex of the
polynomial presentation of `𝒪_X` on the sections of `i⁻¹𝒪_P` and `NL_{X/Y}`, written over the
iterated inverse image `i⁻¹h⁻¹𝒪_Y`. -/
abbrev presentationComparison :=
  naiveCotangentComplexComparison.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
      ringedSpaceStructureMap (ringedSpaceHom i))
    (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageMiddleRing (ringedSpaceHom i)))
    (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom i)))

/-- **The pulled-back comparison of [Stacks Project, Tag 08TL] is a quasi-isomorphism**, for
every `g' : X' ⟶ X`: the degree-`0` stalks of `NL_{X/Y}` are free. -/
theorem quasiIso_pulled_presentationComparison :
    QuasiIso ((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h)) := by
  have := Stacks.NaiveCotangentTower.quasiIso_schemePresentationComparison i h
  refine quasiIso_pulledComplexFunctor_map _ _
    (fun j h1 h2 => presentationNaiveCotangentComplex_isZero_X.{u, u, u, u} _ _ _ _ _ _ j h1 h2)
    (fun j h1 h2 => naiveCotangentComplex_isZero_X.{u, u, u, u} _ _ _ _ j h1 h2) fun x => ?_
  have := presentation_id_isLocallySurjective
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
      ringedSpaceStructureMap (ringedSpaceHom i))
  exact projective_stalk_towerNaiveCotangentComplex_X_zero
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
    (freeAlgebraSheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
      (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        X.toRingedSpace.sheaf)) X.toRingedSpace.sheaf
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
      (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        X.toRingedSpace.sheaf))
    (presentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
        ringedSpaceStructureMap (ringedSpaceHom i))
      (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        X.toRingedSpace.sheaf) (𝟙 _)) x
    (formallySmooth_stalk_freeAlgebraSheaf _ _ x)

/-- **The pulled-back comparison of the polynomial presentation with the presentation
`i⁻¹𝒪_P ⟶ 𝒪_X` is a quasi-isomorphism** for `h` formally smooth and every `g' : X' ⟶ X`: the
degree-`0` stalks of the target are projective. -/
theorem quasiIso_pulled_schemeTowerComparison (hg : Stacks.Smooth.FormallySmoothScheme h) :
    QuasiIso ((pulledComplexFunctor g'.toLRSHom.toShHom).map
      (Stacks.NaiveCotangentTower.schemeTowerComparison i h)) := by
  have := Stacks.NaiveCotangentTower.quasiIso_schemeTowerComparison i h hg
  refine quasiIso_pulledComplexFunctor_map _ _
    (fun j h1 h2 => towerNaiveCotangentComplex_isZero_X _ _ _ _ _ j h1 h2)
    (fun j h1 h2 => towerNaiveCotangentComplex_isZero_X _ _ _ _ _ j h1 h2) fun x => ?_
  exact projective_stalk_towerNaiveCotangentComplex_X_zero _ _ _ _ _ x
    (Stacks.NaiveCotangentInverseImageStalkSmooth.formallySmooth_stalk_inverseImageFirstRingMap
      i h hg x)

/-- The isomorphism of complexes `(I/I² ⟶ 𝒪_X ⊗ Ω) ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})` of
[Stacks Project, Tag 0FV4], with its two inputs discharged. -/
abbrev towerIso :=
  Stacks.NaiveCotangentConormalAssembly.towerComplexIso i h
    (Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i h)
    (Stacks.NaiveCotangentConormalAssembly.hsq_of_transpose i h
      (Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i h)
      (Stacks.NaiveCotangentConormalTranspose.conormalTranspose_comp i h))

/-- **The pulled-back comparison of the polynomial presentation with
`(𝒞_{X/P} ⟶ i^*Ω_{P/Y})` is a quasi-isomorphism** for `h` formally smooth. -/
theorem quasiIso_pulled_conormalComparison (hg : Stacks.Smooth.FormallySmoothScheme h) :
    QuasiIso ((pulledComplexFunctor g'.toLRSHom.toShHom).map
      (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom)) := by
  have := quasiIso_pulled_schemeTowerComparison i h g' hg
  have e := (pulledComplexFunctor g'.toLRSHom.toShHom).map_comp
    (Stacks.NaiveCotangentTower.schemeTowerComparison i h) (towerIso i h).hom
  have : IsIso ((pulledComplexFunctor g'.toLRSHom.toShHom).map (towerIso i h).hom) :=
    ((pulledComplexFunctor g'.toLRSHom.toShHom).mapIso (towerIso i h)).isIso_hom
  have : QuasiIso ((pulledComplexFunctor g'.toLRSHom.toShHom).map (towerIso i h).hom) :=
    quasiIso_of_isIso _
  exact e ▸ quasiIso_comp _ _

/-- The differential of the pulled-back complex `(g')^*(𝒞_{X/P} ⟶ i^*Ω_{P/Y})` is the
pulled-back conormal differential, conjugated by the pullbacks of the identifications of the
two terms. -/
theorem pulled_conormalDifferentialComplex_d :
    ((pulledComplexFunctor g'.toLRSHom.toShHom).obj
        (Stacks.ConormalSequenceRight.conormalDifferentialComplex i h)).d (-1) 0 =
      ((RingedSpaceModuleAdjunction.twoStepPullback g'.toLRSHom.toShHom).mapIso
          (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i h)).hom ≫
        (RingedSpaceModuleAdjunction.twoStepPullback g'.toLRSHom.toShHom).map
          (Stacks.ConormalSequenceRight.conormalDifferential i h) ≫
        ((RingedSpaceModuleAdjunction.twoStepPullback g'.toLRSHom.toShHom).mapIso
          (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoZero i h)).inv := by
  change (RingedSpaceModuleAdjunction.twoStepPullback g'.toLRSHom.toShHom).map
    ((Stacks.ConormalSequenceRight.conormalDifferentialComplex i h).d (-1) 0) = _
  rw [Stacks.ConormalSequenceRight.conormalDifferentialComplex_d_negOne_zero]
  exact map_comp_comp _ _ _ _

/-- **`H^{-1}((g')^*(𝒞_{X/P} ⟶ i^*Ω_{P/Y}))` is the kernel of the pulled-back conormal
differential** `(g')^*𝒞_{X/P} ⟶ (g')^*i^*Ω_{P/Y}`. -/
def pulledConormalHomologyNegOneIso :
    ((pulledComplexFunctor g'.toLRSHom.toShHom).obj
        (Stacks.ConormalSequenceRight.conormalDifferentialComplex i h)).homology (-1) ≅
      kernel ((RingedSpaceModuleAdjunction.twoStepPullback g'.toLRSHom.toShHom).map
        (Stacks.ConormalSequenceRight.conormalDifferential i h)) :=
  homologyNegOneIsoKernel _ (isZero_pulledComplexFunctor_obj_X _ _ _
      (Stacks.ConormalSequenceRight.conormalDifferentialComplex_isZero_X i h (-2)
        (by decide) (by decide))) ≪≫
    kernelIsoOfEq (pulled_conormalDifferentialComplex_d i h g') ≪≫ kernelConjIso _ _ _

/-- **`H^{-1}((g')^*NL_{X/Y})` is the kernel of the pulled-back conormal differential**, in the
spelling of `NL_{X/Y}` over the iterated inverse image `i⁻¹h⁻¹𝒪_Y`, for `h` formally smooth.
It is the inverse of the isomorphism induced on `H^{-1}` by the pulled-back comparison of
[Stacks Project, Tag 08TL], followed by the one induced by the pulled-back comparison with
`(𝒞_{X/P} ⟶ i^*Ω_{P/Y})`, followed by `pulledConormalHomologyNegOneIso`; see
`homologyMap_comp_pulledPresentationHomologyNegOneIso`. -/
def pulledPresentationHomologyNegOneIso (hg : Stacks.Smooth.FormallySmoothScheme h) :
    ((pulledComplexFunctor g'.toLRSHom.toShHom).obj
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.toRingedSpace.carrier)
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
          (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
            ringedSpaceStructureMap (ringedSpaceHom i)))).homology (-1) ≅
      kernel ((RingedSpaceModuleAdjunction.twoStepPullback g'.toLRSHom.toShHom).map
        (Stacks.ConormalSequenceRight.conormalDifferential i h)) :=
  (@asIso _ _ _ _ (HomologicalComplex.homologyMap
      ((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h)) (-1))
      ((quasiIsoAt_iff_isIso_homologyMap _ (-1)).mp
        ((quasiIso_pulled_presentationComparison i h g').quasiIsoAt (-1)))).symm ≪≫
    @asIso _ _ _ _ (HomologicalComplex.homologyMap ((pulledComplexFunctor g'.toLRSHom.toShHom).map
      (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom)) (-1))
      ((quasiIsoAt_iff_isIso_homologyMap _ (-1)).mp
        ((quasiIso_pulled_conormalComparison i h g' hg).quasiIsoAt (-1))) ≪≫
    pulledConormalHomologyNegOneIso i h g'

/-- **The compatibility of `pulledPresentationHomologyNegOneIso` with the chain maps it is
built from**: precomposed with the map induced on `H^{-1}` by the pulled-back comparison of
[Stacks Project, Tag 08TL], it is the map induced by the pulled-back comparison with
`(𝒞_{X/P} ⟶ i^*Ω_{P/Y})`, followed by `pulledConormalHomologyNegOneIso`.  Since the first map
is invertible, this characterises the isomorphism. -/
theorem homologyMap_comp_pulledPresentationHomologyNegOneIso
    (hg : Stacks.Smooth.FormallySmoothScheme h) :
    HomologicalComplex.homologyMap
        ((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h)) (-1) ≫
      (pulledPresentationHomologyNegOneIso i h g' hg).hom =
    HomologicalComplex.homologyMap ((pulledComplexFunctor g'.toLRSHom.toShHom).map
        (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom)) (-1) ≫
      (pulledConormalHomologyNegOneIso i h g').hom :=
  hom_comp_symm_trans
    (@asIso _ _ _ _ (HomologicalComplex.homologyMap
      ((pulledComplexFunctor g'.toLRSHom.toShHom).map (presentationComparison i h)) (-1))
      ((quasiIsoAt_iff_isIso_homologyMap _ (-1)).mp
        ((quasiIso_pulled_presentationComparison i h g').quasiIsoAt (-1))))
    (@asIso _ _ _ _ (HomologicalComplex.homologyMap ((pulledComplexFunctor g'.toLRSHom.toShHom).map
      (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom)) (-1))
      ((quasiIsoAt_iff_isIso_homologyMap _ (-1)).mp
        ((quasiIso_pulled_conormalComparison i h g' hg).quasiIsoAt (-1))) ≪≫
    pulledConormalHomologyNegOneIso i h g')

/-- The pullback `(g')^*NL_{X/Y}` is the termwise pullback of `NL_{X/Y}`. -/
theorem pulledComplex_eq (f : X ⟶ Y) :
    Stacks.NaiveCotangentFlatBaseChange.pulledComplex f g' =
      (pulledComplexFunctor g'.toLRSHom.toShHom).obj (Scheme.naiveCotangentComplex f) :=
  rfl

/-- **`H^{-1}((g')^*NL_{X/Y}) ≅ Ker((g')^*𝒞_{X/P} ⟶ (g')^*i^*Ω_{P/Y})`.**  Let `f : X ⟶ Y` factor
as `f = i ≫ h` with `i : X ⟶ P` an immersion and `h : P ⟶ Y` formally smooth, and let
`g' : X' ⟶ X` be any morphism of schemes.  The degree `-1` cohomology sheaf of the termwise
pullback `(g')^*NL_{X/Y}` (`Stacks.NaiveCotangentFlatBaseChange.pulledComplex`) is the kernel of
the pullback along `g'` of the first arrow `𝒞_{X/P} ⟶ i^*Ω_{P/Y}` of the conormal sequence.

The isomorphism is the composite of the identification of `NL_{X/Y}` with its spelling over
the iterated inverse image (`Stacks.NaiveCotangentTower.schemePresentationIso`), pulled back,
with `pulledPresentationHomologyNegOneIso`. -/
def pulledComplexHomologyNegOneIso (f : X ⟶ Y) (hf : f = i ≫ h)
    (hg : Stacks.Smooth.FormallySmoothScheme h) :
    (Stacks.NaiveCotangentFlatBaseChange.pulledComplex f g').homology (-1) ≅
      kernel ((RingedSpaceModuleAdjunction.twoStepPullback g'.toLRSHom.toShHom).map
        (Stacks.ConormalSequenceRight.conormalDifferential i h)) :=
  eqToIso (congrArg (fun m : X ⟶ Y ↦
      (Stacks.NaiveCotangentFlatBaseChange.pulledComplex m g').homology (-1)) hf) ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-1)).mapIso
      ((pulledComplexFunctor g'.toLRSHom.toShHom).mapIso
        (Stacks.NaiveCotangentTower.schemePresentationIso i h)) ≪≫
    pulledPresentationHomologyNegOneIso i h g' hg

end Scheme

end Stacks.NaiveCotangentPulledImmersion

end

end
