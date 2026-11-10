module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDegreeBound
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxFreeGradedMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxSmulTmul
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.AffineOpen

/-!
# The degreewise epimorphic presentation of a graded module of finite type

This file is the construction the dévissage of part (2) of [Stacks, Tag 0897] is waiting for:
for a quasi-coherent graded module `N` of finite type on affine opens over a sheaf of graded
algebras `𝓟` on a quasi-compact scheme, a degreewise epimorphism `Q ⟶ N` whose source is
quasi-coherent, of finite type on affine opens, and has uniformly acyclic twists.

## Main results

* `Stacks.Coherent.exists_sum_app_of_cofanIsColimit` — **a section of a finite coproduct of
  `𝒪_X`-modules is a sum of sections of the summands.** A finite coproduct in an additive
  category is a biproduct, so it splits at every open even though the coproduct is formed by
  sheafification.
* `Stacks.Coherent.isFiniteTypeOnAffine_directSum` — **a finite direct sum of graded modules of
  finite type on affine opens is of finite type on affine opens.** The generators are the images
  of the generators of the summands under the coproduct injections.
* `Stacks.Coherent.surjective_freeGradedMk` — **over an affine open the pure tensors of sections
  exhaust the pieces of `F ⊗ 𝓟(-d)`**, for quasi-coherent `F` and `𝓟_{n-d}`.
* `Stacks.Coherent.freeGradedMk_one_smul` and
  `Stacks.Coherent.freeGradedMk_mem_generatedSet` — the pure tensor `g ⊗ a` is the generator
  `g ⊗ 1`, placed in degree `d`, acted on by the homogeneous section `a` of `𝓟`.
* `Stacks.Coherent.isFiniteTypeOnAffine_freeGradedModuleOn` — **the free graded module
  `F ⊗ 𝓟(-d)` is of finite type on affine opens**, for a quasi-coherent `F` whose sections over
  each affine open form a finite module.

## Implementation notes

The generators of `F ⊗ 𝓟(-d)` over an affine open are the `gᵢ ⊗ 1` for a finite generating family
`gᵢ` of `Γ(F, U)` over `Γ(X, U)`, and reducing an arbitrary pure tensor `g ⊗ a` to them needs the
scalar moved across the tensor product: `g = ∑ᵢ cᵢ · gᵢ` gives
`g ⊗ a = ∑ᵢ gᵢ ⊗ (cᵢ · a)`. That step is *not* available at a use site phrased with `Γ(-, -)`,
because the scalar is typed over `AlgebraicGeometry.Scheme.ringCatSheaf` while the sectionwise
tensor product is formed over
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf` — definitionally the same ring,
not syntactically, and not sharing a `CommSemiring` instance, so the
`TensorProduct.CompatibleSMul` instance `TensorProduct.smul_tmul` needs is not found. It is
supplied once, on an arbitrary ringed site, by `Stacks.Coherent.map_tmul_mem_of_sum_smul` in
`CompletionProjectiveEquivalenceAuxSmulTmul.lean`; nothing here mentions
`TensorProduct.CompatibleSMul`.

The homogeneous degree is written `d + m` rather than `n` throughout the finite-type proof, so
that the degree of the action on a generator — which is `d + m` by construction — needs no
transport.

The degreewise epimorphic presentation itself is assembled in
`CompletionProjectiveEquivalenceAuxEpiAssembly.lean`, from
`Stacks.Coherent.exists_finset_epi_degreePresentationHom`,
`Stacks.Coherent.isFiniteTypeOnAffine_directSum` over
`Stacks.Coherent.isFiniteTypeOnAffine_freeGradedModuleOn`, and the two statements about the
pieces of a degreewise direct sum in
`CompletionProjectiveEquivalenceAuxDirectSumPiece.lean`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample (IsInvertibleModule tensorPowModule)
open Stacks.RelativeVeryAmple (tensorModules)
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open scoped TensorProduct

universe u

namespace Stacks.Coherent

variable {X : Scheme.{u}}

/-! ### Sections of a finite coproduct -/

/-- **A section of a finite coproduct of `𝒪_X`-modules is a sum of images of sections of the
summands.**

The coproduct of sheaves of modules is formed by sheafification, so its sections over an open
are not the direct sum of the sections of the summands; but a coproduct indexed by a *finite*
type in an additive category is a biproduct, and the resulting splitting
`∑ₖ pₖ ≫ ιₖ = 𝟙` is an identity of morphisms, which may be read on sections over any open.
This is the same argument as
`Stacks.SheafOfModules.SiteFiniteTypeBridge.exists_eval_comb`, at an arbitrary colimit cofan
rather than at the free sheaf of modules. -/
public theorem exists_sum_app_of_cofanIsColimit {K : Type u} [Fintype K]
    {A : K → X.Modules} {T : X.Modules} (ι : ∀ k, A k ⟶ T)
    (hc : IsColimit (Cofan.mk T ι)) (U : X.Opensᵒᵖ) (y : T.val.obj U) :
    ∃ x : ∀ k, (A k).val.obj U, y = ∑ k : K, ((ι k).val.app U) (x k) := by
  classical
  set p : ∀ k, T ⟶ A k := fun k => Cofan.IsColimit.desc hc
    (fun l => if h : l = k then eqToHom (congrArg A h) else 0) with hp
  have hfac : ∀ j k : K, ι j ≫ p k =
      (if h : j = k then eqToHom (congrArg A h) else 0) := fun j k =>
    Cofan.IsColimit.fac hc (fun l => if h : l = k then eqToHom (congrArg A h) else 0) j
  have htot : (∑ k : K, p k ≫ ι k) = 𝟙 T := by
    refine Cofan.IsColimit.hom_ext hc _ _ fun j => ?_
    have hL : ι j ≫ (∑ k : K, p k ≫ ι k) = ι j := by
      rw [Preadditive.comp_sum]
      refine (Finset.sum_eq_single j (fun k _ hk => ?_) (fun hj => ?_)).trans ?_
      · rw [← Category.assoc, hfac, dite_eq_right (Ne.symm hk), zero_comp]
      · exact absurd (Finset.mem_univ j) hj
      · rw [← Category.assoc, hfac, dite_eq_left rfl]
        simp
    exact hL.trans (Category.comp_id _).symm
  refine ⟨fun k => (p k).val.app U y, ?_⟩
  have h := map_sum
    ({ toFun := fun f : T ⟶ T => f.val.app U y
       map_zero' := rfl
       map_add' := fun _ _ => rfl } : (T ⟶ T) →+ T.val.obj U)
    (fun k => p k ≫ ι k) Finset.univ
  rw [htot] at h
  exact h

/-! ### Finite direct sums -/

variable {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- **A finite direct sum of graded modules of finite type on affine opens is of finite type on
affine opens.**

The generators are the images of the generators of the summands under the coproduct injections,
which are homomorphisms of graded modules and so carry a product `s · a` to the product of the
image with `a`. That every section of the direct sum is a sum of images of sections of the
summands is `Stacks.Coherent.exists_sum_app_of_cofanIsColimit` applied to
`SheafOfModules.GradedModule.directSumPieceIsColimit`. -/
public theorem isFiniteTypeOnAffine_directSum [P.IsCommutative] {K : Type u} [Finite K]
    (M : K → SheafOfModules.GradedModule.{u, u, u} P)
    (h : ∀ k, IsFiniteTypeOnAffine (M k)) :
    IsFiniteTypeOnAffine (SheafOfModules.GradedModule.directSum M) := by
  classical
  have := Fintype.ofFinite K
  intro U
  choose G hG using fun k => h k U
  have hSfin : (⋃ k : K, (fun s : Σ d : ℤ, ((M k).piece d).val.obj (op U.1) =>
      (⟨s.1, ((SheafOfModules.GradedModule.directSumι M k).app s.1).val.app (op U.1) s.2⟩ :
        Σ n : ℤ,
          ((SheafOfModules.GradedModule.directSum M).piece n).val.obj (op U.1))) ''
      (↑(G k) : Set (Σ d : ℤ, ((M k).piece d).val.obj (op U.1)))).Finite :=
    Set.finite_iUnion fun k => Set.Finite.image _ (G k).finite_toSet
  refine ⟨hSfin.toFinset, fun n => top_unique fun y _ => ?_⟩
  obtain ⟨x, hx⟩ := exists_sum_app_of_cofanIsColimit
    (fun k => (SheafOfModules.GradedModule.directSumι M k).app n)
    (SheafOfModules.GradedModule.directSumPieceIsColimit M n) (op U.1) y
  rw [hx]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  have hsub : AddSubgroup.closure (generatedSet (M k) U (↑(G k)) n) ≤
      AddSubgroup.comap
        (ConcreteCategory.hom
            (((SheafOfModules.GradedModule.directSumι M k).app n).val.app
              (op U.1))).toAddMonoidHom
        (AddSubgroup.closure
          (generatedSet (SheafOfModules.GradedModule.directSum M) U
            (↑hSfin.toFinset) n)) := by
    rw [AddSubgroup.closure_le]
    rintro t ⟨s, hs, m, a, hh, rfl⟩
    subst hh
    refine AddSubgroup.subset_closure ⟨⟨s.1,
      ((SheafOfModules.GradedModule.directSumι M k).app s.1).val.app (op U.1) s.2⟩,
      hSfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨k, ⟨s, hs, rfl⟩⟩), m, a, rfl, ?_⟩
    exact (SheafOfModules.GradedModule.directSumι M k).map_smul s.1 m (op U.1) s.2 a
  exact hsub ((hG k n).ge (AddSubgroup.mem_top (x k)))

/-! ### Finite type on affine opens of the free graded module -/

/-- **The unit of `𝓟` read in the degree-`d` piece of `𝓟(-d)`**, which is `𝓟_{d-d}`. -/
public abbrev shiftedOne (P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (d : ℤ)
    (U : X.Opensᵒᵖ) : (P.piece (d + -d)).val.obj U :=
  SheafOfModules.castHom P.piece (show (0 : ℤ) = d + -d by omega) U (P.one.eval U)

/-- **Over an affine open the pure tensors of sections exhaust `F ⊗ 𝓟_{n-d}`.** The degree-`n`
piece of `F ⊗ 𝓟(-d)` is the sheafification of the sectionwise tensor product, and over an affine
open the sheafification unit is *surjective* on sections when both factors are quasi-coherent:
the comparison `Γ(F, U) ⊗ Γ(𝓟_{n-d}, U) → Γ(F ⊗ 𝓟_{n-d}, U)` is bijective by
`Stacks.SectionTensorFormula.bijective_tensorSectionLinear`, and it factors as the unit followed
by the identification `Stacks.SectionTensorFormula.tensorSheafIsoTensorObj` of the sheafified
sectionwise tensor product with the localized monoidal product. -/
public theorem surjective_freeGradedMk (F : X.Modules) [F.IsQuasicoherent] (d n : ℤ)
    (hP : (P.piece (n + -d)).IsQuasicoherent) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (freeGradedMk (P := P) F d n (op U)) := by
  have := hP
  intro y
  set e := Stacks.SectionTensorFormula.tensorSheafIsoTensorObj X.presheaf
    (isSheaf_structureRingPresheaf X) F (P.piece (n + -d))
  have hinv : ∀ a, e.inv.val.app (op U) (e.hom.val.app (op U) a) = a := fun a =>
    congrArg (fun φ : tensorModules X F (P.piece (n + -d)) ⟶ _ => φ.val.app (op U) a)
      e.hom_inv_id
  obtain ⟨t, ht⟩ := (Stacks.SectionTensorFormula.bijective_tensorSectionLinear F
    (P.piece (n + -d)) hU).2 (e.hom.val.app (op U) y)
  refine ⟨t, (hinv (freeGradedMk F d n (op U) t)).symm.trans ?_⟩
  exact ((congrArg (e.inv.val.app (op U)) ht).trans (hinv y))

/-- **Acting on the generator `g ⊗ 1` by a homogeneous section of `𝓟`.** The generator of
`F ⊗ 𝓟(-d)` attached to a section `g` of `F` sits in degree `d`, and acting on it by a section
`a` of `𝓟_i` gives the pure tensor `g ⊗ a` in degree `d + i`. Three transports are involved and
all three collapse: the unit is moved out of the first factor by
`SheafOfModules.Cofree.smul_castHom_left`, the two casts are merged by
`SheafOfModules.Cofree.castHom_castHom`, and the left unit law of `𝓟` is read through
`SheafOfModules.Cofree.castHom_eq_castHom`. -/
public theorem freeGradedMk_one_smul (F : X.Modules) (d i : ℤ) (U : X.Opensᵒᵖ)
    (g : F.val.obj U) (a : (P.piece i).val.obj U) :
    (freeGradedModuleOn F P d).smul d i U
        (freeGradedMk F d d U (g ⊗ₜ shiftedOne P d U)) a
      = freeGradedMk F d (d + i) U
        (g ⊗ₜ SheafOfModules.castHom P.piece (show i = d + i + -d by omega) U a) := by
  refine (SheafOfModules.GradedModule.tensorLeft_smul_tmul X.presheaf
    (isSheaf_structureRingPresheaf X) F (shiftedAlgebraModule P d) d i U g
    (shiftedOne P d U) a).trans ?_
  refine congrArg (fun z => freeGradedMk F d (d + i) U (g ⊗ₜ z)) ?_
  refine Eq.trans (congrArg (fun z => SheafOfModules.castHom P.piece
      (show d + -d + i = d + i + -d by omega) U z)
    (SheafOfModules.Cofree.smul_castHom_left (SheafOfModules.GradedModule.regularModule P)
      (show (0 : ℤ) = d + -d by omega) U (P.one.eval U) a)) ?_
  refine (SheafOfModules.Cofree.castHom_castHom P.piece _ _ U _).trans ?_
  exact SheafOfModules.Cofree.castHom_eq_castHom _ _ U (P.one_mul i U a)

/-- Membership of a pure tensor in the generated set of the free graded module: it is the
generator `g ⊗ 1` acted on by a homogeneous section of `𝓟`. -/
public theorem freeGradedMk_mem_generatedSet [P.IsCommutative] (F : X.Modules) (d m : ℤ)
    (U : X.affineOpens) (G : Set (Σ k : ℤ, ((freeGradedModuleOn F P d).piece k).val.obj (op U.1)))
    (g : F.val.obj (op U.1))
    (hg : (⟨d, freeGradedMk F d d (op U.1) (g ⊗ₜ shiftedOne P d (op U.1))⟩ :
      Σ k : ℤ, ((freeGradedModuleOn F P d).piece k).val.obj (op U.1)) ∈ G)
    (b : (P.piece (d + m + -d)).val.obj (op U.1)) :
    freeGradedMk F d (d + m) (op U.1) (g ⊗ₜ b) ∈
      generatedSet (freeGradedModuleOn F P d) U G (d + m) := by
  refine ⟨⟨d, freeGradedMk F d d (op U.1) (g ⊗ₜ shiftedOne P d (op U.1))⟩, hg, m,
    SheafOfModules.castHom P.piece (show d + m + -d = m by omega) (op U.1) b, rfl, ?_⟩
  refine Eq.symm ?_
  rw [freeGradedMk_one_smul]
  refine congrArg (fun z => freeGradedMk F d (d + m) (op U.1) (g ⊗ₜ z)) ?_
  exact (SheafOfModules.Cofree.castHom_castHom P.piece _ _ (op U.1) b).trans
    (SheafOfModules.castHom_rfl P.piece (op U.1) b)

/-- **The free graded module `F ⊗ 𝓟(-d)` is of finite type on affine opens**, for a
quasi-coherent `F` whose sections over each affine open form a finite module and a `𝓟` with
quasi-coherent pieces.

The generators over an affine open `U` are the elements `gᵢ ⊗ 1` of degree `d`, one for each
member of a finite generating family `gᵢ` of `Γ(F, U)` over `Γ(X, U)`. That they generate is the
composition of three statements:

* over an affine open every section of the degree-`n` piece is a *sum of pure tensors* `g ⊗ a` of
  sections, which is `Stacks.Coherent.surjective_freeGradedMk`;
* a pure tensor `g ⊗ a` with `g = ∑ᵢ cᵢ · gᵢ` is the sum of the pure tensors `gᵢ ⊗ (cᵢ · a)`, by
  `Stacks.Coherent.map_tmul_mem_of_sum_smul`, which is where the scalar crosses the tensor
  product; and
* each `gᵢ ⊗ b` is the generator `gᵢ ⊗ 1` acted on by a homogeneous section of `𝓟`, by
  `Stacks.Coherent.freeGradedMk_mem_generatedSet`.

The homogeneous degree `n` is written `d + m` throughout, so that the degree bookkeeping of the
action on the generator — which lands in `d + m` by construction — needs no transport. -/
public theorem isFiniteTypeOnAffine_freeGradedModuleOn [P.IsCommutative] (F : X.Modules)
    [F.IsQuasicoherent] (hP : ∀ m : ℤ, (P.piece m).IsQuasicoherent)
    (hF : ∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(F, U.1)) (d : ℤ) :
    IsFiniteTypeOnAffine (freeGradedModuleOn F P d) := by
  classical
  intro U
  obtain ⟨sgen, hsgen⟩ := (hF U).fg_top
  have hspan : ∀ z : Γ(F, U.1), ∃ c : Γ(F, U.1) → Γ(X, U.1), ∑ i ∈ sgen, c i • i = z := by
    intro z
    obtain ⟨c, -, hc⟩ :=
      Submodule.mem_span_finset.1 (hsgen ▸ Submodule.mem_top :
        z ∈ Submodule.span Γ(X, U.1) (↑sgen : Set Γ(F, U.1)))
    exact ⟨c, hc⟩
  obtain ⟨Gf, hGf⟩ :
      ∃ Gf : Finset (Σ k : ℤ, ((freeGradedModuleOn F P d).piece k).val.obj (op U.1)),
        ∀ g ∈ sgen, (⟨d, freeGradedMk F d d (op U.1) (g ⊗ₜ shiftedOne P d (op U.1))⟩ :
          Σ k : ℤ, ((freeGradedModuleOn F P d).piece k).val.obj (op U.1)) ∈ Gf :=
    ⟨sgen.image fun g => ⟨d, freeGradedMk F d d (op U.1) (g ⊗ₜ shiftedOne P d (op U.1))⟩,
      fun _ hg => Finset.mem_image_of_mem _ hg⟩
  refine ⟨Gf, fun n => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = d + m := ⟨n - d, by omega⟩
  refine top_unique ?_
  rintro y -
  obtain ⟨t, rfl⟩ := surjective_freeGradedMk F d (d + m) (hP (d + m + -d)) U.2 y
  induction t using TensorProduct.inductionOn with
  | tmul g a =>
    obtain ⟨c, hc⟩ := hspan g
    refine map_tmul_mem_of_sum_smul X.presheaf (isSheaf_structureRingPresheaf X) F
      (P.piece (d + m + -d)) (op U.1) (freeGradedMk F d (d + m) (op U.1)) _ sgen c g hc a
      fun i hi => ?_
    exact AddSubgroup.subset_closure
      (freeGradedMk_mem_generatedSet (P := P) F d m U (↑Gf) i (Finset.mem_coe.2 (hGf i hi)) _)
  | add x y hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy

end Stacks.Coherent

end
