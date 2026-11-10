module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Comparison

/-!
# The characterization of the determinant functor

Let `(R, 𝔪, κ)` be a local ring. A determinant theory is a functor from finite-length
`R`-modules with isomorphisms to one-dimensional `κ`-vector spaces with isomorphisms, endowed
with an isomorphism `γ_{K → L → M}` for every short exact sequence, whose restriction to modules
annihilated by `𝔪` is isomorphic to the usual determinant functor `V ↦ ⋀^{dim V} V` and which has
properties (1), (2) and (3) of Tag 02PA. The determinant of Tag 02P6 with its maps `γ` is one,
and every determinant theory is isomorphic to it by a unique isomorphism respecting all of this
structure.

## Main definitions

* `Module.FiniteLength.DeterminantTheory` is a determinant theory.
* `Module.FiniteLength.DeterminantTheory.canonical` is the determinant of Tag 02P6 with the
  maps `γ` of Tag 02PA, as a determinant theory.
* `Module.FiniteLength.DeterminantTheory.IsComparison` says that a family of isomorphisms
  between the values of two determinant theories respects their structure.

## Main results

* `Module.FiniteLength.DeterminantTheory.existsUnique_comparison` is Tag 02PB: every
  determinant theory admits a unique comparison with the canonical one.

## Implementation notes

A module annihilated by `𝔪` is a `κ`-vector space through `residueFieldModule`; this structure
is put in place locally wherever the usual determinant of such a module is used. The usual
determinant functor and the usual isomorphism of property (3) are stated through their values
on exterior products. Through the comparison of Tag 02P8 a determinant theory becomes a
`NormalizedDeterminantTheory`, for which the comparison is constructed and shown to be unique.

## References

* [Stacks Project, Tag 02PB](https://stacks.math.columbia.edu/tag/02PB)
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct
namespace Module.FiniteLength
universe u v w w'

/-- The residue-field module structure on an `R`-module annihilated by the maximal ideal. -/
abbrev residueFieldModule {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : M, r • x = 0) :
    Module (IsLocalRing.ResidueField R) M :=
  Module.IsTorsionBySet.module (I := IsLocalRing.maximalIdeal R) (by
    intro x a
    exact hM a a.2 x)

/-- The residue-field structure of a module annihilated by the maximal ideal is compatible
with its `R`-module structure. -/
lemma residueFieldModule_isScalarTower {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : M, r • x = 0) :
    letI := residueFieldModule hM
    IsScalarTower R (IsLocalRing.ResidueField R) M :=
  Module.IsTorsionBySet.isScalarTower _

/-- A finite-length module annihilated by the maximal ideal is finite-dimensional over the
residue field. -/
lemma residueFieldModule_finite {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : M, r • x = 0)
    (hfin : IsFiniteLength R M) :
    letI := residueFieldModule hM
    Module.Finite (IsLocalRing.ResidueField R) M := by
  let := residueFieldModule hM
  have := residueFieldModule_isScalarTower hM
  have : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  exact Module.Finite.of_restrictScalars_finite R (IsLocalRing.ResidueField R) M

/-- A determinant theory for a local ring `(R, 𝔪, κ)`: a functor from finite-length
`R`-modules with isomorphisms to one-dimensional `κ`-vector spaces with isomorphisms, with an
isomorphism `γ_{K → L → M}` for every short exact sequence, such that the restriction of the
functor to modules annihilated by `𝔪` is isomorphic to the usual determinant functor
`V ↦ ⋀^{dim V} V` of `κ`-vector spaces, and properties (1), (2) and (3) of Tag 02PA hold. -/
public structure DeterminantTheory (R : Type u) [CommRing R] [IsLocalRing R] where
  /-- The functor on finite-length modules and their isomorphisms. -/
  toFunctor : FiniteLengthModuleIso.{u, v} R ⥤
    OneDimensionalVectorSpaceIso.{u, w} (IsLocalRing.ResidueField R)
  /-- The map `γ_{K → L → M}` attached to a short exact sequence `0 → K → L → M → 0`. -/
  gamma {K L M : FiniteLengthModuleIso.{u, v} R}
      (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
      (hi : Function.Injective i) (hp : Function.Surjective p)
      (hip : Function.Exact i p) :
    (toFunctor.obj K).of.obj ⊗[IsLocalRing.ResidueField R]
      (toFunctor.obj M).of.obj →ₗ[IsLocalRing.ResidueField R]
      (toFunctor.obj L).of.obj
  /-- Each `γ_{K → L → M}` is an isomorphism. -/
  gamma_bijective {K L M : FiniteLengthModuleIso.{u, v} R}
      (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
      (hi : Function.Injective i) (hp : Function.Surjective p)
      (hip : Function.Exact i p) : Function.Bijective (gamma i p hi hp hip)
  /-- The isomorphism of the value on a module annihilated by `𝔪` with the top exterior power
  of that module over `κ`. -/
  residueComparison (M : FiniteLengthModuleIso.{u, v} R)
      (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ m : M.of.obj, r • m = 0) :
    letI := residueFieldModule hM
    (toFunctor.obj M).of.obj ≃ₗ[IsLocalRing.ResidueField R]
      ⋀[IsLocalRing.ResidueField R]^(Module.finrank (IsLocalRing.ResidueField R) M.of.obj)
        M.of.obj
  /-- The isomorphisms `residueComparison` form a natural isomorphism with the usual
  determinant functor, which sends `v₁ ∧ ⋯ ∧ vₙ` to `f v₁ ∧ ⋯ ∧ f vₙ`. -/
  residueComparison_natural {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N)
      (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ m : M.of.obj, r • m = 0)
      (hN : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ n : N.of.obj, r • n = 0) :
    letI := residueFieldModule hM
    letI := residueFieldModule hN
    ∃ h : Module.finrank (IsLocalRing.ResidueField R) N.of.obj =
        Module.finrank (IsLocalRing.ResidueField R) M.of.obj,
      ∀ e : Fin (Module.finrank (IsLocalRing.ResidueField R) M.of.obj) → M.of.obj,
        residueComparison N hN ((toFunctor.map f).iso.hom.hom.hom
          ((residueComparison M hM).symm
            (exteriorPower.ιMulti (IsLocalRing.ResidueField R) _ e))) =
        exteriorPower.ιMulti (IsLocalRing.ResidueField R) _
          (fun a ↦ f.iso.hom.hom.hom (e (Fin.cast h a)))
  /-- Property (3) of Tag 02PA: on a short exact sequence of `κ`-vector spaces, `γ` is the usual
  isomorphism `e₁ ∧ ⋯ ∧ eₖ ⊗ f̄₁ ∧ ⋯ ∧ f̄ₘ ↦ e₁ ∧ ⋯ ∧ eₖ ∧ f₁ ∧ ⋯ ∧ fₘ`, with `fⱼ` any lifts of
  the `f̄ⱼ`. -/
  gamma_vectorSpaces {K L M : FiniteLengthModuleIso.{u, v} R}
      (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
      (hi : Function.Injective i) (hp : Function.Surjective p)
      (hip : Function.Exact i p)
      (hK : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ k : K.of.obj, r • k = 0)
      (hL : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ l : L.of.obj, r • l = 0)
      (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ m : M.of.obj, r • m = 0) :
    letI := residueFieldModule hK
    letI := residueFieldModule hL
    letI := residueFieldModule hM
    ∃ hdim : Module.finrank (IsLocalRing.ResidueField R) L.of.obj =
        Module.finrank (IsLocalRing.ResidueField R) K.of.obj +
          Module.finrank (IsLocalRing.ResidueField R) M.of.obj,
      ∀ (e : Fin (Module.finrank (IsLocalRing.ResidueField R) K.of.obj) → K.of.obj)
        (fbar : Fin (Module.finrank (IsLocalRing.ResidueField R) M.of.obj) → M.of.obj)
        (f : Fin (Module.finrank (IsLocalRing.ResidueField R) M.of.obj) → L.of.obj),
        (∀ a, p (f a) = fbar a) →
          residueComparison L hL (gamma i p hi hp hip
            ((residueComparison K hK).symm
                (exteriorPower.ιMulti (IsLocalRing.ResidueField R) _ e) ⊗ₜ
              (residueComparison M hM).symm
                (exteriorPower.ιMulti (IsLocalRing.ResidueField R) _ fbar))) =
            exteriorPower.ιMulti (IsLocalRing.ResidueField R) _
              (fun a ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast hdim a))
  /-- Property (1) of Tag 02PA: `γ` is compatible with isomorphisms of short exact
  sequences. -/
  gamma_natural {K L M K' L' M' : FiniteLengthModuleIso.{u, v} R}
      (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
      (i' : K'.of.obj →ₗ[R] L'.of.obj) (p' : L'.of.obj →ₗ[R] M'.of.obj)
      (hi : Function.Injective i) (hp : Function.Surjective p)
      (hip : Function.Exact i p)
      (hi' : Function.Injective i') (hp' : Function.Surjective p')
      (hip' : Function.Exact i' p')
      (u : K ⟶ K') (v : L ⟶ L') (w : M ⟶ M')
      (hu : i'.comp u.iso.hom.hom.hom = v.iso.hom.hom.hom.comp i)
      (hw : p'.comp v.iso.hom.hom.hom = w.iso.hom.hom.hom.comp p) :
    (gamma i' p' hi' hp' hip').comp
      (TensorProduct.map (toFunctor.map u).iso.hom.hom.hom
        (toFunctor.map w).iso.hom.hom.hom) =
      (toFunctor.map v).iso.hom.hom.hom.comp (gamma i p hi hp hip)
  /-- Property (2) of Tag 02PA: for a commutative three-by-three diagram with exact rows and
  columns the two composites of the maps `γ` agree after interchanging the middle factors with
  the sign `(-1)^{cg}`, `c = length C` and `g = length G`. -/
  gamma_three_by_three
      {A B C D E F G H I : FiniteLengthModuleIso.{u, v} R}
      (iAB : A.of.obj →ₗ[R] B.of.obj) (pBC : B.of.obj →ₗ[R] C.of.obj)
      (iDE : D.of.obj →ₗ[R] E.of.obj) (pEF : E.of.obj →ₗ[R] F.of.obj)
      (iGH : G.of.obj →ₗ[R] H.of.obj) (pHI : H.of.obj →ₗ[R] I.of.obj)
      (iAD : A.of.obj →ₗ[R] D.of.obj) (iBE : B.of.obj →ₗ[R] E.of.obj)
      (iCF : C.of.obj →ₗ[R] F.of.obj) (pDG : D.of.obj →ₗ[R] G.of.obj)
      (pEH : E.of.obj →ₗ[R] H.of.obj) (pFI : F.of.obj →ₗ[R] I.of.obj)
      (hAB : Function.Injective iAB) (hBC : Function.Surjective pBC)
      (hexABC : Function.Exact iAB pBC)
      (hDE : Function.Injective iDE) (hEF : Function.Surjective pEF)
      (hexDEF : Function.Exact iDE pEF)
      (hGH : Function.Injective iGH) (hHI : Function.Surjective pHI)
      (hexGHI : Function.Exact iGH pHI)
      (hAD : Function.Injective iAD) (hDG : Function.Surjective pDG)
      (hexADG : Function.Exact iAD pDG)
      (hBE : Function.Injective iBE) (hEH : Function.Surjective pEH)
      (hexBEH : Function.Exact iBE pEH)
      (hCF : Function.Injective iCF) (hFI : Function.Surjective pFI)
      (hexCFI : Function.Exact iCF pFI)
      (commADEB : iDE.comp iAD = iBE.comp iAB)
      (commBEFC : pEF.comp iBE = iCF.comp pBC)
      (commDGEH : iGH.comp pDG = pEH.comp iDE)
      (commEHIF : pHI.comp pEH = pFI.comp pEF) :
    (gamma iBE pEH hBE hEH hexBEH).comp
      (TensorProduct.map (gamma iAB pBC hAB hBC hexABC)
        (gamma iGH pHI hGH hHI hexGHI)) =
    (gamma iDE pEF hDE hEF hexDEF).comp
      ((TensorProduct.map (gamma iAD pDG hAD hDG hexADG)
        (gamma iCF pFI hCF hFI hexCFI)).comp
        (signedTensorInterchange
          (IsLocalRing.ResidueField R)
          (toFunctor.obj A).of.obj (toFunctor.obj C).of.obj
          (toFunctor.obj G).of.obj (toFunctor.obj I).of.obj
          (moduleLength R C.of.obj) (moduleLength R G.of.obj)))

/-- On a module annihilated by the maximal ideal, the inverse of the comparison of Tag 02P8
sends the exterior product of a family to the symbol of that family. -/
private lemma exteriorPowerComparison_symm_ιMulti
    {R : Type u} [CommRing R] [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module (IsLocalRing.ResidueField R) M] [IsScalarTower R (IsLocalRing.ResidueField R) M]
    [Module.Finite (IsLocalRing.ResidueField R) M]
    (e : Fin (Module.finrank (IsLocalRing.ResidueField R) M) → M) :
    (determinantExteriorPowerComparison R M).equiv.symm
        (exteriorPower.ιMulti (IsLocalRing.ResidueField R) _ e) =
      symbol ⟨fun a ↦ e (Fin.cast (determinantExteriorPowerComparison R M).length_eq_finrank a),
        all_admissible R M _⟩ := by
  rw [LinearEquiv.symm_apply_eq, (determinantExteriorPowerComparison R M).equiv_symbol]
  congr 1

/-- The determinant of Tag 02P6 with the maps `γ` of Tag 02PA is a determinant theory: it is
the usual determinant on vector spaces over the residue field by Tag 02P8, and it has
properties (1), (2) and (3) of Tag 02PA. -/
public noncomputable def DeterminantTheory.canonical (R : Type u) [CommRing R] [IsLocalRing R] :
    DeterminantTheory.{u, v, max u v} R where
  toFunctor := (determinantFunctor.{u, v} R).toFunctor
  gamma {K L M} i p hi hp hip :=
    determinantExactSequenceMap i p hi hp hip K.of.property L.of.property M.of.property
  gamma_bijective {K L M} i p hi hp hip :=
    determinantExactSequenceMap_bijective i p hi hp hip K.of.property L.of.property
      M.of.property
  residueComparison M hM :=
    letI := residueFieldModule hM
    haveI := residueFieldModule_isScalarTower hM
    haveI := residueFieldModule_finite hM M.of.property
    (determinantExteriorPowerComparison R M.of.obj).equiv
  residueComparison_natural {M N} f hM hN := by
    let := residueFieldModule hM
    have := residueFieldModule_isScalarTower hM
    have := residueFieldModule_finite hM M.of.property
    let := residueFieldModule hN
    have := residueFieldModule_isScalarTower hN
    have := residueFieldModule_finite hN N.of.property
    let cM := determinantExteriorPowerComparison R M.of.obj
    let cN := determinantExteriorPowerComparison R N.of.obj
    refine ⟨cN.length_eq_finrank.symm.trans
      (((determinantFunctor.{u, v} R).map_length f).symm.trans cM.length_eq_finrank), ?_⟩
    intro e
    change cN.equiv ((determinantFunctor.{u, v} R).mapLinearEquiv f (cM.equiv.symm
      (exteriorPower.ιMulti (IsLocalRing.ResidueField R) _ e))) = _
    rw [exteriorPowerComparison_symm_ιMulti, (determinantFunctor.{u, v} R).map_symbol,
      cN.equiv_symbol]
    congr 1
  gamma_vectorSpaces {K L M} i p hi hp hip hK hL hM := by
    let := residueFieldModule hK
    have := residueFieldModule_isScalarTower hK
    have := residueFieldModule_finite hK K.of.property
    let := residueFieldModule hL
    have := residueFieldModule_isScalarTower hL
    have := residueFieldModule_finite hL L.of.property
    let := residueFieldModule hM
    have := residueFieldModule_isScalarTower hM
    have := residueFieldModule_finite hM M.of.property
    exact determinantExactSequenceMap_comparison_apply
      (i.extendScalarsOfSurjective IsLocalRing.residue_surjective)
      (p.extendScalarsOfSurjective IsLocalRing.residue_surjective) hi hp hip
      K.of.property L.of.property M.of.property
  gamma_natural := determinantExactSequenceMap_natural
  gamma_three_by_three {A B C D E F G H I} iAB pBC iDE pEF iGH pHI iAD iBE iCF pDG pEH pFI
      hAB hBC hexABC hDE hEF hexDEF hGH hHI hexGHI hAD hDG hexADG hBE hEH hexBEH
      hCF hFI hexCFI commADEB commBEFC commDGEH commEHIF :=
    determinantExactSequenceMap_three_by_three iAB pBC iDE pEF iGH pHI iAD iBE iCF pDG pEH pFI
      hAB hBC hexABC hDE hEF hexDEF hGH hHI hexGHI hAD hDG hexADG hBE hEH hexBEH
      hCF hFI hexCFI commADEB commBEFC commDGEH commEHIF A.of.property B.of.property
      C.of.property D.of.property E.of.property F.of.property G.of.property H.of.property
      I.of.property

/-- A comparison between two determinant theories: isomorphisms between their values that are
natural, compatible with the maps `γ`, and compatible with the two identifications with the
usual determinant on modules annihilated by the maximal ideal. -/
public def DeterminantTheory.IsComparison {R : Type u} [CommRing R] [IsLocalRing R]
    (D : DeterminantTheory.{u, v, w} R) (D' : DeterminantTheory.{u, v, w'} R)
    (η : ∀ M : FiniteLengthModuleIso.{u, v} R,
      (D.toFunctor.obj M).of.obj ≃ₗ[IsLocalRing.ResidueField R] (D'.toFunctor.obj M).of.obj) :
    Prop :=
  (∀ {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N),
    (η N).toLinearMap.comp (D.toFunctor.map f).iso.hom.hom.hom =
      (D'.toFunctor.map f).iso.hom.hom.hom.comp (η M).toLinearMap) ∧
  (∀ {K L M : FiniteLengthModuleIso.{u, v} R}
      (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
      (hi : Function.Injective i) (hp : Function.Surjective p)
      (hip : Function.Exact i p),
    (η L).toLinearMap.comp (D.gamma i p hi hp hip) =
      (D'.gamma i p hi hp hip).comp
        (TensorProduct.map (η K).toLinearMap (η M).toLinearMap)) ∧
  (∀ (M : FiniteLengthModuleIso.{u, v} R)
      (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ m : M.of.obj, r • m = 0),
    letI := residueFieldModule hM
    (η M).trans (D'.residueComparison M hM) = D.residueComparison M hM)

/-- On a module annihilated by the maximal ideal, the isomorphism between the values of two
determinant theories obtained from their identifications with the top exterior power. -/
private noncomputable def residueTransfer {R : Type u} [CommRing R] [IsLocalRing R]
    (D : DeterminantTheory.{u, v, w} R) (D' : DeterminantTheory.{u, v, w'} R)
    (M : FiniteLengthModuleIso.{u, v} R)
    (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ m : M.of.obj, r • m = 0) :
    (D.toFunctor.obj M).of.obj ≃ₗ[IsLocalRing.ResidueField R] (D'.toFunctor.obj M).of.obj :=
  letI := residueFieldModule hM
  (D.residueComparison M hM).trans (D'.residueComparison M hM).symm

/-- Two linear maps out of a tensor product of exterior powers agree as soon as they agree on
tensor products of exterior products. -/
private lemma tensor_exteriorPower_ext {k : Type*} [Field k]
    {V W X : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup X] [Module k X] {n m : ℕ}
    (Φ Ψ : ⋀[k]^n V ⊗[k] ⋀[k]^m W →ₗ[k] X)
    (h : ∀ (e : Fin n → V) (f : Fin m → W),
      Φ (exteriorPower.ιMulti k n e ⊗ₜ exteriorPower.ιMulti k m f) =
        Ψ (exteriorPower.ιMulti k n e ⊗ₜ exteriorPower.ιMulti k m f)) :
    Φ = Ψ := by
  refine TensorProduct.ext' fun x y ↦ ?_
  have hx : x ∈ Submodule.span k (Set.range (exteriorPower.ιMulti k n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  have hy : y ∈ Submodule.span k (Set.range (exteriorPower.ιMulti k m)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, rfl⟩ := hy
      exact h e f
    | zero => simp
    | add y y' _ _ hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | smul c y _ hy => simp only [TensorProduct.tmul_smul, map_smul, hy]
  | zero => simp
  | add x x' _ _ hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  | smul c x _ hx => simp only [← TensorProduct.smul_tmul', map_smul, hx]

/-- The transfer between two determinant theories is natural on modules annihilated by the
maximal ideal, because both identifications with the top exterior power are. -/
private lemma residueTransfer_natural {R : Type u} [CommRing R] [IsLocalRing R]
    (D : DeterminantTheory.{u, v, w} R) (D' : DeterminantTheory.{u, v, w'} R)
    {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N)
    (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ m : M.of.obj, r • m = 0)
    (hN : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ n : N.of.obj, r • n = 0) :
    (residueTransfer D D' N hN).toLinearMap.comp (D.toFunctor.map f).iso.hom.hom.hom =
      (D'.toFunctor.map f).iso.hom.hom.hom.comp (residueTransfer D D' M hM).toLinearMap := by
  let := residueFieldModule hM
  let := residueFieldModule hN
  obtain ⟨h, hD⟩ := D.residueComparison_natural f hM hN
  obtain ⟨h', hD'⟩ := D'.residueComparison_natural f hM hN
  let ρM := D.residueComparison M hM
  refine (LinearMap.cancel_right (g := ρM.symm.toLinearMap) ρM.symm.surjective).mp ?_
  apply exteriorPower.linearMap_ext
  ext e
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, residueTransfer, LinearEquiv.trans_apply, ρM,
    LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.symm_apply_eq, hD, ← hD' e]

/-- The transfer between two determinant theories is compatible with the maps `γ` of a short
exact sequence of modules annihilated by the maximal ideal, because both theories have
property (3) of Tag 02PA. -/
private lemma residueTransfer_gamma {R : Type u} [CommRing R] [IsLocalRing R]
    (D : DeterminantTheory.{u, v, w} R) (D' : DeterminantTheory.{u, v, w'} R)
    {K L M : FiniteLengthModuleIso.{u, v} R}
    (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (hK : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ k : K.of.obj, r • k = 0)
    (hL : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ l : L.of.obj, r • l = 0)
    (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ m : M.of.obj, r • m = 0) :
    (residueTransfer D D' L hL).toLinearMap.comp (D.gamma i p hi hp hip) =
      (D'.gamma i p hi hp hip).comp
        (TensorProduct.map (residueTransfer D D' K hK).toLinearMap
          (residueTransfer D D' M hM).toLinearMap) := by
  let := residueFieldModule hK
  let := residueFieldModule hL
  let := residueFieldModule hM
  obtain ⟨hdim, hD⟩ := D.gamma_vectorSpaces i p hi hp hip hK hL hM
  obtain ⟨hdim', hD'⟩ := D'.gamma_vectorSpaces i p hi hp hip hK hL hM
  let ρK := D.residueComparison K hK
  let ρM := D.residueComparison M hM
  refine (LinearMap.cancel_right (g := TensorProduct.map ρK.symm.toLinearMap ρM.symm.toLinearMap)
    (TensorProduct.congr ρK.symm ρM.symm).surjective).mp ?_
  apply tensor_exteriorPower_ext
  intro e fbar
  choose f hf using fun a ↦ hp (fbar a)
  simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, residueTransfer, LinearEquiv.trans_apply, ρK, ρM,
    LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.symm_apply_eq, hD e fbar f hf, ← hD' e fbar f hf]

/-- A determinant theory, with its identification with the usual determinant on modules
annihilated by the maximal ideal replaced by the identification with the determinant of
Tag 02P6 that it induces through Tag 02P8. -/
private noncomputable def DeterminantTheory.toNormalized {R : Type u} [CommRing R]
    [IsLocalRing R] (D : DeterminantTheory.{u, v, w} R) :
    NormalizedDeterminantTheory.{u, v, w} R where
  toFunctor := D.toFunctor
  gamma := D.gamma
  gamma_bijective := D.gamma_bijective
  residueComparison M hM := residueTransfer D (DeterminantTheory.canonical R) M hM
  residueComparison_natural f hM hN :=
    residueTransfer_natural D (DeterminantTheory.canonical R) f hM hN
  residueComparison_gamma i p hi hp hip hK hL hM :=
    residueTransfer_gamma D (DeterminantTheory.canonical R) i p hi hp hip hK hL hM
  gamma_natural := D.gamma_natural
  gamma_three_by_three := D.gamma_three_by_three

/-- **Stacks Project, Tag 02PB.** The determinant functor of finite-length modules over a
local ring, endowed with the maps `γ_{K → L → M}`, is characterized by its properties: every
determinant theory, that is, every functor with maps `γ` whose restriction to modules
annihilated by the maximal ideal is isomorphic to the usual determinant functor and which has
properties (1), (2) and (3) of Tag 02PA, is isomorphic to the canonical one by a unique
isomorphism compatible with all of this structure. -/
@[stacks 02PB]
public theorem DeterminantTheory.existsUnique_comparison {R : Type u} [CommRing R]
    [IsLocalRing R] (D : DeterminantTheory.{u, v, w} R) :
    ∃! η : ∀ M : FiniteLengthModuleIso.{u, v} R,
      (D.toFunctor.obj M).of.obj ≃ₗ[IsLocalRing.ResidueField R]
        ((DeterminantTheory.canonical R).toFunctor.obj M).of.obj,
      D.IsComparison (DeterminantTheory.canonical R) η := by
  have hiff : ∀ η, IsDeterminantComparison D.toNormalized η ↔
      D.IsComparison (DeterminantTheory.canonical R) η := by
    intro η
    refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun M ↦ forall_congr' fun hM ↦ ?_))
    let := residueFieldModule hM
    change η M = (D.residueComparison M hM).trans
        ((DeterminantTheory.canonical R).residueComparison M hM).symm ↔
      (η M).trans ((DeterminantTheory.canonical R).residueComparison M hM) =
        D.residueComparison M hM
    constructor
    · intro h
      rw [h]
      refine LinearEquiv.ext fun x ↦ ?_
      exact ((DeterminantTheory.canonical R).residueComparison M hM).apply_symm_apply
        (D.residueComparison M hM x)
    · intro h
      rw [← h]
      refine LinearEquiv.ext fun x ↦ ?_
      exact (((DeterminantTheory.canonical R).residueComparison M hM).symm_apply_apply
        (η M x)).symm
  obtain ⟨η, hη, huniq⟩ := existsUnique_normalizedComparison D.toNormalized
  exact ⟨η, (hiff η).mp hη, fun η' hη' ↦ huniq η' ((hiff η').mpr hη')⟩

end Module.FiniteLength

end
