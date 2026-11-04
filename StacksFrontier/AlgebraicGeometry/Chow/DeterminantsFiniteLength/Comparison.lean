module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.GammaIsomorphism
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.GammaNatural
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.GammaThreeByThree
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.GammaVectorSpaces

/-!
# Comparison of a determinant theory with the determinant construction

A normalized determinant theory for a local ring `R` is a functor on the groupoid of
finite-length `R`-modules together with exact-sequence maps, identified with the determinant
of Tag 02P6 on modules annihilated by the maximal ideal, and compatible with isomorphisms of
short exact sequences and with three-by-three diagrams. It admits a unique comparison with the
determinant construction extending that identification.

## Main definitions

* `Module.FiniteLength.NormalizedDeterminantTheory` is a functor together with its
  exact-sequence maps, its identification with the determinant on modules annihilated by the
  maximal ideal, and the axioms they obey.
* `Module.FiniteLength.IsDeterminantComparison` is the defining rule for a comparison
  between a normalized determinant theory and the determinant of Tag 02P6.

## Main results

* `Module.FiniteLength.existsUnique_normalizedComparison` states that a normalized
  determinant theory admits a unique comparison with the determinant construction.

## Implementation notes

The comparison is produced by induction on length. On a module killed by the maximal ideal
it is the normalization axiom. In general a nonzero element of the socle gives a short exact
sequence whose outer terms have smaller length, and the exact-sequence axiom transports the
comparison across it; the three-by-three axiom is what makes the result independent of the
chosen socle element, and naturality is what makes it independent of the module's
presentation.

`ShortExact` here is a short exact sequence of *objects of the groupoid* of finite-length
modules, so it is not the short exact sequence of plain modules that the flatness library
defines; it is `private` to this module for that reason.

## References

* [Stacks Project, Tag 02PB](https://stacks.math.columbia.edu/tag/02PB)
-/
@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct
namespace Module.FiniteLength
universe u v w

/-- A finite-length module as an object of the groupoid of finite-length modules. -/
private abbrev finiteLengthObject
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) : FiniteLengthModuleIso.{u, v} R :=
  ⟨⟨ModuleCat.of R M, hM⟩⟩

/-- A submodule of a finite-length module as an object of the groupoid. -/
private abbrev finiteLengthSubmoduleObject
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (S : Submodule R M) : FiniteLengthModuleIso.{u, v} R :=
  finiteLengthObject (hM.of_injective S.subtype_injective)

/-- A quotient of a finite-length module as an object of the groupoid. -/
private abbrev finiteLengthQuotientObject
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (S : Submodule R M) : FiniteLengthModuleIso.{u, v} R :=
  finiteLengthObject (hM.of_surjective S.mkQ_surjective)

/-- The socle in the sense used here: the submodule killed by the maximal ideal. -/
private abbrev socleSubmodule
    (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : Submodule R M :=
  Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R)

/-- The maximal ideal annihilates the socle. -/
private lemma socleSubmodule_annihilated
    {R : Type u} [CommRing R] [IsLocalRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R)
    {x : M} (hx : x ∈ socleSubmodule R M) : r • x = 0 :=
  (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨r, hr⟩

/-- A nontrivial module of finite length contains a simple submodule, since its submodule
lattice is then artinian and hence atomic. -/
private lemma exists_simple_submodule_of_finiteLength
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) [Nontrivial M] :
    ∃ S : Submodule R M, IsSimpleModule R S := by
  have : IsArtinian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  simpa only [isSimpleModule_iff_isAtom] using IsAtomic.exists_atom (Submodule R M)

/-- The socle of a nontrivial finite-length module is nonzero. -/
private lemma socleSubmodule_ne_bot_of_finiteLength
    {R : Type u} [CommRing R] [IsLocalRing R] {M : Type v}
    [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) [Nontrivial M] : socleSubmodule R M ≠ ⊥ := by
  classical
  obtain ⟨S, hS⟩ := exists_simple_submodule_of_finiteLength hM
  have : Nontrivial S := not_subsingleton_iff_nontrivial.mp fun h =>
    (isSimpleModule_iff_isAtom.mp hS).1 (Submodule.subsingleton_iff_eq_bot.mp h)
  obtain ⟨x, hx⟩ := exists_ne (0 : S)
  intro hbot
  have hmem : (x : M) ∈ socleSubmodule R M := (Submodule.mem_torsionBySet_iff _ _).mpr
    fun r => congrArg Subtype.val (maximalIdeal_smul_eq_zero_of_simple r.property x)
  rw [hbot] at hmem
  exact hx (Submodule.coe_eq_zero.mp ((Submodule.mem_bot R).mp hmem))

/-- A functor from finite-length modules to one-dimensional vector spaces with exact-sequence
maps, identified with the determinant of Tag 02P6 on modules annihilated by the maximal ideal,
compatible with that identification on short exact sequences of such modules, with
isomorphisms of short exact sequences, and with three-by-three diagrams. -/
public structure NormalizedDeterminantTheory (R : Type u) [CommRing R] [IsLocalRing R] where
  toFunctor : FiniteLengthModuleIso.{u, v} R ⥤
    OneDimensionalVectorSpaceIso.{u, w} (IsLocalRing.ResidueField R)
  gamma {K L M : FiniteLengthModuleIso.{u, v} R}
      (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
      (hi : Function.Injective i) (hp : Function.Surjective p)
      (hip : Function.Exact i p) :
    (toFunctor.obj K).of.obj ⊗[IsLocalRing.ResidueField R]
      (toFunctor.obj M).of.obj →ₗ[IsLocalRing.ResidueField R]
      (toFunctor.obj L).of.obj
  gamma_bijective {K L M : FiniteLengthModuleIso.{u, v} R}
      (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
      (hi : Function.Injective i) (hp : Function.Surjective p)
      (hip : Function.Exact i p) : Function.Bijective (gamma i p hi hp hip)
  /-- The prescribed comparison on the subcategory of modules annihilated by
  the maximal ideal. -/
  residueComparison (M : FiniteLengthModuleIso.{u, v} R)
      (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ m : M.of.obj, r • m = 0) :
    (toFunctor.obj M).of.obj ≃ₗ[IsLocalRing.ResidueField R]
      determinant R M.of.obj
  residueComparison_natural {M N : FiniteLengthModuleIso.{u, v} R}
      (f : M ⟶ N)
      (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ m : M.of.obj, r • m = 0)
      (hN : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ n : N.of.obj, r • n = 0) :
    (residueComparison N hN).toLinearMap.comp
      (toFunctor.map f).iso.hom.hom.hom =
    ((determinantFunctor R).mapLinearEquiv f).toLinearMap.comp
      (residueComparison M hM).toLinearMap
  residueComparison_gamma {K L M : FiniteLengthModuleIso.{u, v} R}
      (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
      (hi : Function.Injective i) (hp : Function.Surjective p)
      (hip : Function.Exact i p)
      (hK : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ k : K.of.obj, r • k = 0)
      (hL : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ l : L.of.obj, r • l = 0)
      (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ m : M.of.obj, r • m = 0) :
    (residueComparison L hL).toLinearMap.comp (gamma i p hi hp hip) =
      (determinantExactSequenceMap i p hi hp hip
        K.of.property L.of.property M.of.property).comp
        (TensorProduct.map (residueComparison K hK).toLinearMap
          (residueComparison M hM).toLinearMap)
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

/-- A comparison of a normalized determinant theory with the determinant construction,
preserving isomorphisms, exact-sequence maps, and its fixed normalization. -/
public def IsDeterminantComparison {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R)
    (η : ∀ M : FiniteLengthModuleIso.{u, v} R,
      (D.toFunctor.obj M).of.obj ≃ₗ[IsLocalRing.ResidueField R]
        determinant R M.of.obj) : Prop :=
  (∀ {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N),
    (η N).toLinearMap.comp (D.toFunctor.map f).iso.hom.hom.hom =
      ((determinantFunctor R).mapLinearEquiv f).toLinearMap.comp
        (η M).toLinearMap) ∧
  (∀ {K L M : FiniteLengthModuleIso.{u, v} R}
      (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
      (hi : Function.Injective i) (hp : Function.Surjective p)
      (hip : Function.Exact i p),
    (η L).toLinearMap.comp (D.gamma i p hi hp hip) =
      (determinantExactSequenceMap i p hi hp hip
        K.of.property L.of.property M.of.property).comp
        (TensorProduct.map (η K).toLinearMap (η M).toLinearMap)) ∧
  (∀ (M : FiniteLengthModuleIso.{u, v} R)
      (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ m : M.of.obj, r • m = 0),
    η M = D.residueComparison M hM)

/-- The exact-sequence map of a determinant theory, read as an equivalence between the tensor
product of the outer values and the middle value. -/
private noncomputable def theoryGammaEquiv
    {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R)
    {K L M : FiniteLengthModuleIso.{u, v} R}
    (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p) :
    (D.toFunctor.obj K).of.obj ⊗[IsLocalRing.ResidueField R]
        (D.toFunctor.obj M).of.obj ≃ₗ[IsLocalRing.ResidueField R]
      (D.toFunctor.obj L).of.obj :=
  LinearEquiv.ofBijective (D.gamma i p hi hp hip)
    (D.gamma_bijective i p hi hp hip)

/-- The exact-sequence map of the determinant construction, read as an equivalence. -/
private noncomputable def canonicalGammaEquiv
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K L M : Type v} [AddCommGroup K] [Module R K]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (hK : IsFiniteLength R K) (hL : IsFiniteLength R L) (hM : IsFiniteLength R M) :
    determinant R K ⊗[IsLocalRing.ResidueField R] determinant R M ≃ₗ[IsLocalRing.ResidueField R]
      determinant R L :=
  LinearEquiv.ofBijective _ (determinantExactSequenceMap_bijective i p hi hp hip hK hL hM)

/-- Transport a comparison across a short exact sequence: given comparisons on the outer
terms, the exact-sequence axioms determine one on the middle term. -/
private noncomputable def extendComparisonAcrossExact
    {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R)
    {K L M : FiniteLengthModuleIso.{u, v} R}
    (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (hK : IsFiniteLength R K.of.obj) (hL : IsFiniteLength R L.of.obj)
    (hM : IsFiniteLength R M.of.obj)
    (ηK : (D.toFunctor.obj K).of.obj ≃ₗ[IsLocalRing.ResidueField R]
      determinant R K.of.obj)
    (ηM : (D.toFunctor.obj M).of.obj ≃ₗ[IsLocalRing.ResidueField R]
      determinant R M.of.obj) :
    (D.toFunctor.obj L).of.obj ≃ₗ[IsLocalRing.ResidueField R]
      determinant R L.of.obj :=
  ((theoryGammaEquiv D i p hi hp hip).symm).trans
    ((TensorProduct.congr ηK ηM).trans
      (canonicalGammaEquiv i p hi hp hip hK hL hM))

/-- `extendComparisonAcrossExact` is compatible with the two exact-sequence maps. -/
private theorem extendComparisonAcrossExact_spec
    {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R)
    {K L M : FiniteLengthModuleIso.{u, v} R}
    (i : K.of.obj →ₗ[R] L.of.obj) (p : L.of.obj →ₗ[R] M.of.obj)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (hK : IsFiniteLength R K.of.obj) (hL : IsFiniteLength R L.of.obj)
    (hM : IsFiniteLength R M.of.obj)
    (ηK : (D.toFunctor.obj K).of.obj ≃ₗ[IsLocalRing.ResidueField R]
      determinant R K.of.obj)
    (ηM : (D.toFunctor.obj M).of.obj ≃ₗ[IsLocalRing.ResidueField R]
      determinant R M.of.obj) :
    (extendComparisonAcrossExact D i p hi hp hip hK hL hM ηK ηM).toLinearMap.comp
        (D.gamma i p hi hp hip) =
      (determinantExactSequenceMap i p hi hp hip hK hL hM).comp
        (TensorProduct.map ηK.toLinearMap ηM.toLinearMap) := by
  ext z
  simp [extendComparisonAcrossExact, theoryGammaEquiv, canonicalGammaEquiv]

/-- In a short exact sequence whose first term is nontrivial, the last term is shorter than
the middle one. -/
private lemma moduleLength_lt_of_exact {R : Type u} [CommRing R]
    {K L M : Type v} [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M] (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K) (hM : IsFiniteLength R M) [Nontrivial K] :
    moduleLength R M < moduleLength R L := by
  have hlen := Module.length_eq_add_of_exact i p hi hp hip
  have hnat : moduleLength R L = moduleLength R K + moduleLength R M := by
    unfold moduleLength
    rw [hlen, ENat.toNat_add (Module.length_ne_top_iff.mpr hK)
      (Module.length_ne_top_iff.mpr hM)]
  have hpos : 0 < moduleLength R K := by
    have hcast : (moduleLength R K : ℕ∞) = Module.length R K :=
      ENat.natCast_toNat (Module.length_ne_top_iff.mpr hK)
    exact_mod_cast (hcast ▸ Module.length_pos_iff.mpr ‹Nontrivial K›)
  omega

/-- Dividing out a nonzero submodule strictly decreases the length. -/
private lemma quotient_length_lt {R : Type u} [CommRing R]
    (L : FiniteLengthModuleIso.{u, v} R) (S : Submodule R L.of.obj) (hS : S ≠ ⊥) :
    moduleLength R (L.of.obj ⧸ S) < moduleLength R L.of.obj :=
  have : Nontrivial S := not_subsingleton_iff_nontrivial.mp
    (fun h => hS (Submodule.subsingleton_iff_eq_bot.mp h))
  moduleLength_lt_of_exact S.subtype S.mkQ S.subtype_injective S.mkQ_surjective
    (LinearMap.exact_iff.mpr (by simp)) (L.of.property.of_injective S.subtype_injective)
    (L.of.property.of_surjective S.mkQ_surjective)

/-- A module not annihilated by the maximal ideal is nontrivial. -/
private lemma nontrivial_of_not_annihilated {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (h : ¬ ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : M, r • x = 0) : Nontrivial M := by
  by_contra hn
  have := not_nontrivial_iff_subsingleton.mp hn
  exact h fun r _ x => by simp [Subsingleton.elim x 0]

/-- The maximal ideal annihilates the socle, as a module in its own right. -/
private lemma socle_killed {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] :
    ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : socleSubmodule R M, r • x = 0 :=
  fun r hr x => Subtype.ext (socleSubmodule_annihilated r hr x.property)

/-- A module surjected onto by a module killed by the maximal ideal is also killed by it. -/
private lemma killed_of_surjective {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N} (hf : Function.Surjective f)
    (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : M, r • x = 0) :
    ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : N, r • x = 0 := by
  intro r hr x
  obtain ⟨x, rfl⟩ := hf x
  rw [← map_smul, hM r hr, map_zero]

/-- The quotient by the socle of a module not killed by the maximal ideal is shorter. -/
private lemma socle_quotient_length_lt {R : Type u} [CommRing R] [IsLocalRing R]
    (L : FiniteLengthModuleIso.{u, v} R)
    (hL : ¬ ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : L.of.obj, r • x = 0) :
    moduleLength R (L.of.obj ⧸ socleSubmodule R L.of.obj) < moduleLength R L.of.obj :=
  have : Nontrivial L.of.obj := nontrivial_of_not_annihilated hL
  quotient_length_lt L _ (socleSubmodule_ne_bot_of_finiteLength L.of.property)

/-- The comparison at a single module, built by induction on its length: on a module killed
by the maximal ideal it is the normalization axiom, and otherwise it is transported across
the short exact sequence given by the socle. -/
private noncomputable def pointwiseComparison
    {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R) :
    ∀ {M : Type v} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M),
      (D.toFunctor.obj (finiteLengthObject hM)).of.obj ≃ₗ[IsLocalRing.ResidueField R]
        determinant R M := by
  intro M _ _ hM
  classical
  by_cases hkill : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : M, r • x = 0
  · exact D.residueComparison (finiteLengthObject hM) hkill
  · let S := socleSubmodule R M
    have hQ : IsFiniteLength R (M ⧸ S) := hM.of_surjective S.mkQ_surjective
    exact extendComparisonAcrossExact D S.subtype S.mkQ S.subtype_injective
      S.mkQ_surjective (LinearMap.exact_iff.mpr (by simp))
      (hM.of_injective S.subtype_injective) hM hQ
      (D.residueComparison (finiteLengthSubmoduleObject hM S) socle_killed)
      (pointwiseComparison D hQ)
termination_by M _ _ _hM => moduleLength R M
decreasing_by
  classical
  have : Nontrivial M := nontrivial_of_not_annihilated
    ‹¬ (∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : M, r • x = 0)›
  exact quotient_length_lt (finiteLengthObject hM) _ (socleSubmodule_ne_bot_of_finiteLength hM)

/-- On a module killed by the maximal ideal, `pointwiseComparison` is the normalization
axiom. -/
private theorem pointwiseComparison_on_killed
    {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R)
    {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M)
    (hkill : ∀ r ∈ IsLocalRing.maximalIdeal R,
      ∀ x : (finiteLengthObject hM).of.obj, r • x = 0) :
    pointwiseComparison D hM = D.residueComparison (finiteLengthObject hM) hkill := by
  classical
  rw [pointwiseComparison, dite_eq_left hkill]

/-- The type of a comparison at one object: an equivalence between the value of the
determinant theory and the determinant of Tag 02P6. -/
private abbrev Comparison {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R) (M : FiniteLengthModuleIso.{u, v} R) :=
  (D.toFunctor.obj M).of.obj ≃ₗ[IsLocalRing.ResidueField R] determinant R M.of.obj

/-- The comparison at one object of the groupoid. -/
private abbrev comparison {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R) (M : FiniteLengthModuleIso.{u, v} R) :
    Comparison D M := pointwiseComparison D M.of.property

/-- On a module killed by the maximal ideal, the comparison is the normalization axiom. -/
private lemma comparison_eq_residueComparison {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R) (M : FiniteLengthModuleIso.{u, v} R)
    (hM : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : M.of.obj, r • x = 0) :
    comparison D M = D.residueComparison M hM :=
  pointwiseComparison_on_killed D _ hM

/-- A short exact sequence of objects of the groupoid of finite-length modules. This is not
the short exact sequence of plain modules of the flatness library: its maps go between the
underlying modules of groupoid objects. -/
private structure ShortExact {R : Type u} [CommRing R]
    (K L M : FiniteLengthModuleIso.{u, v} R) where
  i : K.of.obj →ₗ[R] L.of.obj
  p : L.of.obj →ₗ[R] M.of.obj
  hi : Function.Injective i
  hp : Function.Surjective p
  exact : Function.Exact i p

/-- The exact-sequence map of the determinant construction attached to a short exact
sequence. -/
private abbrev ShortExact.gamma {R : Type u} [CommRing R] [IsLocalRing R]
    {K L M : FiniteLengthModuleIso.{u, v} R} (s : ShortExact K L M) :=
  determinantExactSequenceMap s.i s.p s.hi s.hp s.exact
    K.of.property L.of.property M.of.property

/-- The exact-sequence map of a determinant theory attached to a short exact sequence. -/
private abbrev ShortExact.gammaD {R : Type u} [CommRing R] [IsLocalRing R]
    {K L M : FiniteLengthModuleIso.{u, v} R} (s : ShortExact K L M)
    (D : NormalizedDeterminantTheory.{u, v, w} R) := D.gamma s.i s.p s.hi s.hp s.exact

/-- Compatibility of three comparisons with the two exact-sequence maps of a short exact
sequence. -/
private def ShortExact.Compatible {R : Type u} [CommRing R] [IsLocalRing R]
    {K L M : FiniteLengthModuleIso.{u, v} R} (s : ShortExact K L M)
    {D : NormalizedDeterminantTheory.{u, v, w} R}
    (a : Comparison D K) (b : Comparison D L) (c : Comparison D M) : Prop :=
  b.toLinearMap.comp (s.gammaD D) = s.gamma.comp (TensorProduct.map a.toLinearMap c.toLinearMap)

/-- The short exact sequence of groupoid objects given by a submodule and its quotient. -/
private abbrev submoduleSequence {R : Type u} [CommRing R]
    (L : FiniteLengthModuleIso.{u, v} R) (S : Submodule R L.of.obj) :
    ShortExact (finiteLengthSubmoduleObject L.of.property S) L
      (finiteLengthQuotientObject L.of.property S) :=
  ⟨S.subtype, S.mkQ, S.subtype_injective, S.mkQ_surjective,
    LinearMap.exact_iff.mpr (by simp)⟩

/-- The comparison on a module is compatible with the short exact sequence coming from a
simple submodule of its socle. -/
private lemma comparison_submodule_socle {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R) (L : FiniteLengthModuleIso.{u, v} R) :
    let S := socleSubmodule R L.of.obj
    (submoduleSequence L S).Compatible
      (comparison D (finiteLengthSubmoduleObject L.of.property S))
      (comparison D L)
      (comparison D (finiteLengthQuotientObject L.of.property S)) := by
  dsimp only
  let S := socleSubmodule R L.of.obj
  rw [comparison_eq_residueComparison D _ socle_killed]
  by_cases hL : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : L.of.obj, r • x = 0
  · have hQ := killed_of_surjective S.mkQ_surjective hL
    rw [comparison_eq_residueComparison D L hL, comparison_eq_residueComparison D _ hQ]
    exact D.residueComparison_gamma (K := finiteLengthSubmoduleObject L.of.property S)
      (L := L) (M := finiteLengthQuotientObject L.of.property S) S.subtype S.mkQ S.subtype_injective
      S.mkQ_surjective (submoduleSequence L S).exact socle_killed hL hQ
  · conv in (comparison D L) =>
      unfold comparison
      rw [pointwiseComparison]
      simp only [dite_eq_right hL]
    exact extendComparisonAcrossExact_spec D _ _ _ _ _ _ _ _ _ _

/-- A comparison obeying the defining rule is unique. -/
private lemma determinantComparison_unique {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R)
    (η : ∀ M : FiniteLengthModuleIso.{u, v} R, Comparison D M)
    (hη : IsDeterminantComparison D η) : η = comparison D := by
  funext L
  generalize hn : moduleLength R L.of.obj = n
  induction n using Nat.strong_induction_on generalizing L with
  | h n ih =>
    by_cases hL : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : L.of.obj, r • x = 0
    · exact (hη.2.2 L hL).trans (comparison_eq_residueComparison D _ hL).symm
    · let S := socleSubmodule R L.of.obj
      have hK : η (finiteLengthSubmoduleObject L.of.property S) =
          comparison D (finiteLengthSubmoduleObject L.of.property S) :=
        (hη.2.2 _ socle_killed).trans (comparison_eq_residueComparison D _ socle_killed).symm
      have hQ := ih (moduleLength R (L.of.obj ⧸ S)) (hn ▸ socle_quotient_length_lt L hL)
        (finiteLengthQuotientObject L.of.property S) rfl
      apply LinearEquiv.toLinearMap_injective
      apply (LinearMap.cancel_right
        (D.gamma_bijective (K := finiteLengthSubmoduleObject L.of.property S)
          (L := L) (M := finiteLengthQuotientObject L.of.property S)
          S.subtype S.mkQ S.subtype_injective S.mkQ_surjective
          (submoduleSequence L S).exact).2).mp
      rw [hη.2.1 (K := finiteLengthSubmoduleObject L.of.property S)
        (L := L) (M := finiteLengthQuotientObject L.of.property S)
        S.subtype S.mkQ S.subtype_injective S.mkQ_surjective (submoduleSequence L S).exact,
        hK, hQ]
      exact (comparison_submodule_socle D L).symm

/-- A commutative three-by-three diagram of groupoid objects with exact rows and columns. -/
private structure ExactGrid {R : Type u} [CommRing R] where
  (A B C D E F G H I : FiniteLengthModuleIso.{u, v} R)
  top : ShortExact A B C
  middle : ShortExact D E F
  bottom : ShortExact G H I
  left : ShortExact A D G
  center : ShortExact B E H
  right : ShortExact C F I
  comm₁ : middle.i.comp left.i = center.i.comp top.i
  comm₂ : middle.p.comp center.i = right.i.comp top.p
  comm₃ : bottom.i.comp left.p = center.p.comp middle.i
  comm₄ : bottom.p.comp center.p = right.p.comp middle.p

/-- The signed interchange of the middle determinant factors, for the determinant
construction. -/
private abbrev interchange {R : Type u} [CommRing R] [IsLocalRing R]
    (g : ExactGrid.{u, v} (R := R)) :=
  signedTensorInterchange (IsLocalRing.ResidueField R)
    (determinant R g.A.of.obj) (determinant R g.C.of.obj)
    (determinant R g.G.of.obj) (determinant R g.I.of.obj)
    (moduleLength R g.C.of.obj) (moduleLength R g.G.of.obj)

/-- The signed interchange of the middle factors, for a determinant theory. -/
private abbrev interchangeD {R : Type u} [CommRing R] [IsLocalRing R]
    (g : ExactGrid.{u, v} (R := R)) (D : NormalizedDeterminantTheory.{u, v, w} R) :=
  signedTensorInterchange (IsLocalRing.ResidueField R)
    (D.toFunctor.obj g.A).of.obj (D.toFunctor.obj g.C).of.obj
    (D.toFunctor.obj g.G).of.obj (D.toFunctor.obj g.I).of.obj
    (moduleLength R g.C.of.obj) (moduleLength R g.G.of.obj)

/-- The three-by-three axiom of the determinant construction, in the form used here. -/
private lemma grid_commutes {R : Type u} [CommRing R] [IsLocalRing R]
    (g : ExactGrid.{u, v} (R := R)) :
    g.center.gamma.comp (TensorProduct.map g.top.gamma g.bottom.gamma) =
    g.middle.gamma.comp ((TensorProduct.map g.left.gamma g.right.gamma).comp
      (interchange g)) :=
  determinantExactSequenceMap_three_by_three
    g.top.i g.top.p g.middle.i g.middle.p g.bottom.i g.bottom.p
    g.left.i g.center.i g.right.i g.left.p g.center.p g.right.p
    g.top.hi g.top.hp g.top.exact g.middle.hi g.middle.hp g.middle.exact
    g.bottom.hi g.bottom.hp g.bottom.exact g.left.hi g.left.hp g.left.exact
    g.center.hi g.center.hp g.center.exact g.right.hi g.right.hp g.right.exact
    g.comm₁ g.comm₂ g.comm₃ g.comm₄
    g.A.of.property g.B.of.property g.C.of.property g.D.of.property g.E.of.property
    g.F.of.property g.G.of.property g.H.of.property g.I.of.property

/-- The three-by-three axiom of a determinant theory, in the form used here. -/
private lemma grid_commutesD {R : Type u} [CommRing R] [IsLocalRing R]
    (g : ExactGrid.{u, v} (R := R)) (D : NormalizedDeterminantTheory.{u, v, w} R) :
    (g.center.gammaD D).comp (TensorProduct.map (g.top.gammaD D) (g.bottom.gammaD D)) =
    (g.middle.gammaD D).comp
      ((TensorProduct.map (g.left.gammaD D) (g.right.gammaD D)).comp (interchangeD g D)) :=
  D.gamma_three_by_three (A := g.A) (B := g.B) (C := g.C) (D := g.D) (E := g.E)
    (F := g.F) (G := g.G) (H := g.H) (I := g.I)
    g.top.i g.top.p g.middle.i g.middle.p g.bottom.i g.bottom.p
    g.left.i g.center.i g.right.i g.left.p g.center.p g.right.p
    g.top.hi g.top.hp g.top.exact g.middle.hi g.middle.hp g.middle.exact
    g.bottom.hi g.bottom.hp g.bottom.exact g.left.hi g.left.hp g.left.exact
    g.center.hi g.center.hp g.center.exact g.right.hi g.right.hp g.right.exact
    g.comm₁ g.comm₂ g.comm₃ g.comm₄

/-- The signed interchange is natural in the four comparisons. -/
private lemma interchange_natural {R : Type u} [CommRing R] [IsLocalRing R]
    (g : ExactGrid.{u, v} (R := R)) {D : NormalizedDeterminantTheory.{u, v, w} R}
    (a : Comparison D g.A) (c : Comparison D g.C)
    (d : Comparison D g.G) (i : Comparison D g.I) :
    (interchange g).comp
      (TensorProduct.map (TensorProduct.map a.toLinearMap c.toLinearMap)
        (TensorProduct.map d.toLinearMap i.toLinearMap)) =
    (TensorProduct.map (TensorProduct.map a.toLinearMap d.toLinearMap)
      (TensorProduct.map c.toLinearMap i.toLinearMap)).comp (interchangeD g D) := by
  ext x y z w
  simp [interchange, interchangeD, signedTensorInterchange]

/-- Scaling by a unit of the base field does not change surjectivity. -/
private lemma surjective_smul_equiv {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] W) (c : k) (hc : c ≠ 0) :
    Function.Surjective (c • e.toLinearMap) := by
  intro y
  refine ⟨e.symm (c⁻¹ • y), ?_⟩
  simp [smul_smul, hc]

/-- The signed interchange of a determinant theory is surjective. -/
private lemma interchangeD_surjective {R : Type u} [CommRing R] [IsLocalRing R]
    (g : ExactGrid.{u, v} (R := R)) (D : NormalizedDeterminantTheory.{u, v, w} R) :
    Function.Surjective (interchangeD g D) := by
  unfold interchangeD signedTensorInterchange
  exact surjective_smul_equiv _ _ (by simp)

/-- In an exact three-by-three grid, compatibility of the comparisons along the outer rows
and columns forces compatibility in the middle. -/
private lemma compatible_middle {R : Type u} [CommRing R] [IsLocalRing R]
    (g : ExactGrid.{u, v} (R := R)) {D : NormalizedDeterminantTheory.{u, v, w} R}
    (a : Comparison D g.A) (b : Comparison D g.B) (c : Comparison D g.C)
    (d : Comparison D g.D) (e : Comparison D g.E) (f : Comparison D g.F)
    (j : Comparison D g.G) (h : Comparison D g.H) (i : Comparison D g.I)
    (ht : g.top.Compatible a b c) (hb : g.bottom.Compatible j h i)
    (hl : g.left.Compatible a d j) (hc : g.center.Compatible b e h)
    (hr : g.right.Compatible c f i) : g.middle.Compatible d e f := by
  unfold ShortExact.Compatible at *
  apply (LinearMap.cancel_right
    (g := (TensorProduct.map (g.left.gammaD D) (g.right.gammaD D)).comp (interchangeD g D))
    ((TensorProduct.map_bijective
      (D.gamma_bijective (K := g.A) (L := g.D) (M := g.G)
        g.left.i g.left.p g.left.hi g.left.hp g.left.exact)
      (D.gamma_bijective (K := g.C) (L := g.F) (M := g.I)
        g.right.i g.right.p g.right.hi g.right.hp g.right.exact)).2.comp
        (interchangeD_surjective g D))).mp
  show (e.toLinearMap.comp (g.middle.gammaD D)).comp
      ((TensorProduct.map (g.left.gammaD D) (g.right.gammaD D)).comp (interchangeD g D)) = _
  calc
    _ = (e.toLinearMap.comp (g.center.gammaD D)).comp
        (TensorProduct.map (g.top.gammaD D) (g.bottom.gammaD D)) := by
      rw [LinearMap.comp_assoc, ← grid_commutesD, ← LinearMap.comp_assoc]
    _ = g.center.gamma.comp
        (TensorProduct.map (g.top.gamma.comp (TensorProduct.map a.toLinearMap c.toLinearMap))
          (g.bottom.gamma.comp (TensorProduct.map j.toLinearMap i.toLinearMap))) := by
      rw [hc, LinearMap.comp_assoc, ← TensorProduct.map_comp, ht, hb]
    _ = (g.center.gamma.comp (TensorProduct.map g.top.gamma g.bottom.gamma)).comp
        (TensorProduct.map (TensorProduct.map a.toLinearMap c.toLinearMap)
          (TensorProduct.map j.toLinearMap i.toLinearMap)) := by
      rw [TensorProduct.map_comp, LinearMap.comp_assoc]
    _ = g.middle.gamma.comp
        ((TensorProduct.map g.left.gamma g.right.gamma).comp
          ((TensorProduct.map (TensorProduct.map a.toLinearMap j.toLinearMap)
            (TensorProduct.map c.toLinearMap i.toLinearMap)).comp (interchangeD g D))) := by
      rw [grid_commutes, LinearMap.comp_assoc, LinearMap.comp_assoc, interchange_natural]
    _ = (g.middle.gamma.comp (TensorProduct.map d.toLinearMap f.toLinearMap)).comp
        ((TensorProduct.map (g.left.gammaD D) (g.right.gammaD D)).comp
          (interchangeD g D)) := by
      rw [← LinearMap.comp_assoc (interchangeD g D), ← TensorProduct.map_comp, ← hl, ← hr,
        TensorProduct.map_comp]
      simp only [LinearMap.comp_assoc]

/-- A linear equivalence read as an isomorphism of module objects. -/
private abbrev isoOfLinearEquiv {R : Type u} [CommRing R]
    {M N : FiniteLengthModuleIso.{u, v} R} (e : M.of.obj ≃ₗ[R] N.of.obj) : M ⟶ N :=
  (Core.isoMk (ObjectProperty.isoMk
    (fun X : ModuleCat.{v} R => IsFiniteLength R X) e.toModuleIso)).hom

/-- Naturality of a comparison for an isomorphism of modules. -/
private def NaturalComparison {R : Type u} [CommRing R] [IsLocalRing R]
    {D : NormalizedDeterminantTheory.{u, v, w} R} {M N : FiniteLengthModuleIso.{u, v} R}
    (a : Comparison D M) (b : Comparison D N) (f : M ⟶ N) : Prop :=
  b.toLinearMap.comp (D.toFunctor.map f).iso.hom.hom.hom =
    ((determinantFunctor R).mapLinearEquiv f).toLinearMap.comp a.toLinearMap

/-- A comparison transported across a short exact sequence is natural when the comparisons on
the outer terms are. -/
private lemma naturalComparison_of_exact {R : Type u} [CommRing R] [IsLocalRing R]
    {D : NormalizedDeterminantTheory.{u, v, w} R}
    {K L M K' L' M' : FiniteLengthModuleIso.{u, v} R}
    (s : ShortExact K L M) (t : ShortExact K' L' M')
    (a : Comparison D K) (b : Comparison D L) (c : Comparison D M)
    (a' : Comparison D K') (b' : Comparison D L') (c' : Comparison D M')
    (u : K ⟶ K') (v : L ⟶ L') (w : M ⟶ M')
    (hu : t.i.comp u.iso.hom.hom.hom = v.iso.hom.hom.hom.comp s.i)
    (hw : t.p.comp v.iso.hom.hom.hom = w.iso.hom.hom.hom.comp s.p)
    (hs : s.Compatible a b c) (ht : t.Compatible a' b' c')
    (ha : NaturalComparison a a' u) (hc : NaturalComparison c c' w) :
    NaturalComparison b b' v := by
  unfold NaturalComparison at *
  unfold ShortExact.Compatible at hs ht
  apply (LinearMap.cancel_right
    (D.gamma_bijective (K := K) (L := L) (M := M) s.i s.p s.hi s.hp s.exact).2).mp
  have hD := D.gamma_natural s.i s.p t.i t.p s.hi s.hp s.exact
    t.hi t.hp t.exact u v w hu hw
  have hC := determinantExactSequenceMap_natural
    s.i s.p t.i t.p s.hi s.hp s.exact t.hi t.hp t.exact u v w hu hw
  show (b'.toLinearMap.comp (D.toFunctor.map v).iso.hom.hom.hom).comp
    (s.gammaD D) = _
  calc
    _ = (b'.toLinearMap.comp (t.gammaD D)).comp
        (TensorProduct.map (D.toFunctor.map u).iso.hom.hom.hom
          (D.toFunctor.map w).iso.hom.hom.hom) := by
      rw [LinearMap.comp_assoc, ← hD, ← LinearMap.comp_assoc]
    _ = t.gamma.comp
        (TensorProduct.map
          (((determinantFunctor R).mapLinearEquiv u).toLinearMap.comp a.toLinearMap)
          (((determinantFunctor R).mapLinearEquiv w).toLinearMap.comp c.toLinearMap)) := by
      rw [ht, LinearMap.comp_assoc, ← TensorProduct.map_comp, ha, hc]
    _ = (((determinantFunctor R).mapLinearEquiv v).toLinearMap.comp s.gamma).comp
        (TensorProduct.map a.toLinearMap c.toLinearMap) := by
      rw [TensorProduct.map_comp, ← LinearMap.comp_assoc, hC]
    _ = _ := by rw [LinearMap.comp_assoc, ← hs, ← LinearMap.comp_assoc]

/-- An isomorphism of modules carries the socle into the socle. -/
private lemma socle_map_le {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (socleSubmodule R M).map f ≤ socleSubmodule R N := by
  rintro _ ⟨x, hx, rfl⟩
  apply (Submodule.mem_torsionBySet_iff _ _).mpr
  intro r
  rw [← map_smul, socleSubmodule_annihilated (r : R) r.property hx, map_zero]

/-- An isomorphism of modules restricts to an isomorphism of socles. -/
private lemma socle_map_equiv {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    (socleSubmodule R M).map e.toLinearMap = socleSubmodule R N := by
  apply le_antisymm (socle_map_le e.toLinearMap)
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  exact socle_map_le e.symm.toLinearMap ⟨y, hy, rfl⟩

/-- `pointwiseComparison` is natural for isomorphisms of modules. -/
private lemma comparison_natural {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R)
    {L N : FiniteLengthModuleIso.{u, v} R} (f : L ⟶ N) :
    NaturalComparison (comparison D L) (comparison D N) f := by
  generalize hn : moduleLength R L.of.obj = n
  induction n using Nat.strong_induction_on generalizing L N with
  | h n ih =>
    let e := underlyingLinearEquiv f
    by_cases hL : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : L.of.obj, r • x = 0
    · have hN := killed_of_surjective e.surjective hL
      rw [comparison_eq_residueComparison D L hL, comparison_eq_residueComparison D N hN]
      exact D.residueComparison_natural f hL hN
    · let S := socleSubmodule R L.of.obj
      let T := socleSubmodule R N.of.obj
      let K := finiteLengthSubmoduleObject L.of.property S
      let K' := finiteLengthSubmoduleObject N.of.property T
      let Q := finiteLengthQuotientObject L.of.property S
      let Q' := finiteLengthQuotientObject N.of.property T
      let u : K ⟶ K' := isoOfLinearEquiv (e.ofSubmodules S T (socle_map_equiv e))
      let w : Q ⟶ Q' := isoOfLinearEquiv (Submodule.Quotient.equiv S T e (socle_map_equiv e))
      have hlt : moduleLength R Q.of.obj < n := hn ▸ socle_quotient_length_lt L hL
      apply naturalComparison_of_exact (submoduleSequence L S) (submoduleSequence N T)
        _ _ _ _ _ _ u f w
      · ext x
        rfl
      · ext x
        rfl
      · exact comparison_submodule_socle D L
      · exact comparison_submodule_socle D N
      · rw [comparison_eq_residueComparison D K socle_killed,
          comparison_eq_residueComparison D K' socle_killed]
        exact D.residueComparison_natural u socle_killed socle_killed
      · exact ih _ hlt w rfl

/-- Pulling a simple submodule of the socle back along an isomorphism is injective on
submodules. -/
private lemma socle_comap_injective {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    (socleSubmodule R N).comap f = socleSubmodule R M := by
  ext x
  refine ⟨fun hx => (Submodule.mem_torsionBySet_iff _ _).mpr fun r => hf ?_,
    fun hx => socle_map_le f ⟨x, hx, rfl⟩⟩
  rw [map_smul, map_zero]
  exact socleSubmodule_annihilated (r : R) r.property hx

/-- The three-by-three grid built from two simple submodules of the socle, used to show that
`pointwiseComparison` does not depend on which one is chosen. -/
private def inducedGrid {R : Type u} [CommRing R] [IsLocalRing R]
    {K L M : FiniteLengthModuleIso.{u, v} R} (s : ShortExact K L M) :
    ExactGrid.{u, v} (R := R) := by
  let A := socleSubmodule R K.of.obj
  let B := socleSubmodule R L.of.obj
  let C := B.map s.p
  have hiAB : A ≤ B.comap s.i := Submodule.map_le_iff_le_comap.mp (socle_map_le s.i)
  have hpBC : B ≤ C.comap s.p := Submodule.le_comap_map s.p B
  let iAB : A →ₗ[R] B := (s.i.comp A.subtype).codRestrict B (fun x => hiAB x.property)
  let pBC : B →ₗ[R] C := (s.p.comp B.subtype).codRestrict C
    (fun x => ⟨x, x.property, rfl⟩)
  let iGH := A.mapQ B s.i hiAB
  let pHI := B.mapQ C s.p hpBC
  have hAB : Function.Injective iAB := fun x y h => Subtype.ext (s.hi (congrArg Subtype.val h))
  have hBC : Function.Surjective pBC := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  have hexABC : Function.Exact iAB pBC := by
    refine fun y => ⟨fun hy => ?_, ?_⟩
    · have hy' : s.p y = 0 := congrArg Subtype.val hy
      obtain ⟨x, hx⟩ := (s.exact y).mp hy'
      have hxA : x ∈ A := by
        change x ∈ socleSubmodule R K.of.obj
        rw [← socle_comap_injective s.i s.hi]
        change s.i x ∈ B
        rw [hx]
        exact y.property
      exact ⟨⟨x, hxA⟩, Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext (s.exact.apply_apply_eq_zero x)
  have hGH : Function.Injective iGH := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, socle_comap_injective s.i s.hi]
    simp [A]
  have hHI : Function.Surjective pHI := by
    intro x
    obtain ⟨m, rfl⟩ := C.mkQ_surjective x
    obtain ⟨l, rfl⟩ := s.hp m
    exact ⟨B.mkQ l, rfl⟩
  have hexGHI : Function.Exact iGH pHI :=
    (s.exact.exact_mapQ_iff hiAB hpBC).mpr inf_le_right
  exact {
    A := finiteLengthSubmoduleObject K.of.property A
    B := finiteLengthSubmoduleObject L.of.property B
    C := finiteLengthSubmoduleObject M.of.property C
    D := K, E := L, F := M
    G := finiteLengthQuotientObject K.of.property A
    H := finiteLengthQuotientObject L.of.property B
    I := finiteLengthQuotientObject M.of.property C
    top := ⟨iAB, pBC, hAB, hBC, hexABC⟩
    middle := s
    bottom := ⟨iGH, pHI, hGH, hHI, hexGHI⟩
    left := submoduleSequence K A
    center := submoduleSequence L B
    right := submoduleSequence M C
    comm₁ := by ext; rfl
    comm₂ := by ext; rfl
    comm₃ := by ext; rfl
    comm₄ := by ext; rfl }

/-- On a module killed by the maximal ideal, the comparison is the normalization axiom. -/
private lemma comparison_of_killed {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R)
    {K L M : FiniteLengthModuleIso.{u, v} R} (s : ShortExact K L M)
    (hL : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : L.of.obj, r • x = 0) :
    s.Compatible (comparison D K) (comparison D L) (comparison D M) := by
  have hK : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : K.of.obj, r • x = 0 := by
    intro r hr x
    apply s.hi
    rw [map_smul, map_zero, hL r hr]
  have hM := killed_of_surjective s.hp hL
  rw [comparison_eq_residueComparison D K hK, comparison_eq_residueComparison D L hL,
    comparison_eq_residueComparison D M hM]
  exact D.residueComparison_gamma s.i s.p s.hi s.hp s.exact hK hL hM

/-- The comparison is compatible with every short exact sequence. -/
private lemma comparison_exact {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R)
    {K L M : FiniteLengthModuleIso.{u, v} R} (s : ShortExact K L M) :
    s.Compatible (comparison D K) (comparison D L) (comparison D M) := by
  generalize hn : moduleLength R L.of.obj = n
  induction n using Nat.strong_induction_on generalizing K L M with
  | h n ih =>
    by_cases hL : ∀ r ∈ IsLocalRing.maximalIdeal R, ∀ x : L.of.obj, r • x = 0
    · exact comparison_of_killed D s hL
    · let g := inducedGrid s
      have hlt : moduleLength R g.H.of.obj < n := hn ▸ socle_quotient_length_lt L hL
      apply compatible_middle g (comparison D g.A) (comparison D g.B) (comparison D g.C)
        (comparison D g.D) (comparison D g.E) (comparison D g.F)
        (comparison D g.G) (comparison D g.H) (comparison D g.I)
      · exact comparison_of_killed D _ socle_killed
      · exact ih _ hlt g.bottom rfl
      · exact comparison_submodule_socle D K
      · exact comparison_submodule_socle D L
      · cases subsingleton_or_nontrivial K.of.obj with
        | inl hK =>
          have hp : Function.Injective s.p := by
            rw [← LinearMap.ker_eq_bot, s.exact.linearMap_ker_eq]
            apply LinearMap.range_eq_bot.mpr
            ext x
            rw [hK.elim x 0, map_zero]
            rfl
          have heq : (socleSubmodule R L.of.obj).map s.p = socleSubmodule R M.of.obj :=
            socle_map_equiv (LinearEquiv.ofBijective s.p ⟨hp, s.hp⟩)
          show (submoduleSequence M ((socleSubmodule R L.of.obj).map s.p)).Compatible
            (comparison D (finiteLengthSubmoduleObject M.of.property
              ((socleSubmodule R L.of.obj).map s.p)))
            (comparison D M)
            (comparison D (finiteLengthQuotientObject M.of.property
              ((socleSubmodule R L.of.obj).map s.p)))
          rw [heq]
          exact comparison_submodule_socle D M
        | inr hK =>
          have hltM : moduleLength R M.of.obj < n :=
            hn ▸ moduleLength_lt_of_exact s.i s.p s.hi s.hp s.exact K.of.property M.of.property
          exact ih _ hltM g.right rfl

/-- A normalized determinant theory admits a unique comparison with the determinant
construction: an isomorphism that is natural, compatible with the exact-sequence maps, and
equal to the given identification on modules annihilated by the maximal ideal. -/
public theorem existsUnique_normalizedComparison
    {R : Type u} [CommRing R] [IsLocalRing R]
    (D : NormalizedDeterminantTheory.{u, v, w} R) :
    ∃! η : ∀ M : FiniteLengthModuleIso.{u, v} R,
      (D.toFunctor.obj M).of.obj ≃ₗ[IsLocalRing.ResidueField R]
        determinant R M.of.obj,
      IsDeterminantComparison D η :=
  ⟨comparison D, ⟨fun f => comparison_natural D f,
    fun i p hi hp hip => comparison_exact D ⟨i, p, hi, hp, hip⟩,
    fun M hM => pointwiseComparison_on_killed D M.of.property hM⟩,
    determinantComparison_unique D⟩

end Module.FiniteLength

end
