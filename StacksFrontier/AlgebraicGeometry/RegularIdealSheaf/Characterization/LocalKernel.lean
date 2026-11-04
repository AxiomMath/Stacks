module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.StalkGenerators
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Basic
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsSheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.ConormalSheaves
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.FiniteTypeAndWords

/-!
# Quasi-regular ideal sheaves: the local kernel and free presentations

Generation read on germs, polynomial classes of symmetric words, the local kernel of the
canonical map for quasi-regular generators, and the comparison of free presheaves of modules
with their sheafifications.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingTheory.QuasiRegular
open scoped BigOperators
universe u v

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible] SheafOfModules.toSheaf PresheafOfModules.presheaf
open Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal in
attribute [local implicit_reducible] quotientPresheaf quotientSheaf gradedPresheaf
attribute [local implicit_reducible] PresheafOfModules.freeObj ModuleCat.free
  CategoryTheory.Functor.sheafPushforwardContinuous

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

@[sga "1 II 4.14" "(ii), special case"]
private noncomputable def gradedPieceOneBasis {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R)
    (hf : Function.Injective (associatedGradedMap f)) :
    Module.Basis (Fin r) (qrRbar f) (Construction.GradedPiece (Jid f) 1) :=
  (cotangentBasis f hf).map
    (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (gradedPieceOneEquivCotangent (Jid f))).symm

private lemma canonicalMap_bijective_of_polynomialCanonicalMap_injective
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (hf : Function.Injective (associatedGradedMap f)) (n : ℕ) :
    Function.Bijective (Construction.canonicalMap (Jid f) n) :=
  ⟨canonicalMap_injective_of_polynomialCanonicalMap_injective f hf n,
    Construction.canonicalMap_surjective (Jid f) n⟩

namespace Construction

lemma symmetricMap_wordClass {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (K : Ideal S) (φ : R →+* S) (h : I ≤ K.comap φ)
    (n : ℕ) (a : Fin n → I) :
    symmetricMap I K φ h n (wordClass I n a) =
      wordClass K n (fun i => idealMap I K φ h (a i)) := by
  show Submodule.Quotient.mk (wordsMap I K φ h n (word I a)) = _
  rw [wordsMap_word]
  rfl

private noncomputable def monomialClass {R : Type u} [CommRing R]
    (I : Ideal R) {r : ℕ} (f : Fin r → I) (n : ℕ) (e : Fin r →₀ ℕ) :
    SymmetricPower I n :=
  if h : ∃ t : Fin n → Fin r, tupleExponent t = e then
    wordClass I n (f ∘ h.choose) else 0

private lemma monomialClass_tupleExponent {R : Type u} [CommRing R]
    (I : Ideal R) {r n : ℕ} (f : Fin r → I) (t : Fin n → Fin r) :
    monomialClass I f n (tupleExponent t) = wordClass I n (f ∘ t) := by
  classical
  let h : ∃ s : Fin n → Fin r, tupleExponent s = tupleExponent t := ⟨t, rfl⟩
  rw [monomialClass, dite_eq_left h]
  show wordClass I n (f ∘ h.choose) = _
  obtain ⟨σ, hσ⟩ := (tupleExponent_eq_iff h.choose t).mp h.choose_spec
  rw [← hσ]
  exact wordClass_perm I (f ∘ t) σ

private noncomputable def polynomialClass {R : Type u} [CommRing R]
    (I : Ideal R) {r : ℕ} (f : Fin r → I) (n : ℕ) :
    MvPolynomial (Fin r) R →ₗ[R] SymmetricPower I n :=
  (MvPolynomial.basisMonomials (Fin r) R).constr R (monomialClass I f n)

private lemma polynomialClass_monomial {R : Type u} [CommRing R]
    (I : Ideal R) {r : ℕ} (f : Fin r → I) (n : ℕ) (e : Fin r →₀ ℕ) (c : R) :
    polynomialClass I f n (MvPolynomial.monomial e c) = c • monomialClass I f n e := by
  have h : MvPolynomial.monomial e c = c • MvPolynomial.monomial e (1 : R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul]
  congr 1
  exact Module.Basis.constr_basis _ _ _ _

private lemma polynomialClass_eq_zero_of_coeff_mem {R : Type u} [CommRing R]
    (I : Ideal R) {r : ℕ} (f : Fin r → I) (n : ℕ) (p : MvPolynomial (Fin r) R)
    (hp : ∀ e, p.coeff e ∈ I) : polynomialClass I f n p = 0 := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro e he
  rw [polynomialClass_monomial]
  exact symmetricPower_torsion I n (a := ⟨p.coeff e, hp e⟩)

private lemma symmetricMap_polynomialClass {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (K : Ideal S) (φ : R →+* S) (h : I ≤ K.comap φ)
    {r : ℕ} (f : Fin r → I) (n : ℕ) (p : MvPolynomial (Fin r) R) :
    symmetricMap I K φ h n (polynomialClass I f n p) =
      polynomialClass K (fun i => idealMap I K φ h (f i)) n (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial e c =>
    simp only [MvPolynomial.map_monomial, polynomialClass_monomial, map_smulₛₗ]
    congr 1
    unfold monomialClass
    split_ifs with he
    · exact symmetricMap_wordClass _ _ _ _ _ _
    · exact map_zero _

end Construction

lemma exists_common_open {T : Type u} [TopologicalSpace T]
    {ι : Type v} [Finite ι] (x : T) (U : Opens T)
    (V : ι → Opens T) (hx : x ∈ U) (hV : ∀ i, x ∈ V i) :
    ∃ W : Opens T, x ∈ W ∧ W ≤ U ∧ ∀ i, W ≤ V i := by
  let W : Opens T := ⟨(U : Set T) ∩ ⋂ i, (V i : Set T),
    U.isOpen.inter (isOpen_iInter_of_finite (fun i => (V i).isOpen))⟩
  exact ⟨W, ⟨hx, Set.mem_iInter.mpr hV⟩, fun _ h => h.1,
    fun i _ h => Set.mem_iInter.mp h.2 i⟩

lemma symmetric_restrict_comp (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (n : ℕ)
    {U V W : Opens X} (i : V ⟶ U) (j : W ⟶ V)
    (z : Construction.SymmetricPower (sectionIdeal X J (op U)) n) :
    Construction.symmetricMap _ _ (X.presheaf.map j.op).hom
      (sectionIdeal_map X J j.op) n
      (Construction.symmetricMap _ _ (X.presheaf.map i.op).hom
        (sectionIdeal_map X J i.op) n z) =
      Construction.symmetricMap _ _ (X.presheaf.map (j ≫ i).op).hom
        (sectionIdeal_map X J (j ≫ i).op) n z :=
  (PresheafOfModules.map_comp_apply (symmetricPresheaf X J n) i.op j.op z).symm

private lemma exists_local_generatorWord_span (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U)) (hf : IsGeneratedByOn X J U f)
    (n : ℕ) (z : Construction.SymmetricPower (sectionIdeal X J (op U)) n)
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U),
      Construction.symmetricMap _ _ (X.presheaf.map i.op).hom
          (sectionIdeal_map X J i.op) n z ∈
        Submodule.span (X.presheaf.obj (op V))
          (Set.range (fun t : Fin n → Fin r =>
            Construction.wordClass (sectionIdeal X J (op V)) n
              (fun j => ⟨X.presheaf.map i.op (f (t j)),
                J.toSubmodule.map_mem i.op
                  (mem_of_isGeneratedByOn X J U f hf (t j))⟩))) := by
  classical
  let g (V : Opens X) (i : V ⟶ U) : Fin r → sectionIdeal X J (op V) :=
    fun k => ⟨X.presheaf.map i.op (f k), J.toSubmodule.map_mem i.op
      (mem_of_isGeneratedByOn X J U f hf k)⟩
  let S (V : Opens X) (i : V ⟶ U) := Submodule.span (X.presheaf.obj (op V))
    (Set.range (fun t : Fin n → Fin r =>
      Construction.wordClass (sectionIdeal X J (op V)) n (g V i ∘ t)))
  have hres {V W : Opens X} (i : V ⟶ U) (j : W ⟶ V)
      {a : Construction.SymmetricPower (sectionIdeal X J (op V)) n} (ha : a ∈ S V i) :
      Construction.symmetricMap _ _ (X.presheaf.map j.op).hom
        (sectionIdeal_map X J j.op) n a ∈ S W (j ≫ i) := by
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨t, rfl⟩ := ha
      rw [Construction.symmetricMap_wordClass]
      apply Submodule.subset_span
      refine ⟨t, ?_⟩
      apply congrArg (Construction.wordClass (sectionIdeal X J (op W)) n)
      funext k
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (X.presheaf.map_comp i.op j.op) (f (t k))
    | zero => simp
    | add a b ha hb ia ib => simpa only [map_add] using Submodule.add_mem _ ia ib
    | smul c a ha ia => simpa only [map_smulₛₗ] using Submodule.smul_mem _ _ ia
  induction z using Submodule.Quotient.induction_on with | _ z =>
  induction z using Finsupp.induction_linear with
  | zero =>
    refine ⟨U, hx, 𝟙 U, ?_⟩
    simp only [Submodule.Quotient.mk_zero, map_zero]
    exact (S U _).zero_mem
  | add a b ha hb =>
    obtain ⟨V, hxV, i, hi⟩ := ha
    obtain ⟨W, hxW, j, hj⟩ := hb
    let l : V ⊓ W ⟶ V := homOfLE inf_le_left
    let k : V ⊓ W ⟶ W := homOfLE inf_le_right
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, l ≫ i, ?_⟩
    have hi' := hres i l hi
    have hj' := hres j k hj
    simp only [symmetric_restrict_comp] at hi' hj'
    have hk : k ≫ j = l ≫ i := Subsingleton.elim _ _
    rw [hk] at hj'
    simpa only [Submodule.Quotient.mk_add, map_add, S, g, Function.comp_def] using
      (S (V ⊓ W) (l ≫ i)).add_mem hi' hj'
  | single a c =>
    have hl (k : Fin n) := exists_local_linearCombination_of_isGeneratedByOn
      X J U U f hf le_rfl (a k) (a k).property x hx
    choose V hxV i j b hb using hl
    obtain ⟨W, hxW, hWU, hWV⟩ := exists_common_open x U V hx hxV
    let l : W ⟶ U := homOfLE hWU
    let d : Fin n → Fin r → X.presheaf.obj (op W) :=
      fun k t => X.presheaf.map (homOfLE (hWV k)).op (b k t)
    have he : (fun k => Construction.idealMap _ _ (X.presheaf.map l.op).hom
        (sectionIdeal_map X J l.op) (a k)) =
        fun k => ∑ t, d k t • g W l t := by
      funext k
      apply Subtype.ext
      have h := congrArg (fun s => X.presheaf.map (homOfLE (hWV k)).op s) (hb k)
      have hcomp (m : V k ⟶ U) (s : X.presheaf.obj (op U)) :
          X.presheaf.map (homOfLE (hWV k)).op (X.presheaf.map m.op s) =
            X.presheaf.map l.op s := by
        rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
        rfl
      /- `Construction.idealMap` restricts a ring map to the ideals; its coercion back to the
      ambient ring is the ring map applied to the coercion, which is true by `rfl` but only
      at default transparency. Naming that identity as a term keeps the goal well typed at
      `implicit` transparency, where `dsimp only [LinearMap.restrict_apply]` could not fire. -/
      have hcoe : ((Construction.idealMap (sectionIdeal X J (op U))
            (sectionIdeal X J (op W)) (X.presheaf.map l.op).hom
            (sectionIdeal_map X J l.op) (a k) : X.presheaf.obj (op W)))
          = X.presheaf.map l.op ((a k : X.presheaf.obj (op U))) := rfl
      refine hcoe.trans ?_
      dsimp only [g, d]
      simpa only [map_sum, map_mul, hcomp, Submodule.coe_sum, Submodule.coe_smul,
        smul_eq_mul] using h.symm
    have hh : Construction.symmetricMap _ _ (X.presheaf.map l.op).hom
        (sectionIdeal_map X J l.op) n (Construction.wordClass _ n a) ∈ S W l := by
      rw [Construction.symmetricMap_wordClass, he, MultilinearMap.map_sum]
      apply Submodule.sum_mem
      intro t ht
      rw [MultilinearMap.map_smul_univ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self t))
    refine ⟨W, hxW, l, ?_⟩
    have hc : Finsupp.single a c = c • Construction.word _ a := by simp [Construction.word]
    rw [hc, Submodule.Quotient.mk_smul, map_smulₛₗ]
    exact Submodule.smul_mem _ _ hh

lemma exists_local_mem_of_germ_mem_span (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U V : Opens X)
    {r : ℕ} (f : Fin r → X.presheaf.obj (op U))
    (hf : ∀ k, f k ∈ J.obj (op U)) (s : X.presheaf.obj (op V))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (hs : X.presheaf.germ V x hxV s ∈
      Jid (fun k => X.presheaf.germ U x hxU (f k))) :
    ∃ (W : Opens X) (_ : x ∈ W) (i : W ⟶ V),
      X.presheaf.map i.op s ∈ J.obj (op W) := by
  obtain ⟨W, hxW, iU, iV, a, ha⟩ :=
    exists_local_linearCombination_of_germ_mem_span X U V f s x hxU hxV hs
  refine ⟨W, hxW, iV, ?_⟩
  show X.presheaf.map iV.op s ∈ sectionIdeal X J (op W)
  rw [← ha]
  exact Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_left _ _
    (J.toSubmodule.map_mem iU.op (hf k)))

private lemma isGeneratedByOn_of_germ_mem_span (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X)
    {r : ℕ} (f : Fin r → X.presheaf.obj (op U)) (hf : ∀ i, f i ∈ J.obj (op U))
    (h : ∀ (V : Opens X) (hVU : V ≤ U) (s : X.presheaf.obj (op V)),
      s ∈ J.obj (op V) → ∀ (x : X) (hx : x ∈ V),
      X.presheaf.germ V x hx s ∈ Jid (fun i => X.presheaf.germ U x (hVU hx) (f i))) :
    IsGeneratedByOn X J U f := by
  intro V hVU
  apply le_antisymm
  · intro s hs
    apply (generatedIdealOn X U f).isSheaf s
    intro x hx
    obtain ⟨W, hxW, i, hi⟩ := exists_local_mem_of_germ_mem_span X (generatedIdealOn X U f) U V f
      (mem_generatedIdealOn X U f) s x (hVU hx) hx (h V hVU s hs x hx)
    exact ⟨W, i, hi, hxW⟩
  · exact generatedIdealOn_le X U f J hf (op V)

private lemma isGeneratedByOn_iff_germ_mem_span (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X)
    {r : ℕ} (f : Fin r → X.presheaf.obj (op U)) :
    IsGeneratedByOn X J U f ↔
      (∀ i, f i ∈ J.obj (op U)) ∧
      ∀ (V : Opens X) (hVU : V ≤ U) (s : X.presheaf.obj (op V)),
        s ∈ J.obj (op V) → ∀ (x : X) (hx : x ∈ V),
        X.presheaf.germ V x hx s ∈ Jid (fun i => X.presheaf.germ U x (hVU hx) (f i)) := by
  constructor
  · intro h
    exact ⟨mem_of_isGeneratedByOn X J U f h,
      fun V hVU s hs x hx => germ_mem_span_of_isGeneratedByOn X J U V f h hVU s hs x hx⟩
  · rintro ⟨hf, h⟩
    exact isGeneratedByOn_of_germ_mem_span X J U f hf h

private lemma isGeneratedByOn_restrict (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U V : Opens X) (i : V ⟶ U)
    {r : ℕ} (f : Fin r → X.presheaf.obj (op U))
    (hf : IsGeneratedByOn X J U f) :
    IsGeneratedByOn X J V (fun k => X.presheaf.map i.op (f k)) := by
  apply isGeneratedByOn_of_germ_mem_span
  · intro k
    exact J.toSubmodule.map_mem i.op
      (mem_of_isGeneratedByOn X J U f hf k)
  · intro W hWV s hs x hx
    simpa only [TopCat.Presheaf.germ_res_apply] using
      germ_mem_span_of_isGeneratedByOn X J U W f hf
        (hWV.trans (leOfHom i)) s hs x hx

private lemma germ_cast_open (X : RingedSpace.{u}) {U V : Opens X}
    (h : U = V) (x : X) (hx : x ∈ U) (s : X.presheaf.obj (op U)) :
    X.presheaf.germ V x (h ▸ hx) (h ▸ s) = X.presheaf.germ U x hx s := by
  subst V
  rfl

lemma restrictStalkIso_germ_onRestriction (X : RingedSpace.{u}) (U : Opens X)
    (y : U) (s : X.presheaf.obj (op U)) :
    (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding y).hom
      ((X.restrict U.isOpenEmbedding).presheaf.germ ⊤ y trivial
        (sectionOnRestriction X U s)) =
      X.presheaf.germ U y.1 y.2 s := by
  have h := congrArg (fun k => (ConcreteCategory.hom k)
    (sectionOnRestriction X U s))
    (AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ
      X.toPresheafedSpace U.isOpenEmbedding (⊤ : Opens (TopCat.of U)) y trivial)
  refine h.trans ?_
  have htop : U.isOpenEmbedding.functor.obj
      (⊤ : Opens ((Opens.toTopCat X).obj U)) = U := by
    ext z
    simp
  exact germ_cast_open X htop.symm y.1 y.2 s

lemma span_le_comap_of_generators {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {r : ℕ} (f : Fin r → R) (g : Fin r → S)
    (h : ∀ k, φ (f k) = g k) : Jid f ≤ (Jid g).comap φ := by
  apply Ideal.span_le.mpr
  rintro _ ⟨k, rfl⟩
  show φ (f k) ∈ Jid g
  rw [h]
  exact Ideal.subset_span (Set.mem_range_self k)

private noncomputable def tuplePolynomial {R : Type u} [CommRing R] {r n : ℕ}
    (c : (Fin n → Fin r) → R) : MvPolynomial (Fin r) R :=
  ∑ t, MvPolynomial.monomial (tupleExponent t) (c t)

private lemma polynomialClass_tuplePolynomial {R : Type u} [CommRing R]
    (I : Ideal R) {r n : ℕ} (f : Fin r → I) (c : (Fin n → Fin r) → R) :
    Construction.polynomialClass I f n (tuplePolynomial c) =
      ∑ t, c t • Construction.wordClass I n (f ∘ t) := by
  simp only [tuplePolynomial, map_sum, Construction.polynomialClass_monomial,
    Construction.monomialClass_tupleExponent]

private lemma tuplePolynomial_coeff_mem_of_canonicalMap_eq_zero
    {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R)
    (φ : R →+* S) {r n : ℕ} (f : Fin r → I) (g : Fin r → S)
    (hfg : ∀ k, φ (f k) = g k) (hI : I ≤ (Jid g).comap φ)
    (hg : Function.Injective (associatedGradedMap g))
    (c : (Fin n → Fin r) → R)
    (hz : Construction.canonicalMap (Jid g) n
      (Construction.symmetricMap I (Jid g) φ hI n
        (∑ t, c t • Construction.wordClass I n (f ∘ t))) = 0) :
    ∀ e, φ ((tuplePolynomial c).coeff e) ∈ Jid g := by
  let ψ := (Ideal.Quotient.mk (Jid g)).comp φ
  have he : (fun k => Construction.idealMap I (Jid g) φ hI (f k)) =
      idealGenerator g := by
    funext k
    exact Subtype.ext (hfg k)
  have hzero : associatedGradedMap g
      (MvPolynomial.map ψ (tuplePolynomial c)) = 0 := by
    have hm : MvPolynomial.map ψ (tuplePolynomial c) =
        ∑ t, ψ (c t) • MvPolynomial.monomial (tupleExponent t) (1 : qrRbar g) := by
      simp only [tuplePolynomial, map_sum, MvPolynomial.map_monomial,
        MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_sum]
    simp only [map_smul, polynomialCanonicalMap_tuple]
    simp only [← map_smul]
    rw [← map_sum, ← map_sum]
    have he' : (∑ t, ψ (c t) • Construction.wordClass (Jid g) n
        (idealGenerator g ∘ t)) =
        Construction.symmetricMap I (Jid g) φ hI n
          (∑ t, c t • Construction.wordClass I n (f ∘ t)) := by
      simp only [map_sum, map_smulₛₗ, Construction.symmetricMap_wordClass]
      apply Finset.sum_congr rfl
      intro t ht
      have he'' : (fun k => Construction.idealMap I (Jid g) φ hI ((f ∘ t) k)) =
          idealGenerator g ∘ t := congrArg (fun a => a ∘ t) he
      rw [he'']
      exact (IsScalarTower.algebraMap_smul (S ⧸ Jid g) (φ (c t)) _)
    rw [he']
    show gradedPieceToTarget g n (Construction.canonicalMap (Jid g) n _) = 0
    rw [hz, map_zero]
  have hp := hg (hzero.trans (map_zero _).symm)
  intro e
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := congrArg (MvPolynomial.coeff e) hp
  simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, ψ, RingHom.comp_apply] using h

noncomputable def germInRestriction (X : RingedSpace.{u}) (U : Opens X)
    (x : X) (hxU : x ∈ U) (V : Opens X) (hxV : x ∈ V) :
    X.presheaf.obj (op V) →+* (X.restrict U.isOpenEmbedding).presheaf.stalk ⟨x, hxU⟩ :=
  ((X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨x, hxU⟩).inv.hom).comp
    (X.presheaf.germ V x hxV).hom

lemma germInRestriction_res (X : RingedSpace.{u}) (U : Opens X)
    (x : X) (hxU : x ∈ U) (V W : Opens X) (hxV : x ∈ V) (hxW : x ∈ W)
    (i : V ⟶ W) (s : X.presheaf.obj (op W)) :
    germInRestriction X U x hxU V hxV (X.presheaf.map i.op s) =
      germInRestriction X U x hxU W hxW s := by
  show (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨x, hxU⟩).inv
      (X.presheaf.germ V x hxV (X.presheaf.map i.op s)) =
    (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨x, hxU⟩).inv
      (X.presheaf.germ W x hxW s)
  rw [TopCat.Presheaf.germ_res_apply]

lemma germInRestriction_self (X : RingedSpace.{u}) (U : Opens X)
    (x : X) (hxU : x ∈ U) (s : X.presheaf.obj (op U)) :
    germInRestriction X U x hxU U hxU s =
      (X.restrict U.isOpenEmbedding).presheaf.germ ⊤ ⟨x, hxU⟩ trivial
        (sectionOnRestriction X U s) := by
  show (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨x, hxU⟩).inv
    (X.presheaf.germ U x hxU s) = _
  rw [← restrictStalkIso_germ_onRestriction X U ⟨x, hxU⟩ s]
  exact (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨x, hxU⟩).hom_inv_id_apply _

lemma germInRestriction_mem_span_iff (X : RingedSpace.{u}) (U : Opens X)
    (x : X) (hxU : x ∈ U) {r : ℕ} (f : Fin r → X.presheaf.obj (op U))
    (V : Opens X) (hxV : x ∈ V) (s : X.presheaf.obj (op V)) :
    germInRestriction X U x hxU V hxV s ∈
        Jid (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
          (fun k => sectionOnRestriction X U (f k)) ⟨x, hxU⟩) ↔
      X.presheaf.germ V x hxV s ∈ Jid (fun k => X.presheaf.germ U x hxU (f k)) := by
  let e := X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨x, hxU⟩
  have h₁ := span_le_comap_of_generators e.hom.hom
    (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
      (fun k => sectionOnRestriction X U (f k)) ⟨x, hxU⟩)
    (fun k => X.presheaf.germ U x hxU (f k))
    (fun k => restrictStalkIso_germ_onRestriction X U ⟨x, hxU⟩ (f k))
  have h₂ := span_le_comap_of_generators e.inv.hom
    (fun k => X.presheaf.germ U x hxU (f k))
    (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
      (fun k => sectionOnRestriction X U (f k)) ⟨x, hxU⟩)
    (fun k => germInRestriction_self X U x hxU (f k))
  constructor
  · intro h
    have h' := h₁ h
    change e.hom (e.inv (X.presheaf.germ V x hxV s)) ∈
      Jid (fun k => X.presheaf.germ U x hxU (f k)) at h'
    exact (Iso.inv_hom_id_apply e (X.presheaf.germ V x hxV s)) ▸ h'
  · intro h
    exact h₂ h

lemma canonicalMap_local_kernel_of_quasiRegular_generators
    (X : RingedSpace.{u}) (J : (Stacks.RingedSpace.structureSheafModule X).Submodule)
    (W : Opens X) {r : ℕ} (f : Fin r → X.presheaf.obj (op W))
    (hgen : IsGeneratedByOn X J W f)
    (hqr : IsIso (QuasiRegular.quasiRegularMap (X.restrict W.isOpenEmbedding)
      (fun k => sectionOnRestriction X W (f k))).hom)
    (U : Opens X) (n : ℕ) (z : Construction.SymmetricPower (sectionIdeal X J (op U)) n)
    (hz : Construction.canonicalMap (sectionIdeal X J (op U)) n z = 0)
    (x : X) (hxU : x ∈ U) (hxW : x ∈ W) :
    ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U),
      Construction.symmetricMap _ _ (X.presheaf.map i.op).hom
        (sectionIdeal_map X J i.op) n z = 0 := by
  classical
  let T := U ⊓ W
  let iU : T ⟶ U := homOfLE inf_le_left
  let iW : T ⟶ W := homOfLE inf_le_right
  let fT := fun k => X.presheaf.map iW.op (f k)
  let zT := Construction.symmetricMap _ _ (X.presheaf.map iU.op).hom
    (sectionIdeal_map X J iU.op) n z
  have hfT := isGeneratedByOn_restrict X J W T iW f hgen
  obtain ⟨V, hxV, i, hi⟩ := exists_local_generatorWord_span X J T fT hfT n zT x ⟨hxU, hxW⟩
  let fV : Fin r → sectionIdeal X J (op V) := fun k =>
    ⟨X.presheaf.map i.op (fT k), J.toSubmodule.map_mem i.op
      (mem_of_isGeneratedByOn X J T fT hfT k)⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun
    (X.presheaf.obj (op V))).mp hi
  change (∑ t, c t • Construction.wordClass (sectionIdeal X J (op V)) n (fV ∘ t)) =
    Construction.symmetricMap _ _ (X.presheaf.map i.op).hom
      (sectionIdeal_map X J i.op) n zT at hc
  let g := QuasiRegular.germSequence (X.restrict W.isOpenEmbedding)
    (fun k => sectionOnRestriction X W (f k)) ⟨x, hxW⟩
  let φ := germInRestriction X W x hxW V hxV
  have hI : sectionIdeal X J (op V) ≤ (Jid g).comap φ := by
    intro s hs
    apply (germInRestriction_mem_span_iff X W x hxW f V hxV s).mpr
    exact germ_mem_span_of_isGeneratedByOn X J W V f hgen
      (leOfHom (i ≫ iW)) s hs x hxV
  have hfg : ∀ k, φ (fV k) = g k := by
    intro k
    show germInRestriction X W x hxW V hxV
      (X.presheaf.map i.op (X.presheaf.map iW.op (f k))) = _
    rw [germInRestriction_res X W x hxW V T hxV ⟨hxU, hxW⟩ i,
      germInRestriction_res X W x hxW T W ⟨hxU, hxW⟩ hxW iW,
      germInRestriction_self]
    rfl
  have hzV : Construction.canonicalMap (sectionIdeal X J (op V)) n
      (∑ t, c t • Construction.wordClass (sectionIdeal X J (op V)) n (fV ∘ t)) = 0 := by
    rw [hc, Construction.canonicalMap_naturality]
    show Construction.gradedMap _ _ _ _ n
      (Construction.canonicalMap _ n
        (Construction.symmetricMap _ _ _ _ n z)) = 0
    rw [Construction.canonicalMap_naturality, hz, map_zero, map_zero]
  have hp := tuplePolynomial_coeff_mem_of_canonicalMap_eq_zero
    (sectionIdeal X J (op V)) φ fV g hfg hI
    ((quasiRegularMap_isIso_iff _ _).mp hqr ⟨x, hxW⟩).1 c (by
      rw [Construction.canonicalMap_naturality, hzV, map_zero])
  let p := tuplePolynomial c
  have hp' (e : p.support) : ∃ (D : Opens X) (_ : x ∈ D) (j : D ⟶ V),
      X.presheaf.map j.op (p.coeff e) ∈ J.obj (op D) := by
    apply exists_local_mem_of_germ_mem_span X J W V f
      (mem_of_isGeneratedByOn X J W f hgen) _ x hxW hxV
    exact (germInRestriction_mem_span_iff X W x hxW f V hxV _).mp (hp e)
  choose D hxD j hj using hp'
  obtain ⟨E, hxE, hEV, hED⟩ := exists_common_open x V D hxV hxD
  let l : E ⟶ V := homOfLE hEV
  have hcoeff : ∀ e, (MvPolynomial.map (X.presheaf.map l.op).hom p).coeff e ∈
      sectionIdeal X J (op E) := by
    intro e
    rw [MvPolynomial.coeff_map]
    by_cases he : e ∈ p.support
    · have h := J.toSubmodule.map_mem (homOfLE (hED ⟨e, he⟩)).op (hj ⟨e, he⟩)
      change X.presheaf.map (homOfLE (hED ⟨e, he⟩)).op
        (X.presheaf.map (j ⟨e, he⟩).op (p.coeff e)) ∈ _ at h
      rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp] at h
      exact h
    · rw [MvPolynomial.notMem_support_iff.mp he, map_zero]
      exact Ideal.zero_mem _
  refine ⟨E, hxE, l ≫ i ≫ iU, ?_⟩
  have he := Construction.polynomialClass_eq_zero_of_coeff_mem
    (sectionIdeal X J (op E))
    (fun k => Construction.idealMap _ _ (X.presheaf.map l.op).hom
      (sectionIdeal_map X J l.op) (fV k)) n
    (MvPolynomial.map (X.presheaf.map l.op).hom p) hcoeff
  rw [← Construction.symmetricMap_polynomialClass,
    polynomialClass_tuplePolynomial, hc] at he
  simpa only [zT, symmetric_restrict_comp, Category.assoc] using he

section FreePresentation

universe w
variable {C : Type v} [Category.{w} C] {T : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf T RingCat.{u}}

noncomputable def constantFreeHomEquiv (N : PresheafOfModules.{u} R₀) (I : Type u) :
    (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I) ⟶ N) ≃ (I → N.sections) :=
  PresheafOfModules.freeHomEquiv.trans
    { toFun := fun f i => PresheafOfModules.sectionsMk (fun V => f.app V i)
        (fun {V W} j => (CategoryTheory.congr_fun (f.naturality j) i).symm)
      invFun := fun s =>
        { app := fun V => ↾fun i => (s i).val V
          naturality := fun V W j => by
            ext i
            exact ((s i).property j).symm }
      left_inv f := by
        ext V i
        rfl
      right_inv _ := rfl }

lemma constantFreeHomEquiv_apply (N : PresheafOfModules.{u} R₀) (I : Type u)
    (f : PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I) ⟶ N) (i : I) (V : Cᵒᵖ) :
    ((constantFreeHomEquiv N I f i).val V) = f.app V (ModuleCat.freeMk i) := rfl

noncomputable def freePresheafMap (α : R₀ ⟶ R.obj)
    (M : SheafOfModules.{u} R) {I : Type u} (s : I → M.sections) :
    PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I) ⟶
      (PresheafOfModules.restrictScalars α).obj M.val :=
  (constantFreeHomEquiv ((PresheafOfModules.restrictScalars α).obj M.val) I).symm s

lemma freePresheafMap_freeMk (α : R₀ ⟶ R.obj)
    (M : SheafOfModules.{u} R) {I : Type u} (s : I → M.sections) (V : Cᵒᵖ) (i : I) :
    (freePresheafMap α M s).app V (ModuleCat.freeMk i) = (s i).val V := by
  have h := congrArg (fun t => (t i).val V)
    ((constantFreeHomEquiv ((PresheafOfModules.restrictScalars α).obj M.val) I).apply_symm_apply s)
  exact h

lemma isIso_freeHomEquiv_of_locallyBijective
    [HasWeakSheafify T AddCommGrpCat.{u}] [T.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (α : R₀ ⟶ R.obj) [Presheaf.IsLocallySurjective T α]
    (M : SheafOfModules.{u} R) {I : Type u} (s : I → M.sections)
    [PresheafOfModules.IsLocallyInjective T (freePresheafMap α M s)]
    [PresheafOfModules.IsLocallySurjective T (freePresheafMap α M s)] :
    IsIso (M.freeHomEquiv.symm s) := by
  apply isIso_of_coyoneda_map_bijective
  intro N
  let e : (M ⟶ N) ≃ (I → N.sections) :=
    ((SheafOfModules.fullyFaithfulForget R).homEquiv.trans
      (PresheafOfModules.restrictHomEquivOfIsLocallySurjective α N.isSheaf)).trans
      ((PresheafOfModules.homEquivOfIsLocallyBijective
        (freePresheafMap α M s) N.isSheaf).trans
        (constantFreeHomEquiv ((PresheafOfModules.restrictScalars α).obj N.val) I))
  have he : (fun f : M ⟶ N => N.freeHomEquiv (M.freeHomEquiv.symm s ≫ f)) = e := by
    funext f i
    apply PresheafOfModules.sections_ext
    intro V
    show f.val.app V ((M.freeHomEquiv (M.freeHomEquiv.symm s) i).val V) =
      f.val.app V ((freePresheafMap α M s).app V (ModuleCat.freeMk i))
    rw [Equiv.apply_symm_apply, freePresheafMap_freeMk]
  have hb : Function.Bijective (fun f : M ⟶ N =>
      N.freeHomEquiv (M.freeHomEquiv.symm s ≫ f)) := by rw [he]; exact e.bijective
  exact (Function.Bijective.of_comp_iff' N.freeHomEquiv.bijective _).mp hb

/-- The unit of the sheafification of presheaves of modules is locally bijective: on
underlying presheaves of abelian groups it *is* `toSheafify`. -/
private lemma sheafificationUnit_locallyBijective
    [HasWeakSheafify T AddCommGrpCat.{u}] [T.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (α : R₀ ⟶ R.obj) [Presheaf.IsLocallyInjective T α] [Presheaf.IsLocallySurjective T α]
    (M₀ : PresheafOfModules.{u} R₀) :
    PresheafOfModules.IsLocallyInjective T
        ((PresheafOfModules.sheafificationAdjunction α).unit.app M₀) ∧
      PresheafOfModules.IsLocallySurjective T
        ((PresheafOfModules.sheafificationAdjunction α).unit.app M₀) := by
  constructor
  · dsimp only [PresheafOfModules.IsLocallyInjective]
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (T.W_toSheafify M₀.presheaf).isLocallyInjective
  · dsimp only [PresheafOfModules.IsLocallySurjective]
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (T.W_toSheafify M₀.presheaf).isLocallySurjective

/-- The comparison morphism from the free sheaf of modules on `I` to the sheafification of
the free presheaf of modules on the constant functor `I`. Mathlib defines
`SheafOfModules.free` as a coproduct of copies of `unit R` and relates it to no
presheaf-level free object, so this comparison is built by hand. -/
private noncomputable def freeSheafComparison
    [HasWeakSheafify T AddCommGrpCat.{u}] [T.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (α : R₀ ⟶ R.obj) [Presheaf.IsLocallyInjective T α] [Presheaf.IsLocallySurjective T α]
    (I : Type u) :
    SheafOfModules.free (R := R) I ⟶
      (PresheafOfModules.sheafification α).obj
        (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I)) :=
  ((PresheafOfModules.sheafification α).obj
      (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))).freeHomEquiv.symm
    (constantFreeHomEquiv ((PresheafOfModules.restrictScalars α).obj
        ((PresheafOfModules.sheafification α).obj
          (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))).val) I
      ((PresheafOfModules.sheafificationAdjunction α).unit.app
        (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))))

private lemma freeHomEquiv_freeSheafComparison
    [HasWeakSheafify T AddCommGrpCat.{u}] [T.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (α : R₀ ⟶ R.obj) [Presheaf.IsLocallyInjective T α] [Presheaf.IsLocallySurjective T α]
    (I : Type u) :
    ((PresheafOfModules.sheafification α).obj
        (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))).freeHomEquiv
      (freeSheafComparison α I) =
      constantFreeHomEquiv ((PresheafOfModules.restrictScalars α).obj
          ((PresheafOfModules.sheafification α).obj
            (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))).val) I
        ((PresheafOfModules.sheafificationAdjunction α).unit.app
          (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))) :=
  Equiv.apply_symm_apply _ _

private lemma freePresheafMap_freeSheafComparison
    [HasWeakSheafify T AddCommGrpCat.{u}] [T.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (α : R₀ ⟶ R.obj) [Presheaf.IsLocallyInjective T α] [Presheaf.IsLocallySurjective T α]
    (I : Type u) :
    freePresheafMap α ((PresheafOfModules.sheafification α).obj
        (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I)))
      (((PresheafOfModules.sheafification α).obj
        (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))).freeHomEquiv
          (freeSheafComparison α I)) =
      (PresheafOfModules.sheafificationAdjunction α).unit.app
        (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I)) := by
  rw [freeHomEquiv_freeSheafComparison]
  exact (constantFreeHomEquiv _ I).symm_apply_apply _

private instance isIso_freeSheafComparison
    [HasWeakSheafify T AddCommGrpCat.{u}] [T.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (α : R₀ ⟶ R.obj) [Presheaf.IsLocallyInjective T α] [Presheaf.IsLocallySurjective T α]
    (I : Type u) : IsIso (freeSheafComparison α I) := by
  obtain ⟨h₁, h₂⟩ := sheafificationUnit_locallyBijective α
    (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))
  rw [← freePresheafMap_freeSheafComparison α I] at h₁ h₂
  have hiso := @isIso_freeHomEquiv_of_locallyBijective _ _ _ _ _ _ _ α _
    ((PresheafOfModules.sheafification α).obj
      (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I)))
    _ (((PresheafOfModules.sheafification α).obj
      (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))).freeHomEquiv
        (freeSheafComparison α I)) h₁ h₂
  rwa [Equiv.symm_apply_apply] at hiso

/-- **The converse of `isIso_freeHomEquiv_of_locallyBijective`.** For any family of
sections `s` of a sheaf of modules, the presheaf-level map `freePresheafMap α M s` factors
as the (locally bijective) sheafification unit followed by the restriction of scalars of
the sheaf-level map `M.freeHomEquiv.symm s` transported along the comparison. Hence an
`IsIso` at the sheaf level forces local bijectivity at the presheaf level. -/
private lemma freePresheafMap_eq_unit_comp
    [HasWeakSheafify T AddCommGrpCat.{u}] [T.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (α : R₀ ⟶ R.obj) [Presheaf.IsLocallyInjective T α] [Presheaf.IsLocallySurjective T α]
    (M : SheafOfModules.{u} R) {I : Type u} (s : I → M.sections) :
    freePresheafMap α M s =
      (PresheafOfModules.sheafificationAdjunction α).unit.app
          (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I)) ≫
        (PresheafOfModules.restrictScalars α).map
          (inv (freeSheafComparison α I) ≫ M.freeHomEquiv.symm s).val := by
  apply (constantFreeHomEquiv _ I).injective
  funext i
  apply PresheafOfModules.sections_ext
  intro V
  have h1 : SheafOfModules.sectionsMap (inv (freeSheafComparison α I))
      (((PresheafOfModules.sheafification α).obj
        (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))).freeHomEquiv
          (freeSheafComparison α I) i) = SheafOfModules.freeSection i := by
    rw [SheafOfModules.freeHomEquiv_apply, ← SheafOfModules.sectionsMap_comp,
      IsIso.hom_inv_id, SheafOfModules.sectionsMap_id]
  have hti : SheafOfModules.sectionsMap
      (inv (freeSheafComparison α I) ≫ M.freeHomEquiv.symm s)
      (((PresheafOfModules.sheafification α).obj
        (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))).freeHomEquiv
          (freeSheafComparison α I) i) = s i := by
    rw [SheafOfModules.sectionsMap_comp, h1]
    exact SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s i
  rw [constantFreeHomEquiv_apply, constantFreeHomEquiv_apply, freePresheafMap_freeMk,
    ← hti, freeHomEquiv_freeSheafComparison]
  rfl

/-- **From an `IsIso` at the sheaf level to local bijectivity at the presheaf level.**
This is the converse of `isIso_freeHomEquiv_of_locallyBijective`, and the inversion of
Mathlib's free-sheaf packaging that `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`
has to be read through. The proof runs the factorisation through `GrothendieckTopology.W`, where
composition is a statement about isomorphisms, rather than through the local
injectivity and surjectivity classes. -/
lemma freePresheafMap_locallyBijective_of_isIso
    [HasWeakSheafify T AddCommGrpCat.{u}] [T.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (α : R₀ ⟶ R.obj) (hαi : Presheaf.IsLocallyInjective T α)
    (hαs : Presheaf.IsLocallySurjective T α)
    (M : SheafOfModules.{u} R) {I : Type u} (s : I → M.sections)
    (h : IsIso (M.freeHomEquiv.symm s)) :
    PresheafOfModules.IsLocallyInjective T (freePresheafMap α M s) ∧
      PresheafOfModules.IsLocallySurjective T (freePresheafMap α M s) := by
  have := hαi
  have := hαs
  have hπ := h
  have hθ : IsIso (inv (freeSheafComparison α I) ≫ M.freeHomEquiv.symm s) := inferInstance
  have hval : IsIso (inv (freeSheafComparison α I) ≫ M.freeHomEquiv.symm s).val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget R).map
      (inv (freeSheafComparison α I) ≫ M.freeHomEquiv.symm s)))
  have hg : IsIso ((PresheafOfModules.restrictScalars α).map
      (inv (freeSheafComparison α I) ≫ M.freeHomEquiv.symm s).val) := inferInstance
  have hgp : IsIso ((PresheafOfModules.toPresheaf R₀).map
      ((PresheafOfModules.restrictScalars α).map
        (inv (freeSheafComparison α I) ≫ M.freeHomEquiv.symm s).val)) := inferInstance
  have hgs : IsIso ((CategoryTheory.presheafToSheaf T AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf R₀).map
        ((PresheafOfModules.restrictScalars α).map
          (inv (freeSheafComparison α I) ≫ M.freeHomEquiv.symm s).val))) := inferInstance
  have hus : IsIso ((CategoryTheory.presheafToSheaf T AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf R₀).map
        ((PresheafOfModules.sheafificationAdjunction α).unit.app
          (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I))))) :=
    (T.W_iff _).mp (T.W_toSheafify
      (PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I)).presheaf)
  have hW : T.W ((PresheafOfModules.toPresheaf R₀).map (freePresheafMap α M s)) := by
    rw [freePresheafMap_eq_unit_comp α M s, Functor.map_comp, T.W_iff, Functor.map_comp]
    exact IsIso.comp_isIso' hus hgs
  exact ⟨GrothendieckTopology.W.isLocallyInjective hW,
    GrothendieckTopology.W.isLocallySurjective hW⟩

end FreePresentation

end Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

end
