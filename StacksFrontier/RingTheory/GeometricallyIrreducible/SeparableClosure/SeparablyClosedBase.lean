module

public import StacksFrontier.RingTheory.GeometricallyIrreducible.SeparableClosure.AlgClosedBase
import StacksCore.Tactic.EgaSgaAttribute

/-! # Geometric irreducibility over a separably closed subfield

The perfect-closure reduction, irreducibility of `Spec (K ⊗[F] L)` when `F` is separably
closed in `K`, and its consequence for the separable closure of `k` in `K` with test fields in
`Type` (Stacks 037Q (1) in the universe `0`; the 037L form in every universe is
`separableClosure.isGeometricallyIrreducible`). -/

@[expose] public section

open scoped TensorProduct

--
-- ════════════════════════════════════════════════════════════════════════════════════
-- (SL-2/AC-MIG decomposition).  The perfect-closure migration (informal A1 + A3 + ★ + R3)
-- is split into TWO acyclic sub-lemmas with open goals, placed before the MIG assembly:
--   • MIG-FG `tensorAlgClosed_perfectBase_irreducible_fg`: the FINITELY-GENERATED case
--     (`L/Ls` f.g.).  This is the genuine analytic content: base-change iso ★
--     `Ē ⊗[Ls] L ≅ Ē ⊗[P] (P ⊗[Ls] L)`; the purely-inseparable kernel K1 makes `T := P ⊗[Ls] L`
--     have irreducible Spec with reduced quotient a field `L'` f.g. + separably closed over the
--     PERFECT `P` (A1); the nil-kernel base change `Ē ⊗[P] T → Ē ⊗[P] L'` is a Spec homeomorphism
--     (A3); conclude via `hA2` (so it is strictly an assembly of A2, never reproves it).
--   • MIG-R3 `tensorAlgClosed_perfectBase_irreducible_colimit`: the DIRECTED-COLIMIT reduction
--     from a general `L/Ls` to its finitely generated sub-`Ls`-extensions.  `hsc` descends to
--     every f.g. subfield; irreducibility (nilradical prime) passes through filtered colimits.
--     It CONSUMES MIG-FG (applied to each f.g. subfield `Lᵢ` with the descended `hscᵢ`).
-- MIG is then the application of MIG-R3 supplying MIG-FG.  BOTH stubs must close.
--
-- ⚠️ UNIVERSE FIX: `hA2`'s field `L'` is pinned to `Type (max uEbar uL)` (NOT `Type` and NOT a
-- bare `Type*`, both of which fail: `Type` is too small for the reduced quotient `T_red` of
-- `P ⊗[Ls] L` which lives in `max uEbar uL`; a bare `Type*` introduces an unconstrained universe
-- metavariable in the SL-2/AC supplier).  The supplier A2 is `Type*`-polymorphic so it satisfies
-- the pinned binder.
universe uLs uEbar uL
--
/-- (H-A3) A surjective ring homomorphism whose kernel lies inside the nilradical transfers
`Spec` irreducibility from the codomain to the domain. This is the reusable A3 transfer
mechanism; it also subsumes ★, since a ring isomorphism is a surjection whose zero kernel lies
in the nilradical. -/
theorem irreducibleSpace_of_surjective_nilKer {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hsurj : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical A)
    (hB : IrreducibleSpace (PrimeSpectrum B)) : IrreducibleSpace (PrimeSpectrum A) := by
  have hbij := PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hker
  let e : (A ⧸ RingHom.ker f) ≃+* B := RingHom.quotientKerEquivOfSurjective hsurj
  have hb2 : Function.Surjective
      (PrimeSpectrum.comap (e.toRingHom : (A ⧸ RingHom.ker f) →+* B)) := by
    intro x
    refine ⟨PrimeSpectrum.comap e.symm.toRingHom x, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply]; simp
  have hcomp : Function.Surjective
      (PrimeSpectrum.comap (Ideal.Quotient.mk (RingHom.ker f)) ∘ PrimeSpectrum.comap e.toRingHom) :=
    hbij.right.comp hb2
  have heq : (PrimeSpectrum.comap (Ideal.Quotient.mk (RingHom.ker f)) ∘ PrimeSpectrum.comap
      e.toRingHom)
      = PrimeSpectrum.comap f := by rw [← PrimeSpectrum.comap_comp]; congr 1
  rw [heq] at hcomp
  exact Function.Surjective.irreducibleSpace (PrimeSpectrum.continuous_comap _) hcomp

/-- Tensoring with the identity on the left factor is `LinearMap.lTensor`. -/
private theorem toLinearMap_map_id_eq_lTensor {R S A B D : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [CommRing D] [Algebra R S] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Algebra R B] [Algebra R D] (g : B →ₐ[R] D) :
    (Algebra.TensorProduct.map (AlgHom.id S A) g).toLinearMap = LinearMap.lTensor A g.toLinearMap :=
  rfl

-- needed: `perfectBase_fg_assemble`'s `simp [AlgHom.toRingHom_eq_coe]` step needs
-- `g.toLinearMap x` and `g x` accepted as defeq.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
-- needed: `perfectBase_fg_assemble` exhausts the default elaboration budget (whnf
-- timeout), and its instance search exceeds the default instance-search budget
set_option synthInstance.maxHeartbeats 50000 in
/-- The ★ and A3 base-change descent.

MIG-FG is decomposed into two acyclic sub-lemmas plus an assembly. First, MIG-FG-A1
`perfectBase_reducedQuotient_field`: the genuine analytic content — the reduced quotient `T_red
:= (P ⊗[Ls] L) ⧸ nilradical ·` is a FIELD `L'`, finitely generated and separably closed over
the PERFECT `P := ↥(perfectClosure Ls Ebar)`, with a surjective `P`-algebra hom `g : P ⊗[Ls] L
→ₐ[P] L'` whose kernel sits in the nilradical. • MIG-FG-ASM `perfectBase_fg_assemble`: the ★ +
A3 base-change descent — given such a surjection `g` with nil kernel onto a field `L'` and
`IsDomain (Ebar ⊗[P] L')`, the space `Spec(Ebar ⊗[Ls] L)` is irreducible. (Internally: ★ `Ebar
⊗[Ls] L ≅ Ebar ⊗[P] (P ⊗[Ls] L)` via `cancelBaseChange`, then flat base change of `g` keeps the
kernel nil ⟹ H-A3.) ⚠️ The nested tensor `Ebar ⊗[P] (P ⊗[Ls] L)` is kept INSIDE this lemma's
proof (where the `Semiring`/`CommRing` synthesis diamond for the nested tensor must be resolved
with explicit `letI rightAlgebra` instances — see META "abstract-Ls double-tensor regrouping");
it does NOT appear in any statement, so MIG-FG elaborates cleanly. MIG-FG then = obtain A1,
feed `hA2` (using the A1 f.g. + sep-closed facts) for the domain, ASM. -/
theorem perfectBase_fg_assemble
    (Ls : Type uLs) [Field Ls] (Ebar : Type uEbar) [Field Ebar] [Algebra Ls Ebar] [IsAlgClosed Ebar]
    (L : Type uL) [Field L] [Algebra Ls L]
    (L' : Type (max uEbar uL)) [Field L'] [Algebra (↥(perfectClosure Ls Ebar)) L']
    (g : ((↥(perfectClosure Ls Ebar)) ⊗[Ls] L) →ₐ[↥(perfectClosure Ls Ebar)] L')
    (hsurj : Function.Surjective g)
    (hker : RingHom.ker g.toRingHom ≤ nilradical ((↥(perfectClosure Ls Ebar)) ⊗[Ls] L))
    (hdom : IsDomain (Ebar ⊗[↥(perfectClosure Ls Ebar)] L')) :
    IrreducibleSpace (PrimeSpectrum (Ebar ⊗[Ls] L)) := by
  -- ★ (cancelBaseChange) + flat base change of `g` (kernel stays nil) + H-A3 + hdom.
  set P := ↥(perfectClosure Ls Ebar) with hP
  have estar := Algebra.TensorProduct.cancelBaseChange Ls P Ebar Ebar L
  let gM := Algebra.TensorProduct.map (AlgHom.id Ebar Ebar) g
  let g2 := gM.comp estar.symm.toAlgHom
  have : IsDomain (Ebar ⊗[P] L') := hdom
  have hBirr : IrreducibleSpace (PrimeSpectrum (Ebar ⊗[P] L')) := PrimeSpectrum.irreducibleSpace
  have hgMsurj : Function.Surjective gM :=
    (toLinearMap_map_id_eq_lTensor (S := Ebar) (A := Ebar) g ▸
      LinearMap.lTensor_surjective Ebar hsurj :)
  have hg2surj : Function.Surjective g2 := hgMsurj.comp estar.symm.surjective
  -- flatness of `Ebar` over `P` gives an exact sequence after `Ebar ⊗[P] -`
  have : Module.Flat P Ebar := inferInstance
  have hExact : Function.Exact ((LinearMap.ker g.toLinearMap).subtype) g.toLinearMap :=
    LinearMap.exact_subtype_ker_map g.toLinearMap
  have hExactE := Module.Flat.lTensor_exact Ebar hExact
  have hgMeq : gM.toLinearMap = LinearMap.lTensor Ebar g.toLinearMap :=
    toLinearMap_map_id_eq_lTensor g
  -- `estar`-images of the kernel generators are nilpotent (computed in the clean ring `Ebar ⊗[Ls]
  -- L`)
  have hgen : ∀ v,
      IsNilpotent (estar (LinearMap.lTensor Ebar (LinearMap.ker g.toLinearMap).subtype v)) := by
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul e x =>
        rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
        have hxnil : IsNilpotent ((x : P ⊗[Ls] L)) := by
          apply hker
          have hx2 : g.toLinearMap (x : P ⊗[Ls] L) = 0 := x.property
          simp [AlgHom.toRingHom_eq_coe]
        obtain ⟨n, hn⟩ := hxnil
        refine IsNilpotent.map ?_ estar.toRingHom
        refine ⟨n, ?_⟩
        rw [Algebra.TensorProduct.tmul_pow, hn]
        simp
    | add a b ha hb =>
        simp only [map_add]
        exact Commute.isNilpotent_add (Commute.all _ _) ha hb
  -- hence the kernel of the transported map sits inside the nilradical
  have hker2 : RingHom.ker g2.toRingHom ≤ nilradical (Ebar ⊗[Ls] L) := by
    intro u hu
    rw [RingHom.mem_ker] at hu
    have hu0 : gM (estar.symm u) = 0 := hu
    have hwk : LinearMap.lTensor Ebar g.toLinearMap (estar.symm u) = 0 := by
      rw [← hgMeq]; exact hu0
    obtain ⟨v, hv⟩ := (hExactE (estar.symm u)).mp hwk
    rw [mem_nilradical]
    have hue : u = estar (estar.symm u) := by rw [AlgEquiv.apply_symm_apply]
    rw [hue, ← hv]
    exact hgen v
  exact irreducibleSpace_of_surjective_nilKer g2.toRingHom hg2surj hker2 hBirr
--
-- (MIG-FG-A1) THE GENUINE ANALYTIC KERNEL.
-- `P := ↥(perfectClosure Ls Ebar)` PERFECT, purely inseparable over `Ls`; `L/Ls` f.g. with
-- `separableClosure Ls L = ⊥`.  Set `T := P ⊗[Ls] L`.  By K1
-- (`irreducibleSpace_baseChange_purelyInseparable`, with `L ⊗[Ls] P` + `comm`) `Spec T` is
-- irreducible ⟹ `nilradical T` prime ⟹ `T_red := T ⧸ nilradical T` is a DOMAIN.  The global
-- Frobenius (every `t : T` has `t ^ (q^n)` in the image of `1 ⊗ L`) makes `T_red` integral over
-- the field `L`, hence a FIELD `L'` (`Algebra.IsIntegral.isField_iff_isField`), with `L'/L`
-- purely inseparable; `L'/P` finitely generated (= `P` adjoin the images of the `hfgL` gens) and
-- `separableClosure P L' = ⊥`.  Output: the field `L'`, its `P`-algebra structure, and the
-- surjective `P`-algebra hom `g : T →ₐ[P] L'` with kernel ⊆ `nilradical T`.
-- ⚠️ UNIVERSE: `L'` is pinned to `Type (max uEbar uL)` (= `T`'s universe, since `P ⊆ Ebar`) so the
-- supplier `hA2` (relaxed to that universe) is satisfiable and no universe metavariable arises.
-- ════════════════════════════════════════════════════════════════════════════════════
-- (MIG-FG-A1) SUPPORTING LEMMAS for `perfectBase_reducedQuotient_field`.  Each is FULLY PROVED.
--
-- A1.a: a reduced quotient `T ⧸ nilradical T` of an `L`-algebra `T` (L a field) where every
-- element of `T` has some `q`-power in the image of `L`, with `nilradical T` prime, is a FIELD
-- (it is integral over the field `L`, and an integral domain extension that is a field iff the
-- base is — `Algebra.IsIntegral.isField_iff_isField`).
/-- If every element of an `L`-algebra `T` has some `q`-power in the image of `L`, and the
nilradical of `T` is prime, then `T ⧸ nilradical T` is a field. -/
theorem reducedQuotient_isField_of_qpow
    (L : Type*) [Field L] (T : Type*) [CommRing T] [Algebra L T]
    (q : ℕ) (hq : 1 ≤ q)
    (hkey : ∀ t : T, ∃ n : ℕ, t ^ (q ^ n) ∈ (algebraMap L T).range)
    [hprime : (nilradical T).IsPrime] :
    IsField (T ⧸ nilradical T) := by
  set N := nilradical T with hN
  have : N.IsPrime := hprime
  have : IsDomain (T ⧸ N) := Ideal.Quotient.isDomain N
  have hinj : Function.Injective (algebraMap L (T ⧸ N)) :=
    (algebraMap L (T ⧸ N)).injective
  have : Algebra.IsIntegral L (T ⧸ N) := by
    constructor
    intro x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨n, a, ha⟩ := hkey t
    refine ⟨Polynomial.X ^ (q ^ n) - Polynomial.C a, ?_, ?_⟩
    · apply Polynomial.monic_X_pow_sub_C
      exact (Nat.one_le_iff_ne_zero).mp (Nat.one_le_pow _ _ hq)
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      have : (Ideal.Quotient.mk N) t ^ (q ^ n) = algebraMap L (T ⧸ N) a := by
        rw [← map_pow]
        change (Ideal.Quotient.mk N) (t ^ (q^n)) = (Ideal.Quotient.mk N) (algebraMap L T a)
        rw [ha]
      rw [this]; ring
  exact (Algebra.IsIntegral.isField_iff_isField hinj).mp (Field.toIsField L)

/-- A1.b: global Frobenius into the right factor. If `P/Ls` is purely inseparable with exponential
char `q`, every element of `P ⊗[Ls] L` has a `q`-power in the image of `algebraMap L (P ⊗ L)`
(= `1 ⊗ L`). This is the K1-mirror with the roles of the two tensor factors swapped. -/
theorem tensor_qpow_mem_rightRange
    (Ls : Type*) [Field Ls] (P : Type*) [Field P] [Algebra Ls P] [IsPurelyInseparable Ls P]
    (L : Type*) [Field L] [Algebra Ls L]
    (q : ℕ) [ExpChar Ls q] :
    letI : Algebra L (P ⊗[Ls] L) := Algebra.TensorProduct.rightAlgebra
    ∀ z : P ⊗[Ls] L, ∃ n : ℕ, z ^ (q ^ n) ∈ (algebraMap L (P ⊗[Ls] L)).range := by
  let : Algebra L (P ⊗[Ls] L) := Algebra.TensorProduct.rightAlgebra
  set R := P ⊗[Ls] L with hR
  have hqne : q ≠ 0 := (expChar_pos Ls q).ne'
  have e1 : ∀ (l : L), (algebraMap L R) l = 1 ⊗ₜ[Ls] l := fun l => rfl
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b x =>
      obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem Ls q b
      refine ⟨n, c • x ^ (q ^ n), ?_⟩
      rw [Algebra.TensorProduct.tmul_pow, ← hc, e1,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add z w hz hw =>
      obtain ⟨nz, hnz⟩ := hz
      obtain ⟨nw, hnw⟩ := hw
      refine ⟨max nz nw, ?_⟩
      have : ExpChar R q := expChar_of_injective_ringHom (algebraMap Ls R).injective q
      have hmono : ∀ (u : R) (k m : ℕ), u ^ (q ^ k) ∈ (algebraMap L R).range → k ≤ m →
          u ^ (q ^ m) ∈ (algebraMap L R).range := fun u k m hk hkm => by
        rw [show u ^ (q ^ m) = (u ^ (q ^ k)) ^ (q ^ (m - k)) by
          rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hkm]]
        exact Subring.pow_mem _ hk _
      have hadd : (z + w) ^ (q ^ (max nz nw))
          = z ^ (q ^ (max nz nw)) + w ^ (q ^ (max nz nw)) := by
        have := (iterateFrobenius R q (max nz nw)).map_add z w
        simpa [iterateFrobenius_def] using this
      rw [hadd]
      refine Subring.add_mem _ ?_ ?_
      · exact hmono z nz _ hnz (le_max_left _ _)
      · exact hmono w nw _ hnw (le_max_right _ _)

/-- A1.c: a ring isomorphism transports primality of the nilradical. -/
theorem nilradicalIsPrime_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (hB : (nilradical B).IsPrime) : (nilradical A).IsPrime := by
  have h1 : nilradical A = Ideal.comap (e : A →+* B) (nilradical B) := by
    rw [nilradical, nilradical, Ideal.comap_radical]
    congr 1
    rw [show (0 : Ideal A) = ⊥ from rfl, show (0 : Ideal B) = ⊥ from rfl]
    exact (Ideal.comap_bot_of_injective (e : A →+* B) e.injective).symm
  rw [h1]
  exact Ideal.IsPrime.comap _

/-- A1.d: finite generation of `⊤` is preserved by a `P`-spanning ring hom from a field `L` that is
f.g. over `Ls`. (The field `L'` is `P`-spanned by `φ(L)`; the subfield `adjoin P (φ '' s)`
already contains `φ(L)`, since `φ⁻¹` of it is an `Ls`-subfield containing the generators `s`.) -/
theorem fg_top_of_span_adjoin
    (Ls : Type*) [Field Ls] (P : Type*) [Field P] [Algebra Ls P]
    (L : Type*) [Field L] [Algebra Ls L]
    (L' : Type*) [Field L'] [Algebra P L']
    (φ : L →+* L')
    (s : Finset L) (hs : IntermediateField.adjoin Ls (s : Set L) = ⊤)
    (hLs : ∀ c : Ls, φ (algebraMap Ls L c) ∈ Set.range (algebraMap P L'))
    (hspan : Submodule.span P (Set.range φ) = ⊤) :
    (⊤ : IntermediateField P L').FG := by
  classical
  refine ⟨s.image φ, ?_⟩
  set K := IntermediateField.adjoin P ((s.image φ : Finset L') : Set L') with hK
  have hsK : (φ '' (s : Set L)) ⊆ (K : Set L') := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply IntermediateField.subset_adjoin
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨x, hx, rfl⟩
  have hφL : ∀ l : L, φ l ∈ K := by
    have hcomap :
        (IntermediateField.adjoin Ls (s : Set L)).toSubfield ≤ Subfield.comap φ K.toSubfield := by
      apply IntermediateField.adjoin_le_subfield
      · intro y hy
        obtain ⟨c, rfl⟩ := hy
        simp only [SetLike.mem_coe, Subfield.mem_comap]
        obtain ⟨p, hp⟩ := hLs c
        rw [← hp]
        exact K.algebraMap_mem p
      · intro y hy
        simp only [SetLike.mem_coe, Subfield.mem_comap]
        exact hsK ⟨y, hy, rfl⟩
    rw [hs] at hcomap
    intro l
    have : l ∈ Subfield.comap φ K.toSubfield := hcomap (by trivial)
    rwa [Subfield.mem_comap] at this
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Submodule.span P (Set.range φ) := by rw [hspan]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨l, rfl⟩; exact hφL l
  · exact zero_mem _
  · intro a b _ _ ha hb; exact add_mem ha hb
  · intro p a _ ha; exact Submodule.smul_mem K.toSubmodule p ha

/-- A1.e: `L'` (= surjective `P`-algebra image of `P ⊗[Ls] L`) is `P`-spanned by the images of `1 ⊗
L`. -/
theorem span_range_includeRight_map_eq_top
    (Ls : Type*) [Field Ls] (P : Type*) [Field P] [Algebra Ls P]
    (L : Type*) [Field L] [Algebra Ls L]
    (L' : Type*) [CommRing L'] [Algebra P L']
    (g : (P ⊗[Ls] L) →ₐ[P] L') (hg : Function.Surjective g) :
    Submodule.span P (Set.range (fun l : L => g (1 ⊗ₜ[Ls] l))) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := hg y
  induction t using TensorProduct.inductionOn with
  | tmul p l =>
      have hpt : (p ⊗ₜ[Ls] l : P ⊗[Ls] L) = p • (1 ⊗ₜ[Ls] l) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hpt, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  | add a b ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb

/-- (MIG-DESC) descent of `separableClosure Ls · = ⊥` to a sub-`Ls`-field `↥M` of `L`. A
separable-algebraic element of `↥M` over `Ls` is separable-algebraic in `L` over `Ls` (its
`Ls`-minimal polynomial is the same), hence lies in `separableClosure Ls L = ⊥ = Ls`. -/
theorem separableClosure_eq_bot_of_le
    (Ls : Type*) [Field Ls] (L : Type*) [Field L] [Algebra Ls L]
    (hsc : separableClosure Ls L = ⊥) (M : IntermediateField Ls L) :
    separableClosure Ls ↥M = ⊥ := by
  refine eq_bot_iff.mpr (fun x hx => ?_)
  rw [mem_separableClosure_iff] at hx
  have hsep : IsSeparable Ls (M.val x) := hx.map M.val M.val.injective
  have hmem : M.val x ∈ separableClosure Ls L := by
    rw [mem_separableClosure_iff]; exact hsep
  rw [hsc, IntermediateField.mem_bot] at hmem
  obtain ⟨y, hy⟩ := hmem
  rw [IntermediateField.mem_bot]
  refine ⟨y, M.val.injective ?_⟩
  have : M.val (algebraMap Ls ↥M y) = M.val x := by
    rw [M.val.commutes y]; exact hy
  exact this

open IntermediateField in
/-- If the separable closure of `Ls` in `L` is trivial and `l ∈ L` is integral over `Ls`, then
some `q`-power of `l` lies in the image of `Ls`, where `q` is the exponential characteristic. -/
theorem qpow_mem_of_integral_sepBot
    (Ls : Type*) [Field Ls] (L : Type*) [Field L] [Algebra Ls L]
    (hsc : separableClosure Ls L = ⊥) (q : ℕ) [ExpChar Ls q]
    (l : L) (halg : IsIntegral Ls l) :
    ∃ b, l ^ (q ^ b) ∈ (algebraMap Ls L).range := by
  have : Algebra.IsAlgebraic Ls ↥Ls⟮l⟯ := IntermediateField.isAlgebraic_adjoin_simple halg
  have hscM : separableClosure Ls ↥Ls⟮l⟯ = ⊥ := separableClosure_eq_bot_of_le Ls L hsc Ls⟮l⟯
  have : IsPurelyInseparable Ls ↥Ls⟮l⟯ := (separableClosure.eq_bot_iff).mp hscM
  obtain ⟨b, c, hc⟩ := IsPurelyInseparable.pow_mem Ls q (IntermediateField.AdjoinSimple.gen Ls l)
  refine ⟨b, c, ?_⟩
  have hmap :
      (algebraMap (↥Ls⟮l⟯) L) ((IntermediateField.AdjoinSimple.gen Ls l) ^ (q ^ b))
        = l ^ (q ^ b) := by
    rw [map_pow, IntermediateField.AdjoinSimple.algebraMap_gen]
  rw [← hmap, ← hc, ← IsScalarTower.algebraMap_apply Ls (↥Ls⟮l⟯) L c]

/-- A1.g: over a PERFECT field `P` (exp char `q`), any element of an extension with a `q`-power in
`P` already lies in `P` (Frobenius is bijective on `P`, injective on the extension). -/
theorem qpow_mem_imp_mem_of_perfect
    (P : Type*) [Field P] [PerfectField P] (E : Type*) [Field E] [Algebra P E]
    (q : ℕ) [ExpChar P q] (x : E)
    (M : ℕ) (hp : x ^ (q ^ M) ∈ (algebraMap P E).range) :
    x ∈ (algebraMap P E).range := by
  have : ExpChar E q := expChar_of_injective_ringHom (algebraMap P E).injective q
  have : PerfectRing P q := PerfectField.toPerfectRing q
  obtain ⟨p, hp⟩ := hp
  obtain ⟨y, hy⟩ := (iterateFrobeniusEquiv P q M).surjective p
  rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at hy
  refine ⟨y, ?_⟩
  have h2 : x ^ (q ^ M) = (algebraMap P E y) ^ (q ^ M) := by
    rw [← hp, ← hy, map_pow]
  have hinj : Function.Injective (iterateFrobenius E q M) :=
    (iterateFrobenius E q M).injective
  apply hinj
  rw [iterateFrobenius_def, iterateFrobenius_def, ← h2]

/-- A1.h: THE separable-closure crux of Stacks 037Q. `separableClosure P L' = ⊥`. An element `x`
separable over the PERFECT `P` is integral over `P`; by global Frobenius (A1.b + surjective
`g`) some `x^(q^a) = ψ(l)` with `l ∈ L`; `l` is integral over `Ls`; by `hsc` it is purely
inseparable over `Ls`, so `l^(q^b) ∈ Ls`, whence `x^(q^(a+b)) ∈ P`; perfectness (A1.g) forces
`x ∈ P`. -/
theorem perfectBase_reducedQuotient_sepClosed
    (Ls : Type*) [Field Ls] (P : Type*) [Field P] [Algebra Ls P]
    [IsPurelyInseparable Ls P] [PerfectField P]
    (L : Type*) [Field L] [Algebra Ls L]
    (hsc : separableClosure Ls L = ⊥)
    (L' : Type*) [Field L'] [Algebra P L']
    (g : (P ⊗[Ls] L) →ₐ[P] L')
    (hsurj : Function.Surjective g) :
    separableClosure P L' = ⊥ := by
  obtain ⟨q, hq⟩ := ExpChar.exists Ls
  have : ExpChar Ls q := hq
  have : ExpChar P q := expChar_of_injective_ringHom (algebraMap Ls P).injective q
  let instLalg : Algebra L (P ⊗[Ls] L) := Algebra.TensorProduct.rightAlgebra
  let instLsL' : Algebra Ls L' := ((algebraMap P L').comp (algebraMap Ls P)).toAlgebra
  have : IsScalarTower Ls P L' := IsScalarTower.of_algebraMap_eq (fun c => rfl)
  set ψ : L →ₐ[Ls] L' := (g.restrictScalars Ls).comp Algebra.TensorProduct.includeRight with hψ
  let instLL' : Algebra L L' := ψ.toRingHom.toAlgebra
  have hstLL' : IsScalarTower Ls L L' :=
    IsScalarTower.of_algebraMap_eq fun c => (AlgHom.commutes ψ c).symm
  have hPint : Algebra.IsIntegral Ls P := inferInstance
  have hLalgmap : (algebraMap L L') = (ψ : L →+* L') := rfl
  have hpiLL' : ∀ x : L', ∃ a : ℕ, x ^ (q ^ a) ∈ (algebraMap L L').range := by
    intro x
    obtain ⟨t, rfl⟩ := hsurj x
    obtain ⟨a, ht⟩ := tensor_qpow_mem_rightRange Ls P L q t
    refine ⟨a, ?_⟩
    obtain ⟨l, hl⟩ := ht
    refine ⟨l, ?_⟩
    rw [hLalgmap]
    change ψ l = g t ^ (q ^ a)
    rw [hψ]
    change (g.restrictScalars Ls) (Algebra.TensorProduct.includeRight l) = g t ^ (q ^ a)
    rw [← map_pow]
    change g (Algebra.TensorProduct.includeRight l) = g (t ^ (q ^ a))
    have hcast : (Algebra.TensorProduct.includeRight l : P ⊗[Ls] L) = t ^ (q ^ a) := hl
    rw [hcast]
  rw [eq_bot_iff]
  intro x hx
  rw [mem_separableClosure_iff] at hx
  have hxint : IsIntegral P x := hx.isIntegral
  obtain ⟨a, l, hl⟩ := hpiLL' x
  have hxqa : x ^ (q ^ a) = algebraMap L L' l := hl.symm
  have hint1 : IsIntegral P (x ^ (q ^ a)) := hxint.pow _
  have hint2 : IsIntegral Ls (x ^ (q ^ a)) := isIntegral_trans _ hint1
  rw [hxqa] at hint2
  have hlLs : IsIntegral Ls l :=
    IsIntegral.tower_bot (A := L) (B := L') (by rw [hLalgmap]; exact ψ.injective) hint2
  obtain ⟨b, c, hc⟩ := qpow_mem_of_integral_sepBot Ls L hsc q l hlLs
  have hxP : x ^ (q ^ (a + b)) ∈ (algebraMap P L').range := by
    refine ⟨algebraMap Ls P c, ?_⟩
    have e : x ^ (q ^ (a + b)) = (x ^ (q ^ a)) ^ (q ^ b) := by
      rw [← pow_mul, ← pow_add]
    rw [e, hxqa, ← map_pow, ← hc, hLalgmap]
    change algebraMap P L' (algebraMap Ls P c) = ψ (algebraMap Ls L c)
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply Ls P L' c]
  rw [IntermediateField.mem_bot]
  exact qpow_mem_imp_mem_of_perfect P L' q x (a + b) hxP

/-- (MIG-FG-A1, abstract form) The genuine analytic kernel, stated over an arbitrary PERFECT base
`P` that is purely inseparable over `Ls`, with the irreducibility of `Spec (L ⊗[Ls] P)`
supplied as a hypothesis (provided by K1). Keeping `P` abstract (not `↥(perfectClosure Ls
Ebar)`) makes all the tensor/quotient instance synthesis fast. FULLY PROVED. -/
theorem perfectBase_reducedQuotient_field_abstract
    (Ls : Type uLs) [Field Ls] (P : Type uEbar) [Field P] [Algebra Ls P]
    [IsPurelyInseparable Ls P] [PerfectField P]
    (L : Type uL) [Field L] [Algebra Ls L]
    (hfgL : (⊤ : IntermediateField Ls L).FG)
    (hsc : separableClosure Ls L = ⊥)
    (hirrLP : IrreducibleSpace (PrimeSpectrum (L ⊗[Ls] P))) :
    ∃ (L' : Type (max uEbar uL)) (_ : Field L')
        (_ : Algebra P L')
        (g : (P ⊗[Ls] L) →ₐ[P] L'),
        Function.Surjective g ∧
        RingHom.ker g.toRingHom ≤ nilradical (P ⊗[Ls] L) ∧
        (⊤ : IntermediateField P L').FG ∧
        separableClosure P L' = ⊥ := by
  let instLalg : Algebra L (P ⊗[Ls] L) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨q, hq⟩ := ExpChar.exists Ls
  have : ExpChar Ls q := hq
  have hq1 : 1 ≤ q := expChar_pos Ls q
  have hprime : (nilradical (P ⊗[Ls] L)).IsPrime := by
    have hpB : (nilradical (L ⊗[Ls] P)).IsPrime :=
      (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical).mp hirrLP
    exact nilradicalIsPrime_of_ringEquiv
      (Algebra.TensorProduct.comm Ls P L).toRingEquiv hpB
  have hkey := tensor_qpow_mem_rightRange Ls P L q
  have hisfield : IsField ((P ⊗[Ls] L) ⧸ nilradical (P ⊗[Ls] L)) :=
    reducedQuotient_isField_of_qpow L (P ⊗[Ls] L) q hq1 hkey
  let fieldInst : Field ((P ⊗[Ls] L) ⧸ nilradical (P ⊗[Ls] L)) := hisfield.toField
  set g : (P ⊗[Ls] L) →ₐ[P] ((P ⊗[Ls] L) ⧸ nilradical (P ⊗[Ls] L)) :=
    Ideal.Quotient.mkₐ P (nilradical (P ⊗[Ls] L)) with hg
  have hsurj : Function.Surjective g := Ideal.Quotient.mkₐ_surjective P _
  have hker : RingHom.ker g.toRingHom ≤ nilradical (P ⊗[Ls] L) := by
    have hk : RingHom.ker g.toRingHom = nilradical (P ⊗[Ls] L) := by
      rw [hg, AlgHom.toRingHom_eq_coe]
      ext x
      rw [RingHom.mem_ker]
      change (Ideal.Quotient.mk _) x = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [hk]
  refine ⟨(P ⊗[Ls] L) ⧸ nilradical (P ⊗[Ls] L), fieldInst, inferInstance, g, hsurj, hker, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hfgL
    refine fg_top_of_span_adjoin Ls P L _ ((g : (P ⊗[Ls] L) →+* _).comp
      (Algebra.TensorProduct.includeRight : L →ₐ[Ls] (P ⊗[Ls] L)).toRingHom) s hs ?_ ?_
    · intro c
      refine ⟨algebraMap Ls P c, ?_⟩
      rw [RingHom.comp_apply]
      change algebraMap P ((P ⊗[Ls] L) ⧸ nilradical (P ⊗[Ls] L)) (algebraMap Ls P c)
        = g (Algebra.TensorProduct.includeRight (algebraMap Ls L c))
      have h1 : (Algebra.TensorProduct.includeRight (algebraMap Ls L c) : P ⊗[Ls] L)
          = algebraMap P (P ⊗[Ls] L) (algebraMap Ls P c) := by
        rw [Algebra.TensorProduct.includeRight_apply,
          ← IsScalarTower.algebraMap_apply Ls P (P ⊗[Ls] L) c,
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
          Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
      rw [h1, AlgHom.commutes]
    · exact span_range_includeRight_map_eq_top Ls P L _ g hsurj
  · exact perfectBase_reducedQuotient_sepClosed Ls P L hsc _ g hsurj

/-- Migration to the perfect closure: for a finitely generated `L/Ls` with trivial separable
closure, the base change to `P = perfectClosure Ls Ebar` admits a surjection onto a field `L'`
with nilpotent kernel, `L'` again finitely generated over `P` with trivial separable closure. -/
theorem perfectBase_reducedQuotient_field
    (Ls : Type uLs) [Field Ls] (Ebar : Type uEbar) [Field Ebar] [Algebra Ls Ebar] [IsAlgClosed Ebar]
    (L : Type uL) [Field L] [Algebra Ls L]
    (hfgL : (⊤ : IntermediateField Ls L).FG)
    (hsc : separableClosure Ls L = ⊥) :
    ∃ (L' : Type (max uEbar uL)) (_ : Field L')
        (_ : Algebra (↥(perfectClosure Ls Ebar)) L')
        (g : ((↥(perfectClosure Ls Ebar)) ⊗[Ls] L) →ₐ[↥(perfectClosure Ls Ebar)] L'),
        Function.Surjective g ∧
        RingHom.ker g.toRingHom ≤ nilradical ((↥(perfectClosure Ls Ebar)) ⊗[Ls] L) ∧
        (⊤ : IntermediateField (↥(perfectClosure Ls Ebar)) L').FG ∧
        separableClosure (↥(perfectClosure Ls Ebar)) L' = ⊥ := by
  -- `P := ↥(perfectClosure Ls Ebar)` is perfect and purely inseparable over `Ls`; supply the
  -- K1 irreducibility of `Spec (L ⊗[Ls] P)` and delegate to the abstract analytic kernel.
  have hirrLP : IrreducibleSpace (PrimeSpectrum (L ⊗[Ls] (↥(perfectClosure Ls Ebar)))) :=
    irreducibleSpace_baseChange_purelyInseparable Ls L (↥(perfectClosure Ls Ebar))
  exact perfectBase_reducedQuotient_field_abstract Ls (↥(perfectClosure Ls Ebar)) L hfgL hsc hirrLP
--
/-- (MIG-FG) The finitely generated case: obtain `L'` and `g` from A1, feed `hA2` the finite
generation and separably-closed facts from A1 to get `IsDomain (Ebar ⊗[P] L')`, and apply ASM. -/
theorem tensorAlgClosed_perfectBase_irreducible_fg
    (Ls : Type uLs) [Field Ls] (Ebar : Type uEbar) [Field Ebar] [Algebra Ls Ebar] [IsAlgClosed Ebar]
    (L : Type uL) [Field L] [Algebra Ls L]
    (hfgL : (⊤ : IntermediateField Ls L).FG)
    (hsc : separableClosure Ls L = ⊥)
    (hA2 : ∀ (L' : Type (max uEbar uL)) [Field L'] [Algebra (↥(perfectClosure Ls Ebar)) L'],
        (⊤ : IntermediateField (↥(perfectClosure Ls Ebar)) L').FG →
        separableClosure (↥(perfectClosure Ls Ebar)) L' = ⊥ →
        IsDomain (Ebar ⊗[↥(perfectClosure Ls Ebar)] L')) :
    IrreducibleSpace (PrimeSpectrum (Ebar ⊗[Ls] L)) := by
  obtain ⟨L', _, _, g, hsurj, hker, hfg', hsc'⟩ :=
    perfectBase_reducedQuotient_field Ls Ebar L hfgL hsc
  have hdom : IsDomain (Ebar ⊗[↥(perfectClosure Ls Ebar)] L') := hA2 L' hfg' hsc'
  exact perfectBase_fg_assemble Ls Ebar L L' g hsurj hker hdom
/-- (MIG-R3) directed-colimit reduction to the finitely generated case, consuming MIG-FG. The
reduction quantifies over the finitely generated intermediate fields `M` of `L/Ls`, as subtypes
`↥M`, so the universe is pinned to `L`'s, avoiding the universe metavariables that would arise
from an abstract `∀ (M : Type _)`. -/
theorem tensorAlgClosed_perfectBase_irreducible_colimit
    (Ls : Type*) [Field Ls] (Ebar : Type*) [Field Ebar] [Algebra Ls Ebar] [IsAlgClosed Ebar]
    (L : Type*) [Field L] [Algebra Ls L]
    (hFG : ∀ (M : IntermediateField Ls L), M.FG →
        IrreducibleSpace (PrimeSpectrum (Ebar ⊗[Ls] ↥M))) :
    IrreducibleSpace (PrimeSpectrum (Ebar ⊗[Ls] L)) := by
  -- directed union of its finitely generated sub-`Ls`-fields `M`; nilradical-prime passes
  -- through the filtered colimit `Ebar ⊗[Ls] L = colim (Ebar ⊗[Ls] ↥M)`).
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  let φ : (M : IntermediateField Ls L) → (Ebar ⊗[Ls] ↥M →ₐ[Ebar] (Ebar ⊗[Ls] L)) :=
    fun M => Algebra.TensorProduct.map (AlgHom.id Ebar Ebar) M.val
  have hφinj : ∀ (M : IntermediateField Ls L), Function.Injective (φ M) := by
    intro M
    have key : (φ M).toLinearMap = LinearMap.lTensor Ebar (M.val.toLinearMap) :=
      toLinearMap_map_id_eq_lTensor M.val
    rw [show ⇑(φ M) = ⇑(LinearMap.lTensor Ebar (M.val.toLinearMap)) from by rw [← key]; rfl]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ M.val.injective
  have hmono : ∀ (M₁ M₂ : IntermediateField Ls L), M₁ ≤ M₂ →
      (φ M₁).range ≤ (φ M₂).range := by
    intro M₁ M₂ h
    have hfac : φ M₁ = (φ M₂).comp
        (Algebra.TensorProduct.map (AlgHom.id Ebar Ebar) (IntermediateField.inclusion h)) := by
      change Algebra.TensorProduct.map (AlgHom.id Ebar Ebar) (M₁.val) = _
      rw [← Algebra.TensorProduct.map_comp]; congr 1
    rw [hfac, AlgHom.range_comp]
    rintro x ⟨y, -, rfl⟩
    exact ⟨_, rfl⟩
  have hcov : ∀ x : Ebar ⊗[Ls] L, ∃ M : IntermediateField Ls L, M.FG ∧ x ∈ (φ M).range := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul e s =>
        refine ⟨IntermediateField.adjoin Ls {s}, ?_, ?_⟩
        · have h := IntermediateField.fg_adjoin_finset (F := Ls) ({s} : Finset L)
          rw [Finset.coe_singleton] at h
          exact h
        · refine ⟨e ⊗ₜ[Ls] ⟨s, ?_⟩, ?_⟩
          · exact IntermediateField.subset_adjoin Ls {s} (Set.mem_singleton s)
          · change Algebra.TensorProduct.map (AlgHom.id Ebar Ebar) _ _ = _
            rw [Algebra.TensorProduct.map_tmul]; rfl
    | add a b ha hb =>
        obtain ⟨M₁, hM₁, haM₁⟩ := ha
        obtain ⟨M₂, hM₂, hbM₂⟩ := hb
        refine ⟨M₁ ⊔ M₂, IntermediateField.fg_sup hM₁ hM₂, ?_⟩
        exact Subalgebra.add_mem _ (hmono M₁ (M₁ ⊔ M₂) le_sup_left haM₁)
          (hmono M₂ (M₁ ⊔ M₂) le_sup_right hbM₂)
  have hreflect : ∀ (M : IntermediateField Ls L) (u : Ebar ⊗[Ls] ↥M),
      IsNilpotent (φ M u) → IsNilpotent u := by
    intro M u h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, hφinj M ?_⟩
    have e1 : (φ M).toRingHom (u ^ n) = ((φ M).toRingHom u) ^ n := map_pow (φ M).toRingHom u n
    change (φ M).toRingHom (u ^ n) = (φ M).toRingHom 0
    rw [map_zero, e1]
    exact hn
  constructor
  · rw [Ideal.ne_top_iff_one, mem_nilradical]
    exact not_isNilpotent_one
  · intro a b hab
    rw [mem_nilradical] at hab
    obtain ⟨Ma, hMa, ha⟩ := hcov a
    obtain ⟨Mb, hMb, hb⟩ := hcov b
    set M := Ma ⊔ Mb with hM
    have hMfg : M.FG := IntermediateField.fg_sup hMa hMb
    have haM : a ∈ (φ M).range := hmono Ma M le_sup_left ha
    have hbM : b ∈ (φ M).range := hmono Mb M le_sup_right hb
    obtain ⟨a', ha'⟩ := haM
    obtain ⟨b', hb'⟩ := hbM
    have ha'' : (φ M) a' = a := ha'
    have hb'' : (φ M) b' = b := hb'
    have hMprime : (nilradical (Ebar ⊗[Ls] ↥M)).IsPrime := by
      rw [← PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
      exact hFG M hMfg
    have hab' : IsNilpotent (a' * b') := hreflect M _ (by rwa [map_mul, ha'', hb''])
    have hmem : a' * b' ∈ nilradical (Ebar ⊗[Ls] ↥M) := mem_nilradical.mpr hab'
    have hpush : ∀ x : Ebar ⊗[Ls] ↥M, x ∈ nilradical (Ebar ⊗[Ls] ↥M) →
        φ M x ∈ nilradical (Ebar ⊗[Ls] L) := fun x hx =>
      mem_nilradical.mpr ((mem_nilradical.mp hx).map (φ M).toRingHom)
    rcases hMprime.mem_or_mem hmem with h | h
    · exact Or.inl (ha'' ▸ hpush _ h)
    · exact Or.inr (hb'' ▸ hpush _ h)
/-- (SL-2/AC-MIG) THE PERFECT-CLOSURE MIGRATION (ASSEMBLY). Apply MIG-R3 supplying MIG-FG. For each
finitely generated intermediate field `M`, the f.g. of `↥M/Ls` is `M.FG`
(`IntermediateField.essFiniteType_iff` + `IntermediateField.fg_top`) and `separableClosure Ls
↥M = ⊥` descends from `hsc` (MIG-DESC), so MIG-FG (consuming `hA2`) proves `Spec(Ebar ⊗[Ls]
↥M)` irreducible. -/
theorem tensorAlgClosed_irreducible_of_perfectBase_domain
    (Ls : Type uLs) [Field Ls] (Ebar : Type uEbar) [Field Ebar] [Algebra Ls Ebar] [IsAlgClosed Ebar]
    (L : Type uL) [Field L] [Algebra Ls L]
    (hsc : separableClosure Ls L = ⊥)
    (hA2 : ∀ (L' : Type (max uEbar uL)) [Field L'] [Algebra (↥(perfectClosure Ls Ebar)) L'],
        (⊤ : IntermediateField (↥(perfectClosure Ls Ebar)) L').FG →
        separableClosure (↥(perfectClosure Ls Ebar)) L' = ⊥ →
        IsDomain (Ebar ⊗[↥(perfectClosure Ls Ebar)] L')) :
    IrreducibleSpace (PrimeSpectrum (Ebar ⊗[Ls] L)) := by
  -- R3 reduces to the finitely generated case (MIG-FG), which consumes hA2.
  refine tensorAlgClosed_perfectBase_irreducible_colimit Ls Ebar L ?_
  intro M hfgM
  -- `↥M` is finitely generated over `Ls` (M.FG ⟹ EssFiniteType ⟹ ⊤.FG).
  have : Algebra.EssFiniteType Ls ↥M := IntermediateField.essFiniteType_iff.mpr hfgM
  have hfgTop : (⊤ : IntermediateField Ls ↥M).FG := IntermediateField.fg_top Ls ↥M
  -- `separableClosure Ls ↥M = ⊥` descends from `hsc`.
  have hscM : separableClosure Ls ↥M = ⊥ := separableClosure_eq_bot_of_le Ls L hsc M
  exact tensorAlgClosed_perfectBase_irreducible_fg Ls Ebar ↥M hfgTop hscM hA2
/-- (SL-2/AC) The algebraically-closed-`E` core. For `Ē` algebraically closed and `L/Ls` a field
with `separableClosure Ls L = ⊥`, the space `Spec (Ē ⊗[Ls] L)` is irreducible. The proof applies
the perfect-closure migration, supplying the perfect-base domain core (A2) as `hA2`. -/
@[ega "IV 4.3.2" "special case", ega "IV 4.3.3" "special case", ega "IV 4.5.21" "special case"]
theorem tensorAlgClosed_irreducible_of_sepClosed
    (Ls : Type*) [Field Ls] (Ebar : Type*) [Field Ebar] [Algebra Ls Ebar] [IsAlgClosed Ebar]
    (L : Type*) [Field L] [Algebra Ls L]
    (hsc : separableClosure Ls L = ⊥) :
    IrreducibleSpace (PrimeSpectrum (Ebar ⊗[Ls] L)) := by
  have : PerfectField (↥(perfectClosure Ls Ebar)) := inferInstance
  refine tensorAlgClosed_irreducible_of_perfectBase_domain Ls Ebar L hsc ?_
  intro L' _ _ hfg hsc'
  exact tensorAlgClosed_perfectBase_isDomain (↥(perfectClosure Ls Ebar)) Ebar L' hfg hsc'
--
/-- (SL-2) Take `Ē := AlgebraicClosure E` (algebraically closed, an `E`-algebra hence an
`Ls`-algebra via the scalar tower), apply the alg-closed core (SL-2/AC) to get `Spec(Ē ⊗[Ls]
L)` irreducible, then descend to `E` (SL-2/R). -/
@[ega "IV 4.3.2",
  ega "IV 4.3.3" "forward implication",
  ega "IV 4.3.4" "special case",
  ega "IV 4.4.4" "special case",
  ega "IV 4.4.5" "special case",
  ega "IV 4.5.21" "special case"]
theorem tensorField_irreducible_of_sepClosed
    (Ls : Type*) [Field Ls] (E : Type*) [Field E] [Algebra Ls E]
    (L : Type*) [Field L] [Algebra Ls L]
    (hsc : separableClosure Ls L = ⊥) :
    IrreducibleSpace (PrimeSpectrum (E ⊗[Ls] L)) := by
  -- the TRUE implication direction; conclusion is Spec-irreducible, not domain, so the
  -- char-p nilpotent case is correctly covered).
  -- `Ē := AlgebraicClosure E`: algebraically closed; its `Ls`-algebra structure and the
  -- scalar tower `Ls → E → Ē` are the canonical Mathlib instances.
  -- alg-closed core ⟹ `Spec(Ē ⊗[Ls] L)` irreducible.
  have hEbar : IrreducibleSpace (PrimeSpectrum ((AlgebraicClosure E) ⊗[Ls] L)) :=
    tensorAlgClosed_irreducible_of_sepClosed Ls (AlgebraicClosure E) L hsc
  -- descend along the faithfully-flat base change `E ⊗ L → Ē ⊗ L`.
  exact tensorField_irreducible_descent_of_algClosure Ls E (AlgebraicClosure E) L hEbar

/-- (G1a) THE GENUINE ANALYTIC KERNEL — now PROVED modulo SL-1 + SL-2. Reduce the domain `B` to `E
:= FractionRing B` (SL-1), then apply the field-theoretic geometric-irreducibility core (SL-2). -/
@[ega "IV 4.3.2" "more general",
  ega "IV 4.3.3" "forward implication",
  ega "IV 4.3.4" "special case",
  ega "IV 4.4.4" "special case",
  ega "IV 4.4.5" "special case",
  ega "IV 4.5.21" "special case"]
theorem geomPure_baseChange_irreducible
    (Ls : Type*) [Field Ls] (B : Type*) [CommRing B] [IsDomain B] [Algebra Ls B]
    (L : Type*) [Field L] [Algebra Ls L]
    (hsc : separableClosure Ls L = ⊥) :
    IrreducibleSpace (PrimeSpectrum (B ⊗[Ls] L)) :=
  tensor_irreducible_of_fractionRing Ls B L
    (tensorField_irreducible_of_sepClosed Ls (FractionRing B) L hsc)

/-- (G1) The analytic kernel over an abstract base field `Ls`. The proof is bookkeeping: set
`B := K ⊗[F] Ls`, a domain by `hdom`, with its right `Ls`-algebra structure; the descent (G1a)
gives irreducibility of `Spec (B ⊗[Ls] L)`; transport along the base-change-associativity ring
isomorphism `(K ⊗[F] Ls) ⊗[Ls] L ≃+* K ⊗[F] L`. -/
@[ega "IV 4.3.3" "special case"]
theorem irreducibleSpace_tensor_of_relSepClosed_bot
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    (Ls : Type*) [Field Ls] [Algebra F Ls]
    (L : Type) [Field L] [Algebra F L] [Algebra Ls L] [IsScalarTower F Ls L]
    (hdom : IsDomain (K ⊗[F] Ls)) (hsc : separableClosure Ls L = ⊥) :
    IrreducibleSpace (PrimeSpectrum (K ⊗[F] L)) := by
  -- give `B := K ⊗[F] Ls` its right `Ls`-algebra structure (the diamond fix: do all
  -- the `⊗[Ls]` work HERE where `Ls` is a clean bound variable).
  let : Algebra Ls (K ⊗[F] Ls) := Algebra.TensorProduct.rightAlgebra
  -- (G1a) descent over the domain base `B := K ⊗[F] Ls`.
  have hirr : IrreducibleSpace (PrimeSpectrum ((K ⊗[F] Ls) ⊗[Ls] L)) :=
    geomPure_baseChange_irreducible Ls (K ⊗[F] Ls) L hsc
  -- base-change associativity ring iso: `(K ⊗[F] Ls) ⊗[Ls] L ≃+* K ⊗[F] L`.
  have eglue : (K ⊗[F] Ls) ⊗[Ls] L ≃+* K ⊗[F] L := by
    have hmap : ∀ s : Ls, (algebraMap Ls (K ⊗[F] Ls)) s = 1 ⊗ₜ[F] s := fun s => rfl
    -- inner comm as an `Ls`-algebra equiv (rightAlgebra on the left ↔ leftAlgebra on
    -- the right; the underlying `comm` is `Ls`-linear).
    have einner : (K ⊗[F] Ls) ≃ₐ[Ls] (Ls ⊗[F] K) :=
      AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm F K Ls).toRingEquiv)
        (by intro s; rw [hmap]; simp)
    -- chain: (K⊗[F]Ls)⊗[Ls]L ≃[Ls] L⊗[Ls](K⊗[F]Ls) ≃[Ls] L⊗[Ls](Ls⊗[F]K)
    --        ≃[Ls] L⊗[F]K ≃[F] K⊗[F]L
    have e0 := Algebra.TensorProduct.comm Ls (K ⊗[F] Ls) L
    have e1 := Algebra.TensorProduct.congr (AlgEquiv.refl (R := Ls) (A₁ := L)) einner
    have e2 := Algebra.TensorProduct.cancelBaseChange F Ls Ls L K
    have e3 := Algebra.TensorProduct.comm F L K
    exact (((e0.trans e1).trans e2).toRingEquiv).trans e3.toRingEquiv
  -- transport irreducibility along the ring iso (manual Homeomorph from `comap`).
  let h : PrimeSpectrum (K ⊗[F] L) ≃ₜ PrimeSpectrum ((K ⊗[F] Ls) ⊗[Ls] L) :=
  { toFun := PrimeSpectrum.comap eglue.toRingHom
    invFun := PrimeSpectrum.comap eglue.symm.toRingHom
    left_inv := by intro x; simp [← PrimeSpectrum.comap_comp_apply]
    right_inv := by intro x; simp [← PrimeSpectrum.comap_comp_apply]
    continuous_toFun := PrimeSpectrum.continuous_comap _
    continuous_invFun := PrimeSpectrum.continuous_comap _ }
  exact h.irreducibleSpace_iff.mpr hirr

/-- (A-G) assembly: instantiate the abstract kernel (G1) at `Ls := separableClosure F L`. -/
@[ega "IV 4.3.3" "special case"]
theorem irreducibleSpace_tensor_of_algSep_domain (F K : Type*) [Field F] [Field K]
    [Algebra F K] (L : Type) [Field L] [Algebra F L]
    (hBdom : IsDomain (K ⊗[F] ↥(separableClosure F L))) :
    IrreducibleSpace (PrimeSpectrum (K ⊗[F] L)) := by
  -- descent. The hypothesis is
  -- IsDomain of the relative-separable-closure tensor; the conclusion is irreducibility
  -- of Spec(K⊗L) — purely-inseparable base change is a Spec universal homeomorphism,
  -- so irreducibility (not integrality) descends. No counterexample.)
  -- `L / (separableClosure F L)` has trivial relative separable closure (P1a-style).
  have hsc : separableClosure (↥(separableClosure F L)) L = ⊥ :=
    separableClosure.separableClosure_eq_bot F L
  -- Apply the abstract geometrically-pure descent kernel (G1) over `Ls := separableClosure F L`.
  exact irreducibleSpace_tensor_of_relSepClosed_bot F K (↥(separableClosure F L)) L hBdom hsc

/-- (A) assembly: chain (A-D) [domain over the relative separable closure] then (A-G). -/
@[ega "IV 4.4.4" "special case", ega "IV 4.4.5" "special case", ega "IV 4.5.21" "special case"]
theorem geomIrred_descent (F K : Type*) [Field F] [Field K] [Algebra F K]
    (hdom : IsDomain (K ⊗[F] (SeparableClosure F)))
    (L : Type) [Field L] [Algebra F L] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[F] L)) := by
  -- separable splitting is controlled by hdom on F^sep, purely-insep base change is a
  -- Spec universal homeomorphism so irreducibility — not integrality — descends to all L).
  -- (A-D): `Ls := separableClosure F L` is separable-algebraic over `F`, so
  -- `K ⊗[F] Ls` is a domain.
  have hsep : Algebra.IsSeparable F ↥(separableClosure F L) :=
    separableClosure.isSeparable F L
  have halg : Algebra.IsAlgebraic F ↥(separableClosure F L) :=
    separableClosure.isAlgebraic F L
  have hBdom : IsDomain (K ⊗[F] ↥(separableClosure F L)) :=
    tensorSep_algSep_isDomain F K hdom ↥(separableClosure F L)
  -- (A-G): the geometrically pure descent upgrades this domain to irreducibility of
  -- `Spec(K ⊗[F] L)`.
  exact irreducibleSpace_tensor_of_algSep_domain F K L hBdom

/-- If the separable closure of `F` in `K` is trivial, then `Spec (K ⊗[F] L)` is irreducible for
every field extension `L/F`. -/
@[ega "IV 4.3.3" "special case",
  ega "IV 4.4.4" "special case",
  ega "IV 4.5.21" "special case",
  ega "IV 4.5.9" "(c) ⇒ (a), special case"]
theorem geomIrred_of_sepClosed (F K : Type*) [Field F] [Field K] [Algebra F K]
    (hsc : separableClosure F K = ⊥)
    (L : Type) [Field L] [Algebra F L] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[F] L)) := by
  -- Stacks 037L definition quantifies over every field extension; 037K shows
  -- holding for separable/algebraic L ⟺ holding for ALL L; 0G33 gives the
  -- equivalence with `separableClosure F K = ⊥`).
  -- (B) 0G33 core: `K ⊗[F] F^sep` is a domain; (A) 037K descent: upgrade to all `L`.
  have hdom : IsDomain (K ⊗[F] (SeparableClosure F)) :=
    geomIrred_tensor_sep_isDomain F K hsc
  exact geomIrred_descent F K hdom L

/-- Let `k' = separableClosure k K`. For every field extension `L/k'` with `L : Type` (the
universe `0`), the spectrum `Spec(K ⊗_{k'} L)` is irreducible. When `K : Type` this is Stacks
037Q (1); for `K` in a higher universe it tests only fields in `Type`, so it does not by itself
give geometric irreducibility in the 037L sense, which tests fields in the universe of `K`. The
statement of 037Q (1) in the 037L sense, in every universe, is
`separableClosure.isGeometricallyIrreducible`. -/
@[ega "IV 4.3.2" "special case",
  ega "IV 4.3.3" "special case",
  ega "IV 4.4.4" "special case",
  ega "IV 4.5.21" "special case"]
theorem part1 (k K : Type*) [Field k] [Field K] [Algebra k K] :
    ∀ (L : Type) [Field L] [Algebra (separableClosure k K) L],
      IrreducibleSpace (PrimeSpectrum (K ⊗[separableClosure k K] L)) := by
  intro L _ _
  -- `k' = separableClosure k K` is separably closed in `K` (P1a).
  have hsc : separableClosure (separableClosure k K) K = ⊥ :=
    separableClosure.separableClosure_eq_bot k K
  -- Apply the geometric-irreducibility kernel (P1b) with `F := k'`.
  exact geomIrred_of_sepClosed (separableClosure k K) K hsc L
