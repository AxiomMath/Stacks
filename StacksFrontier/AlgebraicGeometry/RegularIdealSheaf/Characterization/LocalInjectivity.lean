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
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.LocalKernel
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.ConormalLocallyFree

/-!
# Quasi-regular ideal sheaves: injectivity from the local kernel

Composition of symmetric maps, injectivity of the canonical map from the local kernel
condition, coordinates of conormally independent generators, and local lifts of conormal
sections over the over-site.
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

namespace Construction

/-- The map on words induced by a composite of ring homomorphisms, on a single word. -/
private lemma wordsMap_comp_word {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) (K : Ideal S) (L : Ideal T) (φ : R →+* S) (ψ : S →+* T) (χ : R →+* T)
    (hχ : ∀ a, χ a = ψ (φ a)) (hφ : I ≤ K.comap φ) (hψ : K ≤ L.comap ψ)
    (hχ' : I ≤ L.comap χ) (n : ℕ) (a : Fin n → I) :
    wordsMap K L ψ hψ n (wordsMap I K φ hφ n (word I a)) =
      wordsMap I L χ hχ' n (word I a) := by
  rw [wordsMap_word, wordsMap_word, wordsMap_word]
  congr 1
  funext i
  exact Subtype.ext (hχ (a i : R)).symm

/-- Composing the maps on words induced by two ring homomorphisms gives the map
induced by their composite. -/
private lemma wordsMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) (K : Ideal S) (L : Ideal T) (φ : R →+* S) (ψ : S →+* T) (χ : R →+* T)
    (hχ : ∀ a, χ a = ψ (φ a)) (hφ : I ≤ K.comap φ) (hψ : K ≤ L.comap ψ)
    (hχ' : I ≤ L.comap χ) (n : ℕ) (z : Words I n) :
    wordsMap K L ψ hψ n (wordsMap I K φ hφ n z) = wordsMap I L χ hχ' n z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | single a c =>
    have h : Finsupp.single a c = c • word I a := by simp [word]
    rw [h, map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hχ c,
      wordsMap_comp_word I K L φ ψ χ hχ hφ hψ hχ' n a]

/-- Composing the maps on symmetric powers induced by two ring homomorphisms gives
the map induced by their composite. -/
private lemma symmetricMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) (K : Ideal S) (L : Ideal T) (φ : R →+* S) (ψ : S →+* T) (χ : R →+* T)
    (hχ : ∀ a, χ a = ψ (φ a)) (hφ : I ≤ K.comap φ) (hψ : K ≤ L.comap ψ)
    (hχ' : I ≤ L.comap χ) (n : ℕ) (z : SymmetricPower I n) :
    symmetricMap K L ψ hψ n (symmetricMap I K φ hφ n z) = symmetricMap I L χ hχ' n z := by
  induction z using Submodule.Quotient.induction_on with | _ z =>
  show Submodule.Quotient.mk (wordsMap K L ψ hψ n (wordsMap I K φ hφ n z)) =
    Submodule.Quotient.mk (wordsMap I L χ hχ' n z)
  rw [wordsMap_comp I K L φ ψ χ hχ hφ hψ hχ' n z]

/-- The canonical map sends the class of a word to the class of the product of
its letters. -/
private lemma canonicalMap_wordClass {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)
    (a : Fin n → I) : canonicalMap I n (wordClass I n a) = productClass I n a := by
  show productMap I n (word I a) = _
  exact productMap_word I a

end Construction

/-- Taking classes in a quotient module commutes with finite sums. -/
private lemma quotient_mk_sum {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M]
    [Module R M] (p : Submodule R M) {ι : Type*} (s : Finset ι) (x : ι → M) :
    (Submodule.Quotient.mk (∑ i ∈ s, x i) : M ⧸ p) =
      ∑ i ∈ s, (Submodule.Quotient.mk (x i) : M ⧸ p) :=
  map_sum (Submodule.mkQ p) x s

/-- The `m`-th power of the ideal generated by a finite family is contained in the
span of the degree `m` monomials in that family. -/
lemma pow_jid_le_span_monomials {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (m : ℕ) :
    Jid f ^ m ≤ Ideal.span (Set.range (fun t : Fin m → Fin r => ∏ j, f (t j))) := by
  induction m with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, top_le_iff]
    apply (Ideal.eq_top_iff_one _).mpr
    exact Ideal.subset_span ⟨fun i : Fin 0 => i.elim0, by simp⟩
  | succ m ih =>
    have hJ : Jid f = Ideal.span (Set.range f) := rfl
    have hstep : Ideal.span (Set.range (fun t : Fin m → Fin r => ∏ j, f (t j))) * Jid f ≤
        Ideal.span (Set.range (fun t : Fin (m + 1) → Fin r => ∏ j, f (t j))) := by
      rw [hJ, Ideal.span_mul_span, Ideal.span_le]
      rintro z ⟨p, ⟨t, rfl⟩, q, ⟨i, rfl⟩, rfl⟩
      refine Ideal.subset_span ⟨Fin.snoc t i, ?_⟩
      simp [Fin.prod_univ_castSucc]
    rw [pow_succ]
    exact le_trans (Ideal.mul_mono ih le_rfl) hstep

/-- Finitely many germs at a point of the restricted space are simultaneously
represented by sections on a single small open. -/
private lemma exists_sections_of_germInRestriction (X : RingedSpace.{u}) (U : Opens X)
    (y : X) (hyU : y ∈ U) (V : Opens X) (hyV : y ∈ V) {ι : Type*} [Finite ι]
    (a : ι → (X.restrict U.isOpenEmbedding).presheaf.stalk ⟨y, hyU⟩) :
    ∃ (W : Opens X) (_ : W ≤ V) (hyW : y ∈ W) (b : ι → X.presheaf.obj (op W)),
      ∀ i, germInRestriction X U y hyU W hyW (b i) = a i := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨W, hWV, hyW, b, hb⟩ := exists_sections_of_finite_germs X y V hyV
    (fun k => (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨y, hyU⟩).hom
      (a (e.symm k)))
  refine ⟨W, hWV, hyW, fun i => b (e i), fun i => ?_⟩
  show (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨y, hyU⟩).inv
    (X.presheaf.germ W y hyW (b (e i))) = a i
  rw [hb (e i), Equiv.symm_apply_apply]
  exact (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨y, hyU⟩).hom_inv_id_apply _

/-- Two sections with the same germ at a point of the restricted space agree on a
smaller open. -/
private lemma germInRestriction_eq (X : RingedSpace.{u}) (U : Opens X)
    (y : X) (hyU : y ∈ U) (V : Opens X) (hyV : y ∈ V) (s t : X.presheaf.obj (op V))
    (h : germInRestriction X U y hyU V hyV s = germInRestriction X U y hyU V hyV t) :
    ∃ (W : Opens X) (_ : y ∈ W) (i : W ⟶ V),
      X.presheaf.map i.op s = X.presheaf.map i.op t := by
  have h0 : (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨y, hyU⟩).inv
      (X.presheaf.germ V y hyV s) =
      (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨y, hyU⟩).inv
      (X.presheaf.germ V y hyV t) := h
  have h' : X.presheaf.germ V y hyV s = X.presheaf.germ V y hyV t := by
    rw [← (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨y, hyU⟩).inv_hom_id_apply
        (X.presheaf.germ V y hyV s),
      ← (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨y, hyU⟩).inv_hom_id_apply
        (X.presheaf.germ V y hyV t), h0]
  obtain ⟨W, hyW, i, j, hij⟩ := X.presheaf.germ_eq y hyV hyV s t h'
  refine ⟨W, hyW, i, ?_⟩
  rw [Subsingleton.elim j i] at hij
  exact hij

/-- A ring homomorphism carries a sum of coefficients times monomials to the same expression
in the images, as soon as it carries coefficients and generators to the given ones. -/
private lemma map_sum_mul_prod {A B : Type*} [CommRing A] [CommRing B] (ρ : A →+* B)
    {r m : ℕ} (a : (Fin m → Fin r) → A) (b : Fin r → A) (a' : (Fin m → Fin r) → B)
    (b' : Fin r → B) (ha : ∀ s, ρ (a s) = a' s) (hb : ∀ k, ρ (b k) = b' k) :
    ρ (∑ s, a s * ∏ j, b (s j)) = ∑ s, a' s * ∏ j, b' (s j) := by
  simp only [map_sum, map_mul, map_prod, ha, hb]

/-- **The stalkwise form of the local-kernel hypothesis.** If the ideal sheaf `J` is
generated on `U` by sections `f`, and if every section of a symmetric power killed by
the canonical map dies after restriction to a smaller open, then the canonical map of
the stalk ideal at each point of `U` is injective in every degree. -/
lemma canonicalMap_injective_of_local_kernel (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule)
    (hkernel : ∀ (n : ℕ) (W : Opens X)
      (z : Construction.SymmetricPower (sectionIdeal X J (op W)) n),
      Construction.canonicalMap (sectionIdeal X J (op W)) n z = 0 →
      ∀ (y : X), y ∈ W → ∃ (V : Opens X) (_ : y ∈ V) (i : V ⟶ W),
        Construction.symmetricMap _ _ (X.presheaf.map i.op).hom
          (sectionIdeal_map X J i.op) n z = 0)
    (U : Opens X) {r : ℕ} (f : Fin r → X.presheaf.obj (op U))
    (hgen : IsGeneratedByOn X J U f) (n : ℕ) (y : X) (hy : y ∈ U) :
    Function.Injective (Construction.canonicalMap
      (Jid (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
        (fun k => sectionOnRestriction X U (f k)) ⟨y, hy⟩)) n) := by
  classical
  have hIgen : ∀ (V : Opens X) (hVU : V ≤ U) (hyV : y ∈ V),
      sectionIdeal X J (op V) ≤
        (Jid (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
          (fun k => sectionOnRestriction X U (f k)) ⟨y, hy⟩)).comap
            (germInRestriction X U y hy V hyV) := by
    intro V hVU hyV s hs
    apply (germInRestriction_mem_span_iff X U y hy f V hyV s).mpr
    exact germ_mem_span_of_isGeneratedByOn X J U V f hgen hVU s hs y hyV
  have hfgen : ∀ (V : Opens X) (hVU : V ≤ U) (hyV : y ∈ V) (k : Fin r),
      germInRestriction X U y hy V hyV (X.presheaf.map (homOfLE hVU).op (f k)) =
        QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
          (fun k => sectionOnRestriction X U (f k)) ⟨y, hy⟩ k := by
    intro V hVU hyV k
    rw [germInRestriction_res X U y hy V U hyV hy (homOfLE hVU),
      germInRestriction_self]
    rfl
  have hfJ : ∀ (V : Opens X) (hVU : V ≤ U) (k : Fin r),
      X.presheaf.map (homOfLE hVU).op (f k) ∈ sectionIdeal X J (op V) := fun V hVU k =>
    J.toSubmodule.map_mem (homOfLE hVU).op (mem_of_isGeneratedByOn X J U f hgen k)
  have hcomp : ∀ {A B C : Opens X} (a : C ⟶ B) (b : B ⟶ A) (s : X.presheaf.obj (op A)),
      X.presheaf.map a.op (X.presheaf.map b.op s) = X.presheaf.map (a ≫ b).op s := by
    intro A B C a b s
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl
  have key : ∀ z, Construction.canonicalMap
      (Jid (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
        (fun k => sectionOnRestriction X U (f k)) ⟨y, hy⟩)) n z = 0 → z = 0 := by
    intro z hz
    have htop := Construction.span_generatorWord_eq_top
      (Jid (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
        (fun k => sectionOnRestriction X U (f k)) ⟨y, hy⟩))
      (idealGenerator (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
        (fun k => sectionOnRestriction X U (f k)) ⟨y, hy⟩))
      (span_idealGenerator_eq_top _) n
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
      (htop.ge (show z ∈ (⊤ : Submodule _ _) from Submodule.mem_top))
    obtain ⟨V, hVU, hyV, c', hc'⟩ :=
      exists_sections_of_germInRestriction X U y hy U hy c
    -- the generators restricted to `V`
    have hfV := hfJ V hVU
    -- the lifted element of the symmetric power on `V`
    have hzz : Construction.symmetricMap (sectionIdeal X J (op V)) _
        (germInRestriction X U y hy V hyV) (hIgen V hVU hyV) n
        (∑ t, c' t • Construction.wordClass (sectionIdeal X J (op V)) n
          (fun j => ⟨X.presheaf.map (homOfLE hVU).op (f (t j)), hfV (t j)⟩)) = z := by
      refine Eq.trans ?_ hc
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro t _
      rw [map_smulₛₗ, Construction.symmetricMap_wordClass]
      have hu : (fun j => Construction.idealMap (sectionIdeal X J (op V)) _
            (germInRestriction X U y hy V hyV) (hIgen V hVU hyV)
            ⟨X.presheaf.map (homOfLE hVU).op (f (t j)), hfV (t j)⟩) =
          (fun j => idealGenerator (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
            (fun k => sectionOnRestriction X U (f k)) ⟨y, hy⟩) (t j)) :=
        funext (fun j => Subtype.ext (hfgen V hVU hyV (t j)))
      rw [hu, hc' t]
      rfl
    -- the canonical image of the lifted element
    have hcan : Construction.canonicalMap (sectionIdeal X J (op V)) n
        (∑ t, c' t • Construction.wordClass (sectionIdeal X J (op V)) n
          (fun j => ⟨X.presheaf.map (homOfLE hVU).op (f (t j)), hfV (t j)⟩)) =
        Submodule.Quotient.mk
          (∑ t, c' t • Construction.product (sectionIdeal X J (op V)) n
            (fun j => ⟨X.presheaf.map (homOfLE hVU).op (f (t j)), hfV (t j)⟩)) := by
      rw [map_sum, quotient_mk_sum]
      refine Finset.sum_congr rfl ?_
      intro t _
      rw [map_smul, Construction.canonicalMap_wordClass]
      rfl
    -- the representative, and the vanishing of its germ class
    set w : X.presheaf.obj (op V) :=
      ((∑ t, c' t • Construction.product (sectionIdeal X J (op V)) n
        (fun j => ⟨X.presheaf.map (homOfLE hVU).op (f (t j)), hfV (t j)⟩) :
          ↥(sectionIdeal X J (op V) ^ n)) : X.presheaf.obj (op V)) with hw
    have hmem : germInRestriction X U y hy V hyV w ∈
        Jid (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
          (fun k => sectionOnRestriction X U (f k)) ⟨y, hy⟩) ^ (n + 1) := by
      have h0 : Construction.gradedMap (sectionIdeal X J (op V)) _
          (germInRestriction X U y hy V hyV) (hIgen V hVU hyV) n
          (Submodule.Quotient.mk
            (∑ t, c' t • Construction.product (sectionIdeal X J (op V)) n
              (fun j => ⟨X.presheaf.map (homOfLE hVU).op (f (t j)), hfV (t j)⟩))) = 0 := by
        rw [← hcan, ← Construction.canonicalMap_naturality, hzz, hz]
      rw [Construction.gradedMap_mk] at h0
      have h1 := (Submodule.Quotient.mk_eq_zero _).mp h0
      exact h1
    obtain ⟨d, hd⟩ := Ideal.mem_span_range_iff_exists_fun.mp
      (pow_jid_le_span_monomials _ (n + 1) hmem)
    obtain ⟨W, hWV, hyW, d', hd'⟩ := exists_sections_of_germInRestriction X U y hy V hyV d
    have hWU : W ≤ U := hWV.trans hVU
    -- the two sections on `W` have the same germ
    have heq : germInRestriction X U y hy W hyW
          (∑ s, d' s * ∏ j, X.presheaf.map (homOfLE hWU).op (f (s j))) =
        germInRestriction X U y hy W hyW (X.presheaf.map (homOfLE hWV).op w) := by
      rw [germInRestriction_res X U y hy W V hyW hyV (homOfLE hWV), ← hd]
      exact (map_sum_mul_prod _ d' _ d _ hd' (hfgen W hWU hyW) :)
    obtain ⟨W', hyW', iW, hW'⟩ := germInRestriction_eq X U y hy W hyW _ _ heq
    have hW'W : W' ≤ W := leOfHom iW
    have hW'V : W' ≤ V := hW'W.trans hWV
    have hW'U : W' ≤ U := hW'V.trans hVU
    -- the representative restricted to `W'` lies in the next power of the ideal
    have hpow : X.presheaf.map (homOfLE hW'V).op w ∈ sectionIdeal X J (op W') ^ (n + 1) := by
      have hres : X.presheaf.map (homOfLE hW'V).op w =
          ∑ s, X.presheaf.map iW.op (d' s) *
            ∏ j, X.presheaf.map (homOfLE hW'U).op (f (s j)) := by
        rw [show X.presheaf.map (homOfLE hW'V).op w =
          X.presheaf.map iW.op (X.presheaf.map (homOfLE hWV).op w) from (hcomp _ _ _).symm,
          ← hW']
        exact (map_sum_mul_prod (X.presheaf.map iW.op).hom d' _ _ _ (fun _ => rfl)
          (fun k => hcomp iW (homOfLE hWU) (f k)) :)
      rw [hres]
      apply Ideal.sum_mem
      intro s _
      apply Ideal.mul_mem_left
      simpa using (show (∏ j, X.presheaf.map (homOfLE hW'U).op (f (s j))) ∈
        ∏ _j : Fin (n + 1), sectionIdeal X J (op W') from
        Ideal.prod_mem_prod (fun j _ => hfJ W' hW'U (s j)))
    -- the canonical map kills the restriction of the lifted element to `W'`
    have hzW : Construction.canonicalMap (sectionIdeal X J (op W')) n
        (Construction.symmetricMap _ _ (X.presheaf.map (homOfLE hW'V).op).hom
          (sectionIdeal_map X J (homOfLE hW'V).op) n
          (∑ t, c' t • Construction.wordClass (sectionIdeal X J (op V)) n
            (fun j => ⟨X.presheaf.map (homOfLE hVU).op (f (t j)), hfV (t j)⟩))) = 0 := by
      rw [Construction.canonicalMap_naturality, hcan, Construction.gradedMap_mk]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hpow
    obtain ⟨V₂, hyV₂, i₂, hi₂⟩ := hkernel n W' _ hzW y hyW'
    have hV₂U : V₂ ≤ U := (leOfHom i₂).trans hW'U
    have hrestr : Construction.symmetricMap _ _
        (X.presheaf.map (i₂ ≫ homOfLE hW'V).op).hom
        (sectionIdeal_map X J (i₂ ≫ homOfLE hW'V).op) n
        (∑ t, c' t • Construction.wordClass (sectionIdeal X J (op V)) n
          (fun j => ⟨X.presheaf.map (homOfLE hVU).op (f (t j)), hfV (t j)⟩)) = 0 :=
      (symmetric_restrict_comp X J n (homOfLE hW'V) i₂ _).symm.trans hi₂
    rw [← hzz, ← Construction.symmetricMap_comp (sectionIdeal X J (op V))
      (sectionIdeal X J (op V₂)) _
      (X.presheaf.map (i₂ ≫ homOfLE hW'V).op).hom
      (germInRestriction X U y hy V₂ hyV₂)
      (germInRestriction X U y hy V hyV)
      (fun s => (germInRestriction_res X U y hy V₂ V hyV₂ hyV
        (i₂ ≫ homOfLE hW'V) s).symm)
      (sectionIdeal_map X J (i₂ ≫ homOfLE hW'V).op)
      (hIgen V₂ hV₂U hyV₂) (hIgen V hVU hyV) n, hrestr, map_zero]
  intro p q hpq
  apply sub_eq_zero.mp
  apply key
  simpa only [map_sub, sub_eq_zero] using hpq

/-- The degree-one conormal class map is surjective: the first power of an ideal is the
ideal itself. -/
private lemma conormalClass_surjective {R : Type u} [CommRing R] (I : Ideal R) :
    Function.Surjective (conormalClass I) := by
  intro z
  induction z using Submodule.Quotient.induction_on with | _ w =>
  exact ⟨⟨w.val, (pow_one I).le w.property⟩, rfl⟩

/-- The conormal classes of a generating sequence span the degree-one graded piece. -/
private lemma span_conormalClass_idealGenerator {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) :
    Submodule.span (qrRbar f)
      (Set.range (fun k => conormalClass (Jid f) (idealGenerator f k))) = ⊤ := by
  apply Submodule.restrictScalars_injective R (qrRbar f)
  rw [Submodule.restrictScalars_span R (qrRbar f) Ideal.Quotient.mk_surjective,
    Submodule.restrictScalars_top]
  have h : (Set.range (fun k => conormalClass (Jid f) (idealGenerator f k))) =
      conormalClass (Jid f) '' (Set.range (idealGenerator f)) := (Set.range_comp _ _)
  rw [h, ← Submodule.map_span, span_idealGenerator_eq_top, Submodule.map_top,
    LinearMap.range_eq_top]
  exact conormalClass_surjective (Jid f)

/-- **The coordinate system from linear independence of the conormal classes.** If the
only relations between the generators modulo the square of the ideal are the trivial
ones, then the conormal classes of the generators form a basis of the degree-one graded
piece, and its coordinates give the dual system that
`polynomialQuasiRegularCanonicalMap_bijective_of_coords` consumes. -/
lemma exists_coords_of_conormal_independent {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R)
    (hind : ∀ a : Fin r → R, (∑ k, a k * f k) ∈ Jid f ^ 2 → ∀ k, a k ∈ Jid f) :
    ∃ L : Jid f →ₗ[R] MvPolynomial (Fin r) (qrRbar f),
      (∀ z : Jid f, (z : R) ∈ Jid f ^ 2 → L z = 0) ∧
      ∀ i, L (idealGenerator f i) = MvPolynomial.X i := by
  classical
  have hli : LinearIndependent (qrRbar f)
      (fun k => conormalClass (Jid f) (idealGenerator f k)) :=
    conormalClass_linearIndependent (Jid f) (idealGenerator f)
      (by intro a ha; exact hind a ha)
  refine ⟨(LinearMap.restrictScalars R
      ((Finsupp.linearCombination (qrRbar f)
        (fun i => (MvPolynomial.X i : MvPolynomial (Fin r) (qrRbar f)))).comp
          (Module.Basis.mk hli (span_conormalClass_idealGenerator f).ge).repr.toLinearMap)).comp
      (conormalClass (Jid f)), ?_, ?_⟩
  · intro z hz
    have h : conormalClass (Jid f) z = 0 := (conormalClass_eq_zero_iff (Jid f) z).mpr hz
    rw [LinearMap.comp_apply, h, map_zero]
  · intro i
    have hb : (Module.Basis.mk hli (span_conormalClass_idealGenerator f).ge) i =
        conormalClass (Jid f) (idealGenerator f i) := Module.Basis.mk_apply _ _ i
    rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.comp_apply]
    show (Finsupp.linearCombination (qrRbar f)
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin r) (qrRbar f))))
        ((Module.Basis.mk hli (span_conormalClass_idealGenerator f).ge).repr
          (conormalClass (Jid f) (idealGenerator f i))) = _
    rw [← hb, Module.Basis.repr_self, Finsupp.linearCombination_single, one_smul]

/-- Linear independence of the conormal classes transfers along a ring isomorphism that
matches the two sequences. -/
lemma conormal_independent_of_ringHom {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (ψ : S →+* R) (hψφ : ∀ x, ψ (φ x) = x) (hφψ : ∀ x, φ (ψ x) = x)
    {r : ℕ} (f : Fin r → R) (g : Fin r → S) (he : ∀ k, φ (f k) = g k)
    (h : ∀ a : Fin r → R, (∑ k, a k * f k) ∈ Jid f ^ 2 → ∀ k, a k ∈ Jid f) :
    ∀ a : Fin r → S, (∑ k, a k * g k) ∈ Jid g ^ 2 → ∀ k, a k ∈ Jid g := by
  intro a ha k
  have hgf : ∀ j, ψ (g j) = f j := by
    intro j
    rw [← he j, hψφ]
  have h1 : Jid g ≤ (Jid f).comap ψ := span_le_comap_of_generators ψ g f hgf
  have h2 : Jid f ≤ (Jid g).comap φ := span_le_comap_of_generators φ f g he
  have hb : (∑ j, ψ (a j) * f j) ∈ Jid f ^ 2 := by
    have hm := Construction.map_pow_mem (Jid g) (Jid f) ψ h1 ha
    simpa only [map_sum, map_mul, hgf] using hm
  have h4 := Ideal.mem_comap.mp (h2 (h (fun j => ψ (a j)) hb k))
  rw [hφψ] at h4
  exact h4

section OverSiteConsumption

variable {X : RingedSpace.{u}}

/-- **Consuming a covering sieve of the over-topology at a point.** A sieve covering
`Y : Over U` contains an arrow out of an open neighbourhood of every point of `Y.left`.
This is the direction opposite to the one `conormalPresentation_locallySurjective`
produces, and the primitive the `hfree` half of Tag 063H is read through. -/
private lemma exists_arrow_of_mem_over (U : Opens X) {Y : Over U} (S : Sieve Y)
    (hS : S ∈ ((Opens.grothendieckTopology X).over U) Y) (y : X) (hy : y ∈ Y.left) :
    ∃ (V : Opens X) (_ : y ∈ V) (i : V ⟶ Y.left),
      S (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) := by
  have hS' : Sieve.overEquiv Y S ∈ (Opens.grothendieckTopology X) Y.left := hS
  obtain ⟨V, i, hi, hyV⟩ := hS' y hy
  exact ⟨V, hyV, i, (Sieve.overEquiv_iff S i).mp hi⟩

/-- Local surjectivity over the over-site, read at a point: a section lifts after
restriction to a neighbourhood. -/
lemma exists_local_preimage_over (U : Opens X)
    {R₀ : (Over U)ᵒᵖ ⥤ RingCat.{u}} {A B : PresheafOfModules.{u} R₀} (φ : A ⟶ B)
    (hφ : Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
      ((PresheafOfModules.toPresheaf R₀).map φ))
    (Y : Over U) (s : B.obj (op Y)) (y : X) (hy : y ∈ Y.left) :
    ∃ (V : Opens X) (_ : y ∈ V) (i : V ⟶ Y.left)
      (t : A.obj (op (Over.mk (i ≫ Y.hom)))),
      φ.app (op (Over.mk (i ≫ Y.hom))) t =
        B.map (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y).op s := by
  obtain ⟨V, hyV, i, hi⟩ := exists_arrow_of_mem_over U
    (Presheaf.imageSieve ((PresheafOfModules.toPresheaf R₀).map φ) s)
    (hφ.imageSieve_mem s) y hy
  obtain ⟨t, ht⟩ := hi
  exact ⟨V, hyV, i, t, ht⟩

/-- Local injectivity over the over-site, read at a point: two sections with the same
image agree after restriction to a neighbourhood. -/
lemma exists_local_eq_of_locallyInjective_over (U : Opens X)
    {R₀ : (Over U)ᵒᵖ ⥤ RingCat.{u}} {A B : PresheafOfModules.{u} R₀} (φ : A ⟶ B)
    (hφ : Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
      ((PresheafOfModules.toPresheaf R₀).map φ))
    (Y : Over U) (t t' : A.obj (op Y))
    (h : φ.app (op Y) t = φ.app (op Y) t') (y : X) (hy : y ∈ Y.left) :
    ∃ (V : Opens X) (_ : y ∈ V) (i : V ⟶ Y.left),
      A.map (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y).op t =
        A.map (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y).op t' := by
  obtain ⟨V, hyV, i, hi⟩ := exists_arrow_of_mem_over U _
    (hφ.equalizerSieve_mem t t' h) y hy
  exact ⟨V, hyV, i, hi⟩

end OverSiteConsumption

/-- The codomain of `conormalSheafificationUnitOver`, named so that every statement about
that morphism is written in one spelling. Asking Lean to equate this with
`((conormalSheaf X J).over U).val` is not merely expensive but ill-typed — the two are
presheaves of modules over different rings. -/
noncomputable abbrev conormalOverTarget (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) :=
  (PresheafOfModules.restrictScalars
    (Functor.whiskerLeft (Over.forget U).op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (quotientPresheaf X J)))).obj
    ((conormalSheaf X J).over U).val

/-- Restriction in the degree-one graded presheaf is restriction of the section. -/
private lemma gradedPresheaf_map_conormalClass (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) {V W : Opens X} (i : W ⟶ V)
    (z : J.obj (op V)) :
    (gradedPresheaf X J 1).map i.op (conormalClass (sectionIdeal X J (op V)) z) =
      conormalClass (sectionIdeal X J (op W))
        ⟨X.presheaf.map i.op z.val, J.toSubmodule.map_mem i.op z.property⟩ := rfl

/-- **One chosen generating section of the conormal sheaf comes from a section of `J`.**
Local surjectivity of the sheafification unit writes it, near any point of `U₀`, as the
conormal class of an honest section of `J`. -/
private lemma exists_local_conormal_lift_at (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X)
    (σ : ((conormalSheaf X J).over U₀).GeneratingSections) (i : σ.I)
    (x : X) (hx : x ∈ U₀) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU₀ : V ≤ U₀) (z : J.obj (op V)),
      (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hVU₀)))
          (conormalClass (sectionIdeal X J (op V)) z) =
        (conormalOverTarget X J U₀).map
          (Over.homMk (homOfLE hVU₀) :
            (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op
          ((σ.s i).val (op (Over.mk (𝟙 U₀)))) := by
  obtain ⟨V, hxV, j, t, ht⟩ := exists_local_preimage_over U₀
    (conormalSheafificationUnitOver X J U₀)
    (conormalSheafificationUnitOver_locallyBijective X J U₀).2 (Over.mk (𝟙 U₀))
    ((σ.s i).val (op (Over.mk (𝟙 U₀)))) x hx
  obtain ⟨z, hz⟩ := conormalClass_surjective (sectionIdeal X J (op V)) t
  refine ⟨V, hxV, leOfHom j, z, ?_⟩
  rw [hz]
  exact ht

/-- Restriction in the pushed-forward degree-one graded presheaf, written with the
morphism of `Over U₀` rather than of `Opens X`: `naturality_apply` must never be asked to
invert `g ↦ g.unop.left.op`, which is where its unification grinds. -/
private lemma pushforwardGraded_map_conormalClass (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X)
    {V W : Opens X} (hVU₀ : V ≤ U₀) (hWV : W ≤ V) (hWU₀ : W ≤ U₀) (z : J.obj (op V)) :
    ((PresheafOfModules.pushforward₀ (Over.forget U₀) (quotientPresheaf X J)).obj
          (gradedPresheaf X J 1)).map
        (Over.homMk (homOfLE hWV) :
          (Over.mk (homOfLE hWU₀) : Over U₀) ⟶ Over.mk (homOfLE hVU₀)).op
        (conormalClass (sectionIdeal X J (op V)) z) =
      conormalClass (sectionIdeal X J (op W))
        ⟨X.presheaf.map (homOfLE hWV).op z.val,
          J.toSubmodule.map_mem (homOfLE hWV).op z.property⟩ := rfl

/-- The conormal lift of a generating section restricts to smaller opens. -/
lemma conormal_lift_restrict (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X)
    (σ : ((conormalSheaf X J).over U₀).GeneratingSections) (i : σ.I)
    {V W : Opens X} (hVU₀ : V ≤ U₀) (hWV : W ≤ V) (hWU₀ : W ≤ U₀) (z : J.obj (op V))
    (hz : (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hVU₀)))
        (conormalClass (sectionIdeal X J (op V)) z) =
      (conormalOverTarget X J U₀).map
        (Over.homMk (homOfLE hVU₀) :
          (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op
        ((σ.s i).val (op (Over.mk (𝟙 U₀))))) :
    (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hWU₀)))
        (conormalClass (sectionIdeal X J (op W))
          ⟨X.presheaf.map (homOfLE hWV).op z.val,
            J.toSubmodule.map_mem (homOfLE hWV).op z.property⟩) =
      (conormalOverTarget X J U₀).map
        (Over.homMk (homOfLE hWU₀) :
          (Over.mk (homOfLE hWU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op
        ((σ.s i).val (op (Over.mk (𝟙 U₀)))) := by
  have hmor : (Over.homMk (homOfLE hWV) :
        (Over.mk (homOfLE hWU₀) : Over U₀) ⟶ Over.mk (homOfLE hVU₀)) ≫
        (Over.homMk (homOfLE hVU₀) :
          (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)) =
      (Over.homMk (homOfLE hWU₀) :
        (Over.mk (homOfLE hWU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)) := by
    apply Over.OverMorphism.ext
    apply Subsingleton.elim
  have hA := pushforwardGraded_map_conormalClass X J U₀ hVU₀ hWV hWU₀ z
  have hnat : (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hWU₀)))
        (((PresheafOfModules.pushforward₀ (Over.forget U₀) (quotientPresheaf X J)).obj
            (gradedPresheaf X J 1)).map
          (Over.homMk (homOfLE hWV) :
            (Over.mk (homOfLE hWU₀) : Over U₀) ⟶ Over.mk (homOfLE hVU₀)).op
          (conormalClass (sectionIdeal X J (op V)) z)) =
      (conormalOverTarget X J U₀).map
        (Over.homMk (homOfLE hWV) :
          (Over.mk (homOfLE hWU₀) : Over U₀) ⟶ Over.mk (homOfLE hVU₀)).op
        ((conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hVU₀)))
          (conormalClass (sectionIdeal X J (op V)) z)) :=
    PresheafOfModules.naturality_apply _ _ _
  have hop : (Over.homMk (homOfLE hVU₀) :
        (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op ≫
      (Over.homMk (homOfLE hWV) :
        (Over.mk (homOfLE hWU₀) : Over U₀) ⟶ Over.mk (homOfLE hVU₀)).op =
      (Over.homMk (homOfLE hWU₀) :
        (Over.mk (homOfLE hWU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op := by
    rw [← op_comp, hmor]
  rw [← hA, hnat, hz]
  refine ((PresheafOfModules.map_comp_apply (conormalOverTarget X J U₀)
    (Over.homMk (homOfLE hVU₀) :
      (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op
    (Over.homMk (homOfLE hWV) :
      (Over.mk (homOfLE hWU₀) : Over U₀) ⟶ Over.mk (homOfLE hVU₀)).op
    ((σ.s i).val (op (Over.mk (𝟙 U₀))))).symm).trans ?_
  rw [hop]

/-- **The chosen generating sections of the conormal sheaf come from sections of `J`.**
Near any point of `U₀`, each generating section is the conormal class of an honest
section of `J`, all on one common open. -/
lemma exists_local_conormal_lift (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U₀ : Opens X)
    (σ : ((conormalSheaf X J).over U₀).GeneratingSections) {r : ℕ} (e : Fin r ≃ σ.I)
    (x : X) (hx : x ∈ U₀) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU₀ : V ≤ U₀) (f : Fin r → J.obj (op V)),
      ∀ k : Fin r,
        (conormalSheafificationUnitOver X J U₀).app (op (Over.mk (homOfLE hVU₀)))
            (conormalClass (sectionIdeal X J (op V)) (f k)) =
          (conormalOverTarget X J U₀).map
            (Over.homMk (homOfLE hVU₀) :
              (Over.mk (homOfLE hVU₀) : Over U₀) ⟶ Over.mk (𝟙 U₀)).op
            ((σ.s (e k)).val (op (Over.mk (𝟙 U₀)))) := by
  classical
  choose V hxV hVU₀ z hz using fun k : Fin r =>
    exists_local_conormal_lift_at X J U₀ σ (e k) x hx
  obtain ⟨W, hxW, hWU₀, hWV⟩ := exists_common_open x U₀ V hx hxV
  exact ⟨W, hxW, hWU₀, fun k => ⟨X.presheaf.map (homOfLE (hWV k)).op (z k).val,
    J.toSubmodule.map_mem (homOfLE (hWV k)).op (z k).property⟩,
    fun k => conormal_lift_restrict X J U₀ σ (e k) (hVU₀ k) (hWV k) hWU₀ (z k) (hz k)⟩

end Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

end
