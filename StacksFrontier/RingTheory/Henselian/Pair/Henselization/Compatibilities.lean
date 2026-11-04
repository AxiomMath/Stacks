module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import StacksFrontier.Algebra.Category.CommAlgCat.FilteredColimits
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Unramified.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Henselian.AbsolutelyIntegrallyClosed
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.Pair.Limits
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Ideal.SmulTop

/-!
# Henselization of a pair: compatibilities

The henselization of pairs commutes with filtered colimits of pairs, depends on `I` only through
`V(I)`, commutes with integral base change, and takes a finite intersection of pairwise comaximal
ideals to the product of the individual henselizations.

## Main results

* `henselization_preserves_filtered_colimits`: compatibility with filtered colimits of pairs.
* `henselizations_equiv_of_zeroLocus_eq`: the henselization depends only on `V(I)`.
* `henselization_tensorProduct_bijective_of_isIntegral`: compatibility with integral base change.
* `henselization_iInf_equiv_pi`: the henselization at a finite intersection of pairwise comaximal
  ideals is the product of the henselizations.

## References

* [Stacks: Tag 0EM7](https://stacks.math.columbia.edu/tag/0EM7)
-/

public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Polynomial
open scoped TensorProduct
open Stacks.Henselization.EtaleColimit

universe u v w

section

/-- The underlying cocone of types has the universal property in every target universe. -/
private lemma coconeTypes_isColimit
    {K : Type v} [SmallCategory K] [IsFiltered K]
    (F : Functor K CommRingCat.{max u v}) (c : Cocone F) (hc : IsColimit c) :
    ((F ⋙ forget CommRingCat).coconeTypesEquiv.symm
      ((forget CommRingCat).mapCocone c)).IsColimit := by
  let h0 := CommRingCat.FilteredColimits.colimitCoconeIsColimit.{v, u} F
  let e0 := h0.coconePointUniqueUpToIso hc
  let e : (F ⋙ forget CommRingCat).ColimitType ≃ c.pt :=
    { toFun := e0.hom.hom
      invFun := e0.inv.hom
      left_inv := fun x ↦ ConcreteCategory.congr_hom e0.hom_inv_id x
      right_inv := fun x ↦ ConcreteCategory.congr_hom e0.inv_hom_id x }
  exact (F ⋙ forget CommRingCat).isColimit_coconeTypes.of_equiv e (fun k x ↦
    (ConcreteCategory.congr_hom (h0.comp_coconePointUniqueUpToIso_hom hc k) x).symm)

/-- Descend a compatible family of ring homomorphisms to an arbitrary target universe. -/
private noncomputable def ringHomDesc
    {K : Type v} [SmallCategory K] [IsFiltered K]
    (F : Functor K CommRingCat.{max u v}) (c : Cocone F) (hc : IsColimit c)
    {B : Type w} [CommRing B] (g : ∀ k, F.obj k →+* B)
    (hg : ∀ {j k} (f : j ⟶ k), g j = (g k).comp (F.map f).hom) : c.pt →+* B := by
  have hcT := coconeTypes_isColimit F c hc
  let gT : (F ⋙ forget CommRingCat).CoconeTypes :=
    { pt := B
      ι := fun k ↦ g k
      ι_naturality := fun f ↦ by
        funext x
        exact DFunLike.congr_fun (hg f).symm x }
  let d : c.pt → B := hcT.desc gT
  have hd (k : K) (x : F.obj k) : d ((c.ι.app k).hom x) = g k x :=
    hcT.fac_apply gT k x
  have key (x y : c.pt) : ∃ (l : K) (x' y' : F.obj l),
      (c.ι.app l).hom x' = x ∧ (c.ι.app l).hom y' = y := by
    obtain ⟨j, x', hx'⟩ := hcT.ι_jointly_surjective x
    obtain ⟨k, y', hy'⟩ := hcT.ι_jointly_surjective y
    refine ⟨IsFiltered.max j k, (F.map (IsFiltered.leftToMax j k)).hom x',
      (F.map (IsFiltered.rightToMax j k)).hom y', ?_, ?_⟩
    · rw [← hx']
      exact ConcreteCategory.congr_hom (c.w (IsFiltered.leftToMax j k)) x'
    · rw [← hy']
      exact ConcreteCategory.congr_hom (c.w (IsFiltered.rightToMax j k)) y'
  refine
    { toFun := d
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }
  · let k : K := (IsFiltered.nonempty (C := K)).some
    rw [← (c.ι.app k).hom.map_one, hd]
    exact (g k).map_one
  · intro x y
    obtain ⟨l, x', y', rfl, rfl⟩ := key x y
    rw [← map_mul, hd, hd, hd]
    exact (g l).map_mul _ _
  · let k : K := (IsFiltered.nonempty (C := K)).some
    rw [← (c.ι.app k).hom.map_zero, hd]
    exact (g k).map_zero
  · intro x y
    obtain ⟨l, x', y', rfl, rfl⟩ := key x y
    rw [← map_add, hd, hd, hd]
    exact (g l).map_add _ _

private lemma ringHomDesc_comp
    {K : Type v} [SmallCategory K] [IsFiltered K]
    (F : Functor K CommRingCat.{max u v}) (c : Cocone F) (hc : IsColimit c)
    {B : Type w} [CommRing B] (g : ∀ k, F.obj k →+* B)
    (hg : ∀ {j k} (f : j ⟶ k), g j = (g k).comp (F.map f).hom) (k : K) :
    (ringHomDesc F c hc g hg).comp (c.ι.app k).hom = g k := by
  ext x
  dsimp only [ringHomDesc]
  exact (coconeTypes_isColimit F c hc).fac_apply _ k x

private lemma ringHom_ext_of_isColimit
    {K : Type v} [SmallCategory K] [IsFiltered K]
    (F : Functor K CommRingCat.{max u v}) (c : Cocone F) (hc : IsColimit c)
    {B : Type w} [CommRing B] (f g : c.pt →+* B)
    (h : ∀ k, f.comp (c.ι.app k).hom = g.comp (c.ι.app k).hom) : f = g := by
  apply RingHom.ext
  intro x
  have hcT := coconeTypes_isColimit F c hc
  obtain ⟨k, y, hy⟩ := hcT.ι_jointly_surjective x
  change (c.ι.app k).hom y = x at hy
  rw [← hy]
  exact DFunLike.congr_fun (h k) y

/-- Henselization of pairs commutes with filtered colimits. More precisely, for a filtered diagram
of pairs and its naturally induced diagram of henselizations, any colimit of the latter is a
henselization of the colimit of the former. Its extended ideal is the supremum of the images of the
extended ideals at the stages. -/
@[stacks 0A04]
theorem henselization_preserves_filtered_colimits
    {K : Type v} [SmallCategory K] [IsFiltered K]
    (F Fh : Functor K CommRingCat.{max u v})
    (I : ∀ k, Ideal (F.obj k))
    (hI : ∀ ⦃j k⦄ (f : j ⟶ k), Ideal.map (F.map f).hom (I j) ≤ I k)
    (η : F ⟶ Fh)
    (hFh : ∀ k, HenselianPair (Fh.obj k) (Ideal.map (η.app k).hom (I k)))
    (hη : ∀ k (B : Type w) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J →
        ∀ f : F.obj k →+* B, I k ≤ J.comap f →
          ∃! g : Fh.obj k →+* B,
            g.comp (η.app k).hom = f ∧ Ideal.map (η.app k).hom (I k) ≤ J.comap g)
    (c : Cocone F) (hc : IsColimit c)
    (ch : Cocone Fh) (hch : IsColimit ch) :
    let ηc : c.pt →+* ch.pt := (hc.desc (Cocone.mk ch.pt (η ≫ ch.ι))).hom
    let Ic : Ideal c.pt := ⨆ k, Ideal.map (c.ι.app k).hom (I k)
    Ideal.map ηc Ic =
        (⨆ k, (Ideal.map ((ch.ι.app k).hom.comp (η.app k).hom) (I k) : Ideal ch.pt)) ∧
      HenselianPair ch.pt (Ideal.map ηc Ic) ∧
      ∀ (B : Type w) (_ : CommRing B) (J : Ideal B),
        HenselianPair B J →
          ∀ f : c.pt →+* B, Ic ≤ J.comap f →
            ∃! g : ch.pt →+* B,
              g.comp ηc = f ∧ Ideal.map ηc Ic ≤ J.comap g := by
  dsimp only
  let ηc : c.pt →+* ch.pt := (hc.desc (Cocone.mk ch.pt (η ≫ ch.ι))).hom
  let Ic : Ideal c.pt := ⨆ k, Ideal.map (c.ι.app k).hom (I k)
  have hηc (k : K) : ηc.comp (c.ι.app k).hom =
      (ch.ι.app k).hom.comp (η.app k).hom := by
    show (c.ι.app k ≫ hc.desc (Cocone.mk ch.pt (η ≫ ch.ι))).hom = _
    exact congrArg CommRingCat.Hom.hom (hc.fac (Cocone.mk ch.pt (η ≫ ch.ι)) k)
  have hideal : Ideal.map ηc Ic =
      (⨆ k, (Ideal.map ((ch.ι.app k).hom.comp (η.app k).hom) (I k) : Ideal ch.pt)) := by
    simp only [Ic, Ideal.map_iSup, Ideal.map_map, hηc]
  refine ⟨hideal, ?_, ?_⟩
  · rw [hideal]
    simpa only [← Ideal.map_map] using henselianPair_colimit Fh
      (fun k ↦ Ideal.map (η.app k).hom (I k)) (fun {j k} f ↦ by
        rw [Ideal.map_map]
        have hn := congrArg CommRingCat.Hom.hom (η.naturality f)
        have hn' : (Fh.map f).hom.comp (η.app j).hom =
            (η.app k).hom.comp (F.map f).hom := by
          exact hn.symm
        rw [hn', ← Ideal.map_map]
        exact Ideal.map_mono (hI f)) ch hch hFh
  · intro B _ J hBJ f hf
    let fk (k : K) : F.obj k →+* B := f.comp (c.ι.app k).hom
    have hfk (k : K) : I k ≤ J.comap (fk k) := by
      intro x hx
      exact hf (Ideal.mem_iSup_of_mem k (Ideal.mem_map_of_mem (c.ι.app k).hom hx))
    choose g hg hgu using fun k ↦ hη k B (inferInstance : CommRing B) J hBJ (fk k) (hfk k)
    have gnat {j k} (a : j ⟶ k) :
        g j = (g k).comp (Fh.map a).hom := by
      symm
      apply hgu j
      have hn : (Fh.map a).hom.comp (η.app j).hom =
          (η.app k).hom.comp (F.map a).hom :=
        (congrArg CommRingCat.Hom.hom (η.naturality a)).symm
      constructor
      · rw [RingHom.comp_assoc]
        rw [hn, ← RingHom.comp_assoc, (hg k).1]
        have hw := congrArg CommRingCat.Hom.hom (c.w a)
        change (c.ι.app k).hom.comp (F.map a).hom = (c.ι.app j).hom at hw
        exact congrArg (fun q ↦ f.comp q) hw
      · rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, RingHom.comp_assoc, hn,
          ← RingHom.comp_assoc, (hg k).1, ← Ideal.comap_comap,
          ← Ideal.map_le_iff_le_comap]
        exact (hI a).trans (hfk k)
    let G : ch.pt →+* B := ringHomDesc Fh ch hch g gnat
    have hG (k : K) : G.comp (ch.ι.app k).hom = g k :=
      ringHomDesc_comp Fh ch hch g gnat k
    refine ⟨G, ?_, ?_⟩
    · constructor
      · exact ringHom_ext_of_isColimit.{u, v, w} F c hc (G.comp ηc) f
          (fun k ↦ by
            rw [RingHom.comp_assoc, hηc, ← RingHom.comp_assoc, hG, (hg k).1])
      · rw [hideal]
        refine iSup_le fun k ↦ ?_
        rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← RingHom.comp_assoc, hG,
          ← Ideal.comap_comap, ← Ideal.map_le_iff_le_comap]
        exact (hg k).2
    · intro G' hG'
      have hstage (k : K) : G'.comp (ch.ι.app k).hom = g k := by
        apply hgu k
        constructor
        · rw [RingHom.comp_assoc, ← hηc, ← RingHom.comp_assoc, hG'.1]
        · have hk : Ideal.map ((ch.ι.app k).hom.comp (η.app k).hom) (I k) ≤
              ⨆ l, (Ideal.map ((ch.ι.app l).hom.comp (η.app l).hom) (I l) : Ideal ch.pt) :=
            le_iSup (fun l : K ↦
              (Ideal.map ((ch.ι.app l).hom.comp (η.app l).hom) (I l) : Ideal ch.pt)) k
          have hall : (⨆ l, (Ideal.map
              ((ch.ι.app l).hom.comp (η.app l).hom) (I l) : Ideal ch.pt)) ≤
              J.comap G' := by
            rw [← hideal]
            exact hG'.2
          rw [← Ideal.comap_comap, ← Ideal.map_le_iff_le_comap, Ideal.map_map]
          exact hk.trans hall
      exact ringHom_ext_of_isColimit.{u, v, w} Fh ch hch G' G
        (fun k ↦ by rw [hstage, hG])

end

section

private lemma zeroLocus_map_eq_of_zeroLocus_eq
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (I J : Ideal A)
    (h : PrimeSpectrum.zeroLocus (I : Set A) = PrimeSpectrum.zeroLocus (J : Set A)) :
    PrimeSpectrum.zeroLocus (I.map f : Set B) =
      PrimeSpectrum.zeroLocus (J.map f : Set B) := by
  ext p
  show I.map f ≤ p.asIdeal ↔ J.map f ≤ p.asIdeal
  rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  exact Set.ext_iff.mp h ⟨Ideal.comap f p.asIdeal, inferInstance⟩

private theorem map_le_comap_of_comp {A R S : Type*} [CommRing A] [CommRing R]
    [CommRing S] (I : Ideal A) (f : A →+* R) (g : R →+* S)
    (b : A →+* S) (J : Ideal S) (hb : I ≤ J.comap b) (hg : g.comp f = b) :
    I.map f ≤ J.comap g := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hg]
  exact hb

/-- An endomorphism of a henselization over the base ring is the identity. -/
private lemma eq_id_of_comp_eq {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A)
    (f : A →+* B) (hB : HenselianPair B (I.map f))
    (hU : ∀ (C : Type u) (_ : CommRing C) (K : Ideal C),
      HenselianPair C K →
        ∀ g : A →+* C, I ≤ K.comap g →
          ∃! h : B →+* C, h.comp f = g ∧ I.map f ≤ K.comap h)
    (φ : B →+* B) (hφ : φ.comp f = f) : φ = RingHom.id B :=
  (hU B inferInstance _ hB f Ideal.le_comap_map).unique
    ⟨hφ, map_le_comap_of_comp _ _ _ _ _ Ideal.le_comap_map hφ⟩
    ⟨RingHom.id_comp _, map_le_comap_of_comp _ _ _ _ _ Ideal.le_comap_map (RingHom.id_comp _)⟩

/-- Henselization of a pair depends only on the radical of its ideal: two ideals with the same
vanishing locus give canonically isomorphic henselizations over the base ring. -/
@[stacks 0F0L]
theorem henselizations_equiv_of_zeroLocus_eq
    (A : Type u) [CommRing A] (I J : Ideal A)
    (AI AJ : Type u) [CommRing AI] [CommRing AJ] [Algebra A AI] [Algebra A AJ]
    (hAI : HenselianPair AI (I.map (algebraMap A AI)))
    (hAJ : HenselianPair AJ (J.map (algebraMap A AJ)))
    (hI : ∀ (B : Type u) (_ : CommRing B) (K : Ideal B),
      HenselianPair B K →
        ∀ f : A →+* B, I ≤ K.comap f →
          ∃! g : AI →+* B,
            g.comp (algebraMap A AI) = f ∧ I.map (algebraMap A AI) ≤ K.comap g)
    (hJ : ∀ (B : Type u) (_ : CommRing B) (K : Ideal B),
      HenselianPair B K →
        ∀ f : A →+* B, J ≤ K.comap f →
          ∃! g : AJ →+* B,
            g.comp (algebraMap A AJ) = f ∧ J.map (algebraMap A AJ) ≤ K.comap g)
    (hIJ : PrimeSpectrum.zeroLocus (I : Set A) = PrimeSpectrum.zeroLocus (J : Set A)) :
    ∃! e : AI ≃+* AJ,
      e.toRingHom.comp (algebraMap A AI) = algebraMap A AJ := by
  have hAIJ := zeroLocus_map_eq_of_zeroLocus_eq (algebraMap A AI) I J hIJ
  have hAJI := zeroLocus_map_eq_of_zeroLocus_eq (algebraMap A AJ) I J hIJ
  have hAI' : HenselianPair AI (J.map (algebraMap A AI)) :=
    (henselianPair_iff_of_zeroLocus_eq _ _ hAIJ).mp hAI
  have hAJ' : HenselianPair AJ (I.map (algebraMap A AJ)) :=
    (henselianPair_iff_of_zeroLocus_eq _ _ hAJI).mpr hAJ
  obtain ⟨g, hg, hg_unique⟩ := hI AJ inferInstance _ hAJ' (algebraMap A AJ) Ideal.le_comap_map
  obtain ⟨f, hf, hf_unique⟩ := hJ AI inferInstance _ hAI' (algebraMap A AI) Ideal.le_comap_map
  have hfg : f.comp g = RingHom.id AI :=
    eq_id_of_comp_eq I _ hAI hI _ (by rw [RingHom.comp_assoc, hg.1, hf.1])
  have hgf : g.comp f = RingHom.id AJ :=
    eq_id_of_comp_eq J _ hAJ hJ _ (by rw [RingHom.comp_assoc, hf.1, hg.1])
  let e : AI ≃+* AJ := RingEquiv.ofRingHom g f hgf hfg
  refine ⟨e, hg.1, ?_⟩
  intro e' he'
  apply RingEquiv.ext
  have heq := hg_unique e'.toRingHom ⟨he', map_le_comap_of_comp I _ _ _ _ Ideal.le_comap_map he'⟩
  intro x
  exact DFunLike.congr_fun heq x

end

section

/-- Henselization commutes with integral base change. For an integral map of pairs
`(A, I) → (B, J)` for which `J` and `IB` have the same vanishing locus, the canonical map
`Aʰ ⊗[A] B → Bʰ` induced by the map of henselizations is an isomorphism. -/
@[stacks 0DYE]
theorem henselization_tensorProduct_bijective_of_isIntegral
    (A Ah : Type u) (B Bh : Type v) [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [IsScalarTower A B Bh]
    [Algebra.IsIntegral A B] (I : Ideal A) (J : Ideal B)
    (hmap : I ≤ J.comap (algebraMap A B))
    (hzero : PrimeSpectrum.zeroLocus (J : Set B) =
      PrimeSpectrum.zeroLocus (I.map (algebraMap A B) : Set B))
    (hAh : HenselianPair Ah (I.map (algebraMap A Ah)))
    (hBh : HenselianPair Bh (J.map (algebraMap B Bh)))
    (hAh_univ : ∀ (C : Type (max u v)) (_ : CommRing C) (K : Ideal C),
      HenselianPair C K →
        ∀ f : A →+* C, I ≤ K.comap f →
          ∃! g : Ah →+* C,
            g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ K.comap g)
    (hBh_univ : ∀ (C : Type (max u v)) (_ : CommRing C) (K : Ideal C),
      HenselianPair C K →
        ∀ f : B →+* C, J ≤ K.comap f →
          ∃! g : Bh →+* C,
            g.comp (algebraMap B Bh) = f ∧ J.map (algebraMap B Bh) ≤ K.comap g)
    (g : Ah →ₐ[A] Bh)
    (hg : I.map (algebraMap A Ah) ≤ (J.map (algebraMap B Bh)).comap g) :
    Function.Bijective
      (Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom A B Bh)
        (fun _ _ ↦ Commute.all _ _)) := by
  let T := Ah ⊗[A] B
  let iA : Ah →+* T := Algebra.TensorProduct.includeLeftRingHom
  let iB : B →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let K : Ideal T := J.map iB
  have hT0 : HenselianPair T
      ((I.map (algebraMap A Ah)).map iA) :=
    henselianPair_map_of_isIntegral _ hAh
  have hi : iA.comp (algebraMap A Ah) = iB.comp (algebraMap A B) := by
    ext a
    simp [iA, iB, T]
  have hzeroT : PrimeSpectrum.zeroLocus (K : Set T) =
      PrimeSpectrum.zeroLocus ((I.map (algebraMap A Ah)).map iA : Set T) := by
    dsimp [K]
    rw [Ideal.map_map]
    rw [hi]
    simpa only [Ideal.map_map] using
      zeroLocus_map_eq_of_zeroLocus_eq iB J (I.map (algebraMap A B)) hzero
  have hTK : HenselianPair T K :=
    (henselianPair_iff_of_zeroLocus_eq K
      ((I.map (algebraMap A Ah)).map iA) hzeroT).mpr hT0
  have hJK : J ≤ K.comap iB := Ideal.le_comap_map
  obtain ⟨k, hk, hk_unique⟩ := hBh_univ T inferInstance K hTK iB hJK
  let φ : T →+* Bh :=
    (Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom A B Bh)
      (fun _ _ ↦ Commute.all _ _)).toRingHom
  have hφiA : φ.comp iA = g.toRingHom := by
    ext a
    simp [φ, iA, T]
  have hφiB : φ.comp iB = algebraMap B Bh := by
    ext b
    simp [φ, iB, T]
  have hkφ : k.comp φ = RingHom.id T := by
    apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro a
      have hkgA : (k.comp g.toRingHom).comp (algebraMap A Ah) =
          iA.comp (algebraMap A Ah) := by
        ext x
        calc
          k (g (algebraMap A Ah x)) = k (algebraMap A Bh x) := congrArg k (g.commutes x)
          _ = k (algebraMap B Bh (algebraMap A B x)) := by
            rw [IsScalarTower.algebraMap_apply A B Bh]
          _ = iB (algebraMap A B x) := DFunLike.congr_fun hk.1 _
          _ = iA (algebraMap A Ah x) := DFunLike.congr_fun hi.symm _
      have hkgI : I.map (algebraMap A Ah) ≤ K.comap (k.comp g.toRingHom) := by
        intro x hx
        exact hk.2 (hg hx)
      have hiAI : I.map (algebraMap A Ah) ≤ K.comap iA := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hi]
        rw [← Ideal.map_map]
        exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr hmap)
      have hbase : I ≤ K.comap (iA.comp (algebraMap A Ah)) :=
        fun x hx ↦ hiAI (Ideal.mem_map_of_mem _ hx)
      obtain ⟨q, hq, huniqA⟩ := hAh_univ T inferInstance K hTK
        (iA.comp (algebraMap A Ah)) hbase
      show k ((φ.comp iA) a) = iA a
      rw [hφiA]
      exact DFunLike.congr_fun
        ((huniqA _ ⟨hkgA, hkgI⟩).trans (huniqA _ ⟨rfl, hiAI⟩).symm) a
    · apply RingHom.ext
      intro b
      show k ((φ.comp iB) b) = iB b
      rw [hφiB]
      exact DFunLike.congr_fun hk.1 b
  have hφk : φ.comp k = RingHom.id Bh := by
    have hφK : K ≤ (J.map (algebraMap B Bh)).comap φ := by
      rw [← Ideal.map_le_iff_le_comap]
      show (J.map iB).map φ ≤ J.map (algebraMap B Bh)
      rw [Ideal.map_map, hφiB]
    let U := ULift.{max u v, v} Bh
    let up : Bh →+* U := ULift.ringEquiv.symm.toRingHom
    let L : Ideal U := (J.map (algebraMap B Bh)).map up
    have hUL : HenselianPair U L :=
      henselianPair_map_of_isIntegral _ hBh
    have hbaseU : J ≤ L.comap (up.comp (algebraMap B Bh)) := by
      intro x hx
      exact Ideal.mem_map_of_mem up (Ideal.mem_map_of_mem _ hx)
    obtain ⟨q, hq, huniqU⟩ := hBh_univ U inferInstance L hUL
      (up.comp (algebraMap B Bh)) hbaseU
    have heq : up.comp (φ.comp k) = up :=
      (huniqU _ ?_).trans (huniqU _ ?_).symm
    · exact RingHom.ext fun y => ULift.ringEquiv.symm.injective (DFunLike.congr_fun heq y)
    · constructor
      · rw [RingHom.comp_assoc, RingHom.comp_assoc]
        congr 1
        apply RingHom.ext
        intro b
        show φ ((k.comp (algebraMap B Bh)) b) = algebraMap B Bh b
        rw [hk.1]
        exact DFunLike.congr_fun hφiB b
      · intro x hx
        exact Ideal.mem_map_of_mem up (hφK (hk.2 hx))
    · constructor
      · rfl
      · exact Ideal.le_comap_map
  constructor
  · intro x y hxy
    have := congrArg k hxy
    change (k.comp φ) x = (k.comp φ) y at this
    rwa [hkφ] at this
  · intro y
    refine ⟨k y, ?_⟩
    exact DFunLike.congr_fun hφk y

end

section

private theorem henselianPair_quotient {R : Type u} [CommRing R] {J : Ideal R}
    (h : HenselianPair R J) (K : Ideal R) :
    HenselianPair (R ⧸ K) (J.map (Ideal.Quotient.mk K)) := by
  apply ((henselianPair_tfae.{u,u} (R ⧸ K)
    (J.map (Ideal.Quotient.mk K))).out 4 1).mp
  intro B _ _ _
  let : Algebra R B := ((algebraMap (R ⧸ K) B).comp (algebraMap R (R ⧸ K))).toAlgebra
  let : IsScalarTower R (R ⧸ K) B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.IsIntegral R B := Algebra.IsIntegral.trans (R ⧸ K)
  have hb : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.IsIntegral R S],
      InducesBijectionOnIdempotents (J.map (algebraMap R S)) :=
    ((henselianPair_tfae.{u,u} R J).out 1 4).mp h
  rw [Ideal.map_map]
  show InducesBijectionOnIdempotents (J.map (algebraMap R B))
  exact hb B

private theorem lift_completeOrthogonalIdempotents {R : Type u} [CommRing R]
    {J : Ideal R} (h : InducesBijectionOnIdempotents J)
    {ι : Type v} [Fintype ι] (d : ι → R ⧸ J) (hd : CompleteOrthogonalIdempotents d) :
    ∃ e : ι → R, CompleteOrthogonalIdempotents e ∧
      ∀ i, Ideal.Quotient.mk J (e i) = d i := by
  have hs := h.2
  have hi := h.1
  choose e he using fun i => hs ⟨d i, hd.idem i⟩
  have heq (i) : Ideal.Quotient.mk J (e i).val = d i := congrArg Subtype.val (he i)
  have hortho : OrthogonalIdempotents (fun i => (e i).val) := by
    refine ⟨fun i => (e i).property, ?_⟩
    intro i j hij
    have hij' : idemMap J ⟨(e i).val * (e j).val, (e i).property.mul (e j).property⟩ =
        idemMap J ⟨0, IsIdempotentElem.zero⟩ := by
      apply Subtype.ext
      show Ideal.Quotient.mk J ((e i).val * (e j).val) = Ideal.Quotient.mk J 0
      rw [map_mul, heq, heq, hd.ortho hij, map_zero]
    exact congrArg Subtype.val (hi hij')
  refine ⟨fun i => (e i).val, ⟨hortho, ?_⟩, heq⟩
  have heq' : idemMap J ⟨∑ i, (e i).val, hortho.isIdempotentElem_sum⟩ =
      idemMap J ⟨1, IsIdempotentElem.one⟩ := by
    apply Subtype.ext
    show Ideal.Quotient.mk J (∑ i, (e i).val) = Ideal.Quotient.mk J 1
    simp only [map_sum, heq, hd.complete, map_one]
  exact congrArg Subtype.val (hi heq')

private theorem exists_crt_idempotents {ι : Type w} [Fintype ι] [DecidableEq ι]
    {A : Type u} [CommRing A] (I : ι → Ideal A)
    (hI : ∀ i j, i ≠ j → I i ⊔ I j = ⊤)
    {R : Type v} [CommRing R] (f : A →+* R) {J : Ideal R}
    (hJ : HenselianPair R J) (hf : (⨅ i, I i) ≤ J.comap f) :
    ∃ (a : ι → A) (e : ι → R), CompleteOrthogonalIdempotents e ∧
      (∀ i j, Ideal.Quotient.mk (I j) (a i) = if i = j then 1 else 0) ∧
      ∀ i, e i - f (a i) ∈ J := by
  classical
  let c := Ideal.quotientInfRingEquivPiQuotient I (fun i j h =>
    Ideal.isCoprime_iff_sup_eq.mpr (hI i j h))
  let d : ι → A ⧸ ⨅ i, I i := fun i => c.symm (Pi.single i 1)
  have hd : CompleteOrthogonalIdempotents d :=
    (CompleteOrthogonalIdempotents.single (fun i => A ⧸ I i)).map c.symm.toRingHom
  choose a ha using fun i => Ideal.Quotient.mk_surjective (d i)
  let q : (A ⧸ ⨅ i, I i) →+* R ⧸ J :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk J).comp f)
      (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hf hx))
  obtain ⟨e, he, heq⟩ := lift_completeOrthogonalIdempotents
    ⟨idemMap_injective J hJ.1, idemMap_surjective_of_lifting J hJ.2⟩ (q ∘ d) (hd.map q)
  refine ⟨a, e, he, ?_, ?_⟩
  · intro i j
    have hh := congrArg (fun z => c z j) (ha i)
    change Ideal.Quotient.mk (I j) (a i) = _ at hh
    rw [show c (d i) = Pi.single i 1 from c.apply_symm_apply _] at hh
    by_cases hij : i = j
    · subst j
      simpa using hh
    · simpa [Pi.single_eq_of_ne (Ne.symm hij), hij] using hh
  · intro i
    apply Ideal.Quotient.eq.mp
    rw [heq, Function.comp_apply, ← ha i]
    rfl

/-- Let `(I i)` be a finite nonempty family of pairwise comaximal ideals of a commutative ring `A`.
For arbitrary choices of a henselization `Aʰ` of `A` along `⨅ i, I i` and henselizations `Aʰᵢ`
along each `I i`, the natural map from `Aʰ` to the product of the `Aʰᵢ` is an isomorphism. The
displayed compatibility with the structure maps identifies this isomorphism canonically. -/
@[stacks 0H7Q]
theorem henselization_iInf_equiv_pi {ι : Type} [Finite ι] [Nonempty ι]
    (A : Type u) [CommRing A] (I : ι → Ideal A)
    (hI : ∀ i j, i ≠ j → I i ⊔ I j = ⊤)
    (Ah : Type u) [CommRing Ah] (algebraMap_h : A →+* Ah)
    (hAh : HenselianPair Ah ((⨅ i, I i).map algebraMap_h) ∧
      ∀ (B : Type u) (_ : CommRing B) (J : Ideal B),
        HenselianPair B J →
          ∀ f : A →+* B, (⨅ i, I i) ≤ J.comap f →
            ∃! g : Ah →+* B,
              g.comp algebraMap_h = f ∧ (⨅ i, I i).map algebraMap_h ≤ J.comap g)
    (Ahi : ι → Type u) [∀ i, CommRing (Ahi i)] (algebraMap_i : ∀ i, A →+* Ahi i)
    (hAhi : ∀ i, HenselianPair (Ahi i) ((I i).map (algebraMap_i i)) ∧
      ∀ (B : Type u) (_ : CommRing B) (J : Ideal B),
        HenselianPair B J →
          ∀ f : A →+* B, I i ≤ J.comap f →
            ∃! g : Ahi i →+* B,
              g.comp (algebraMap_i i) = f ∧ (I i).map (algebraMap_i i) ≤ J.comap g) :
    ∃! e : Ah ≃+* (∀ i, Ahi i),
      ∀ (a : A) (i : ι), e (algebraMap_h a) i = algebraMap_i i a := by
  classical
  let := Fintype.ofFinite ι
  let J := (⨅ i, I i).map algebraMap_h
  obtain ⟨a, e, he, ha, hea⟩ := exists_crt_idempotents I hI algebraMap_h hAh.1
    Ideal.le_comap_map
  let K : ι → Ideal Ah := fun i => Ideal.span {1 - e i}
  let C : ι → Type u := fun i => Ah ⧸ K i
  let q : ∀ i, Ah →+* C i := fun i => Ideal.Quotient.mk (K i)
  have hqe (i) : q i (e i) = 1 := by
    have hz : q i (1 - e i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    exact (sub_eq_zero.mp (by simpa only [map_sub, map_one] using hz)).symm
  have hC (i) : HenselianPair (C i) (J.map (q i)) :=
    henselianPair_quotient hAh.1 (K i)
  have hIC (i) : I i ≤ (J.map (q i)).comap ((q i).comp algebraMap_h) := by
    intro x hx
    have hax : a i * x ∈ ⨅ j, I j := by
      apply Ideal.mem_iInf.mpr
      intro j
      by_cases hij : i = j
      · subst j
        exact (I i).mul_mem_left _ hx
      · have haj : a i ∈ I j := Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [hij] using ha i j)
        exact (I j).mul_mem_right _ haj
    have hex : e i * algebraMap_h x ∈ J := by
      have h₁ := J.mul_mem_right (algebraMap_h x) (hea i)
      have h₂ : algebraMap_h (a i * x) ∈ J := Ideal.mem_map_of_mem _ hax
      convert J.add_mem h₁ h₂ using 1
      simp only [map_mul]
      ring
    have hh := Ideal.mem_map_of_mem (q i) hex
    simpa only [map_mul, hqe, one_mul, Ideal.mem_comap, RingHom.comp_apply] using hh
  choose c hc using fun i => (hAhi i).2 (C i) inferInstance (J.map (q i)) (hC i)
    ((q i).comp algebraMap_h) (hIC i)
  have hAi (i) : (⨅ j, I j) ≤ ((I i).map (algebraMap_i i)).comap (algebraMap_i i) :=
    (iInf_le I i).trans Ideal.le_comap_map
  choose b hb using fun i => hAh.2 (Ahi i) inferInstance ((I i).map (algebraMap_i i))
    (hAhi i).1 (algebraMap_i i) (hAi i)
  have hbe (i) : b i (e i) = 1 := by
    apply IsIdempotentElem.eq_of_sub_mem_jacobson ((he.idem i).map (b i)) IsIdempotentElem.one
    apply (hAhi i).1.1
    have h₁ : b i (e i - algebraMap_h (a i)) ∈ (I i).map (algebraMap_i i) :=
      (hb i).1.2 (hea i)
    have hai : a i - 1 ∈ I i := Ideal.Quotient.eq.mp (by simpa using ha i i)
    have h₂ := Ideal.mem_map_of_mem (algebraMap_i i) hai
    have hcomp : b i (algebraMap_h (a i)) = algebraMap_i i (a i) :=
      DFunLike.congr_fun (hb i).1.1 (a i)
    convert ((I i).map (algebraMap_i i)).add_mem h₁ h₂ using 1
    simp only [map_sub, map_one, hcomp]
    ring
  have hKb (i) : K i ≤ RingHom.ker (b i) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show b i (1 - e i) = 0
    simp only [map_sub, map_one, hbe, sub_self]
  let d : ∀ i, C i →+* Ahi i := fun i =>
    Ideal.Quotient.lift (K i) (b i) (fun x hx => hKb i hx)
  have hdq (i) : (d i).comp (q i) = b i := Ideal.Quotient.lift_comp_mk _ _ _
  have hdc (i) : (d i).comp (c i) = RingHom.id (Ahi i) :=
    eq_id_of_comp_eq _ _ (hAhi i).1 (hAhi i).2 _ (by
      rw [RingHom.comp_assoc, (hc i).1.1, ← RingHom.comp_assoc, hdq, (hb i).1.1])
  let E : Ah ≃+* (∀ i, C i) := RingEquiv.ofBijective (RingHom.pi q) he.bijective_pi
  let g : Ah →+* (∀ i, Ahi i) := RingHom.pi b
  let r : (∀ i, Ahi i) →+* Ah := E.symm.toRingHom.comp
    (RingHom.pi (fun i => (c i).comp (Pi.evalRingHom Ahi i)))
  have hqr (x : ∀ i, Ahi i) (i) : q i (r x) = c i (x i) :=
    congrFun (E.apply_symm_apply (fun i => c i (x i))) i
  have hrgbase : (r.comp g).comp algebraMap_h = algebraMap_h := by
    ext x
    apply E.injective
    show (fun i => q i (r (g (algebraMap_h x)))) = fun i => q i (algebraMap_h x)
    funext i
    rw [hqr]
    show c i (b i (algebraMap_h x)) = q i (algebraMap_h x)
    have hbx : b i (algebraMap_h x) = algebraMap_i i x := DFunLike.congr_fun (hb i).1.1 x
    rw [hbx]
    exact DFunLike.congr_fun (hc i).1.1 x
  have hrg : r.comp g = RingHom.id Ah := eq_id_of_comp_eq _ _ hAh.1 hAh.2 _ hrgbase
  have hgr (x : ∀ i, Ahi i) : g (r x) = x := by
    funext i
    show b i (r x) = x i
    rw [← hdq]
    show d i (q i (r x)) = x i
    rw [hqr]
    exact DFunLike.congr_fun (hdc i) (x i)
  have hg : Function.Bijective g :=
    ⟨Function.LeftInverse.injective (show Function.LeftInverse r g from
        fun x => DFunLike.congr_fun hrg x),
      Function.RightInverse.surjective hgr⟩
  refine ⟨RingEquiv.ofBijective g hg, ?_, ?_⟩
  · intro x i
    exact DFunLike.congr_fun (hb i).1.1 x
  · intro e' he'
    apply RingEquiv.ext
    intro x
    funext i
    let b' := (Pi.evalRingHom Ahi i).comp e'.toRingHom
    have hbase : b'.comp algebraMap_h = algebraMap_i i := by
      ext y
      exact he' y i
    have hb' : b' = b i := (hb i).2 b'
      ⟨hbase, map_le_comap_of_comp _ _ _ _ _ (hAi i) hbase⟩
    exact DFunLike.congr_fun hb' x

end

end
