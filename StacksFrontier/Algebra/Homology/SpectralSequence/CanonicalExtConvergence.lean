module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
public import StacksFrontier.Algebra.Homology.SpectralSequence.Renumbering
public import StacksFrontier.Homology.Injectives.Ext.CanonicalSpectralSequence
public import StacksFrontier.Algebra.Homology.SpectralSequence.ExtBoundedConvergence

/-!
# Convergence of the Ext spectral sequences of the truncation filtrations

Let `M` be bounded above and `K` bounded below in the derived category of a Grothendieck
abelian category.  The spectral sequence of the canonical truncation filtration of a complex
representing `M`, and its renumbering, are bounded and converge to `Extⁿ(M, K)`.

For `K` bounded below and a cochain complex `M^•` bounded above, the spectral sequence of the
brutal truncation filtration `FᵖM^• = σ_{≥ p}M^•` is likewise bounded and converges to
`Extⁿ(M^•, K)`.

## Main definitions

* `canonicalExtFiltration` is the filtration of `Extⁿ(M, K)` induced by the canonical
  truncation filtration of a representative of `M`.
* `renumberedCanonicalExtSpectralSequence` is the canonical Ext spectral sequence with old
  page `r - 1` restricted along `(i, j) ↦ (-j, i + 2j)` to form new page `r`.

## Main results

* `renumberedCanonicalExtSpectralSequence_page_two` identifies the second page of the
  renumbered spectral sequence with `Extⁱ(H⁻ʲ(M), K)`.
* `canonicalExtSpectralSequence_isBounded` and
  `canonicalExtSpectralSequence_convergesToExt` give boundedness and convergence before
  renumbering.
* `renumberedCanonicalExtSpectralSequence_isBounded` and
  `renumberedCanonicalExtSpectralSequence_convergesToExt` give the same assertions after
  renumbering.
* `isBounded_canonicalExtSpectralSequence` and
  `convergesToExt_canonicalExtSpectralSequence` are those assertions for the canonical
  truncation filtration itself, that is, for `canonicalExtSpectralSequence`.
* `stupidExtSpectralSequence_isBounded` and `stupidExtSpectralSequence_convergesToExt` are
  boundedness and convergence for the brutal truncation filtration.

## Implementation notes

Both hypotheses of the bounded-convergence criterion are supplied by
`canonicalExtQuotientBounds`: the Ext groups out of `M / Fᵖ M` vanish once `p ≤ -m`, where `M`
is in degrees `≤ m`, because the inclusion `Fᵖ M ⟶ M` is then a quasi-isomorphism; and the
canonical maps out of those quotients are isomorphisms once `p` is large, because the two
outer Ext groups of the defining triangle vanish for degree reasons.

For the brutal truncation filtration the two hypotheses change places, and so do the two
boundedness assumptions, exactly as in the source: `M^•/σ_{≥ p}M^•` lives in degrees `< p`, so
the Ext groups out of it vanish for `p ≪ 0` because `K` is bounded below
(`stupidExtQuotient_isZero`), while `σ_{≥ p}M^•` vanishes altogether for `p` above the bound of
`M^•`, which makes the comparison map an isomorphism for `p ≫ 0`
(`stupidExtQuotient_isIso`).

Convergence is stated using the canonical finite increasing filtration on each target Ext
group together with an identification of its graded pieces with the infinity page.  The first
page at `(p, q)` uses the graded piece of the representative at filtration index `-p`, so the
corresponding Ext filtration quotient is the step from `-p` to `-p + 1`; under the change of
bidegree `(i, j) ↦ (-j, i + 2j)` that is the step from `j` to `j + 1`.

## References

* [Stacks Project, Tag 0G20](https://stacks.math.columbia.edu/tag/0G20)
* [Stacks Project, Tag 0G1Y](https://stacks.math.columbia.edu/tag/0G1Y)
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated
open CategoryTheory.SpectralSequence

namespace Stacks.Injectives

/-- 0G20 renumbered_e2, declaration 1. -/
@[stacks 0G20 "renumbered_e2"]
public noncomputable def renumberedCanonicalExtSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    {M K : DerivedCategory A} {M' : CochainComplex A ℤ}
    {e : DerivedCategory.Q.obj M' ≅ M}
    (S : CanonicalExtSpectralSequence M K M' e) :
    CohomologicalSpectralSequence AddCommGrpCat.{w} 2 :=
  truncationRenumber S.spectralSequence

/-- 0G20 renumbered_e2, declaration 2. -/
@[stacks 0G20 "renumbered_e2"]
public theorem renumberedCanonicalExtSpectralSequence_page_two
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    {M K : DerivedCategory A} {M' : CochainComplex A ℤ}
    {e : DerivedCategory.Q.obj M' ≅ M}
    (S : CanonicalExtSpectralSequence M K M' e) (i j : ℤ) :
    Nonempty
      (((renumberedCanonicalExtSpectralSequence S).page 2).X (i, j) ≅
        AddCommGrpCat.of
          (DerivedCategory.Ext ((DerivedCategory.singleFunctor A 0).obj
            ((DerivedCategory.homologyFunctor A (-j)).obj M)) K i)) :=
  ⟨truncationRenumber_pageXIso S.spectralSequence i j 2 1 (by omega) le_rfl (by omega) ≪≫
    S.e₁Iso (-j) (i + 2 * j) ≪≫
    eqToIso (by rw [show 2 * -j + (i + 2 * j) = i by omega])⟩

private lemma ext_isZero_of_isZero_source
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {X K : DerivedCategory A} (n : ℤ) (hX : IsZero X) :
    IsZero (AddCommGrpCat.of (DerivedCategory.Ext X K n)) := by
  let : Subsingleton (DerivedCategory.Ext X K n) := ⟨fun f g => hX.eq_of_src f g⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

private lemma ext_isZero_of_homology_lt
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : A) (K : DerivedCategory A) (b n : ℤ) (hK : K.IsGE b) (hn : n < b) :
    IsZero (AddCommGrpCat.of
      (DerivedCategory.Ext ((DerivedCategory.singleFunctor A 0).obj X) K n)) := by
  have hH : IsZero ((DerivedCategory.homologyFunctor A n).obj K) :=
    (DerivedCategory.isGE_iff K b).1 hK n hn
  have hbij := DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    ((DerivedCategory.singleFunctor A 0).obj X) K 0 b n n (by omega) (by omega)
  let : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor A 0).obj X) K n) := ⟨fun f g => by
    apply hbij.1
    calc
      ((DerivedCategory.homologyFunctor A 0).shiftMap f 0 n (by omega)) = 0 :=
        hH.eq_of_tgt _ _
      _ = ((DerivedCategory.homologyFunctor A 0).shiftMap g 0 n (by omega)) :=
        (hH.eq_of_tgt _ _).symm⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

private lemma triangle_mor₂_precomp_isIso
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) (Z : C)
    (h₀ : ∀ f : T.obj₁ ⟶ Z, f = 0)
    (h₁ : ∀ f : T.obj₁⟦(1 : ℤ)⟧ ⟶ Z, f = 0) :
    IsIso (AddCommGrpCat.ofHom
      ({ toFun := fun f : T.obj₃ ⟶ Z => T.mor₂ ≫ f
         map_zero' := by simp
         map_add' := by simp } : (T.obj₃ ⟶ Z) →+ (T.obj₂ ⟶ Z))) := by
  let h : (T.obj₃ ⟶ Z) →+ (T.obj₂ ⟶ Z) :=
    { toFun := fun f => T.mor₂ ≫ f
      map_zero' := by simp
      map_add' := by simp }
  have hb : Function.Bijective h := by
    refine ⟨fun f g hfg => ?_, fun f₂ => ?_⟩
    · change T.mor₂ ≫ f = T.mor₂ ≫ g at hfg
      obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ T hT (f - g)
        (by rw [Preadditive.comp_sub, hfg, sub_self])
      exact sub_eq_zero.mp (by simpa [h₁ k] using hk)
    · obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T hT f₂ (h₀ _)
      exact ⟨g, by simpa [h] using hg.symm⟩
  show IsIso (AddCommGrpCat.ofHom h)
  exact (ConcreteCategory.isIso_iff_bijective _).2 hb

/-- If the `p`-th step of a filtered complex lives in degrees `≤ a` and `K` in degrees `≥ c`, with
`a + n < c`, then `Extⁿ(M / Fᵖ M, K) ⟶ Extⁿ(M, K)` is an isomorphism. -/
private lemma isIso_extFromFilteredQuotient_of_isLE
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (F : CochainComplex.Filtered A) (p n a c : ℤ)
    (hF : (DerivedCategory.Q.obj (F.filtration.obj (op p))).IsLE a) (hK : K.IsGE c)
    (hac : a + n < c) :
    IsIso (extFromFilteredQuotient K F p n) := by
  let f := F.filtration.ι.app (op p)
  have hTsc : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    ShortComplex.shortExact_mk_cokernel_π f
  let T := DerivedCategory.triangleOfSES hTsc
  have : T.obj₁.IsLE a := hF
  have : T.obj₁⟦(1 : ℤ)⟧.IsLE (a - 1) :=
    DerivedCategory.TStructure.t.isLE_shift T.obj₁ a (1 : ℤ) (a - 1) (by omega)
  have : (K⟦n⟧).IsGE (c - n) :=
    DerivedCategory.TStructure.t.isGE_shift K c n (c - n) (by omega)
  exact triangle_mor₂_precomp_isIso T (DerivedCategory.triangleOfSES_distinguished hTsc) (K⟦n⟧)
    (fun g => DerivedCategory.TStructure.t.zero g a (c - n) (by omega))
    (fun g => DerivedCategory.TStructure.t.zero g (a - 1) (c - n) (by omega))

private lemma canonicalExtQuotientBounds
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    {M K : DerivedCategory A} {M' : CochainComplex A ℤ}
    {e : DerivedCategory.Q.obj M' ≅ M}
    (S : CanonicalExtSpectralSequence M K M' e)
    (hM : (DerivedCategory.TStructure.t (C := A)).minus M)
    (hK : (DerivedCategory.TStructure.t (C := A)).plus K) :
    (∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
      IsZero (AddCommGrpCat.of (DerivedCategory.Ext
        (DerivedCategory.Q.obj ((FilteredObject.quot (op p)).obj S.filtered)) K n))) ∧
    (∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p₁ ≤ p →
      IsIso (extFromFilteredQuotient K S.filtered p n)) := by
  constructor
  · intro n
    obtain ⟨m, hm⟩ := (DerivedCategory.minus_iff M).1 hM
    have : M.IsLE m := (DerivedCategory.isLE_iff M m).2 fun i hi => hm i (by omega)
    have hM' : M'.IsLE m := (DerivedCategory.isLE_Q_obj_iff M' m).1
      (DerivedCategory.TStructure.t.isLE_of_iso e.symm m)
    refine ⟨-m, fun p hp => ?_⟩
    let f := S.filtered.filtration.ι.app (op p)
    let Tsc := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hTsc : Tsc.ShortExact := ShortComplex.shortExact_mk_cokernel_π f
    let T := DerivedCategory.triangleOfSES hTsc
    have hT : T ∈ distTriang (DerivedCategory A) :=
      DerivedCategory.triangleOfSES_distinguished hTsc
    have htrunc : IsIso (DerivedCategory.Q.map (M'.ιTruncLE (-p))) := by
      have : M'.IsLE m := hM'
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso, M'.quasiIso_ιTruncLE_iff, M'.isLE_iff]
      exact fun i hi => (M'.isLE_iff m).1 hM' i (by omega)
    have hrel : DerivedCategory.Q.map (S.stepIso p).hom ≫
        DerivedCategory.Q.map (M'.ιTruncLE (-p)) =
        DerivedCategory.Q.map f ≫ DerivedCategory.Q.map S.underlyingIso.hom := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg DerivedCategory.Q.map (S.stepIso_hom_comp p)
    have : IsIso (DerivedCategory.Q.map f ≫ DerivedCategory.Q.map S.underlyingIso.hom) := by
      rw [← hrel]
      infer_instance
    have hfil : IsIso (DerivedCategory.Q.map f) :=
      IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map S.underlyingIso.hom)
    have hzero : IsZero T.obj₃ := (Triangle.isZero₃_iff_isIso₁ T hT).2 hfil
    exact ext_isZero_of_isZero_source n hzero
  · intro n
    obtain ⟨b, hb⟩ := (DerivedCategory.plus_iff K).1 hK
    have : K.IsGE (b + 1) := (DerivedCategory.isGE_iff K (b + 1)).2 fun i hi => hb i (by omega)
    refine ⟨n - b + 1, fun p hp => ?_⟩
    exact isIso_extFromFilteredQuotient_of_isLE K S.filtered p n (-p) (b + 1)
      (DerivedCategory.TStructure.t.isLE_of_iso
        (DerivedCategory.Q.mapIso (S.stepIso p)).symm (-p)) inferInstance (by omega)

/- The accepted filtration definition precedes its private comparison API. -/
/-- The filtration on `Extⁿ(M, K)` obtained from the canonical truncation filtration of a
complex representing `M`. -/
public noncomputable def canonicalExtFiltration
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    {M K : DerivedCategory A} {M' : CochainComplex A ℤ}
    {e : DerivedCategory.Q.obj M' ≅ M}
    (S : CanonicalExtSpectralSequence M K M' e)
    (n p : ℤ) : Subobject (AddCommGrpCat.of (DerivedCategory.Ext M K n)) :=
  imageSubobject <| AddCommGrpCat.ofHom
    { toFun := fun f ↦
        e.inv ≫ DerivedCategory.Q.map S.underlyingIso.inv ≫
          DerivedCategory.Q.map (cokernel.π (S.filtered.filtration.ι.app (op p))) ≫ f
      map_zero' := by simp
      map_add' := by simp }

/-- Precomposition with an isomorphism is an isomorphism of Ext groups: the contravariant case of
`Stacks.Injectives.homCongrAddEquiv`. -/
private noncomputable def extGroupIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {X Y : DerivedCategory A} (e : X ≅ Y) (K : DerivedCategory A) (n : ℤ) :
    AddCommGrpCat.of (DerivedCategory.Ext X K n) ≅
      AddCommGrpCat.of (DerivedCategory.Ext Y K n) :=
  (homCongrAddEquiv e (Iso.refl (K⟦n⟧))).toAddCommGrpIso

private theorem canonicalExtFiltration_eq_map
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    {M K : DerivedCategory A} {M' : CochainComplex A ℤ}
    {e : DerivedCategory.Q.obj M' ≅ M}
    (S : CanonicalExtSpectralSequence M K M' e)
    (n p : ℤ) :
    canonicalExtFiltration S n p =
      (Subobject.map (extGroupIso
        (DerivedCategory.Q.mapIso S.underlyingIso ≪≫ e) K n).hom).obj
          (extQuotientFiltration K S.filtered n p) := by
  unfold canonicalExtFiltration extQuotientFiltration
  rw [Subobject.map_imageSubobject]
  congr 1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  simp [extGroupIso, extFromFilteredQuotient, FilteredObject.quotπ,
    homCongrAddEquiv_apply, Iso.trans_inv]

/-- **Stacks 0G20, boundedness before renumbering.** For `M ∈ D⁻(A)` and
`K ∈ D⁺(A)`, the canonical Ext spectral sequence is bounded. -/
@[stacks 0G20 "canonical_convergence"]
public theorem canonicalExtSpectralSequence_isBounded
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    {M K : DerivedCategory A} {M' : CochainComplex A ℤ}
    {e : DerivedCategory.Q.obj M' ≅ M}
    (S : CanonicalExtSpectralSequence M K M' e)
    (hM : (DerivedCategory.TStructure.t (C := A)).minus M)
    (hK : (DerivedCategory.TStructure.t (C := A)).plus K) :
    IsBounded S.spectralSequence := by
  obtain ⟨m, hm⟩ := (DerivedCategory.minus_iff M).1 hM
  obtain ⟨b, hb⟩ := (DerivedCategory.plus_iff K).1 hK
  have hKge : K.IsGE (b + 1) :=
    (DerivedCategory.isGE_iff K (b + 1)).2 (fun i hi => hb i (by omega))
  intro n
  refine (Set.finite_Icc (b - n) (m - 1)).subset ?_
  intro p hp
  have hpLower : b - n ≤ p := by
    by_contra h
    exact hp (IsZero.of_iso
      (ext_isZero_of_homology_lt _ K (b + 1) (2 * p + (n - p)) hKge (by omega))
      (S.e₁Iso p (n - p)))
  have hpUpper : p ≤ m - 1 := by
    by_contra h
    exact hp (IsZero.of_iso (ext_isZero_of_isZero_source (2 * p + (n - p))
      ((DerivedCategory.singleFunctor A 0).map_isZero (hm p (by omega))))
      (S.e₁Iso p (n - p)))
  exact ⟨hpLower, hpUpper⟩

/-- **Stacks 0G20, convergence before renumbering.** For `M ∈ D⁻(A)` and
`K ∈ D⁺(A)`, the canonical Ext spectral sequence converges to `Ext^(p+q)(M, K)`, with
filtration index `-p`. -/
@[stacks 0G20 "canonical_convergence"]
public theorem canonicalExtSpectralSequence_convergesToExt
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    {M K : DerivedCategory A} {M' : CochainComplex A ℤ}
    {e : DerivedCategory.Q.obj M' ≅ M}
    (S : CanonicalExtSpectralSequence M K M' e)
    (hM : (DerivedCategory.TStructure.t (C := A)).minus M)
    (hK : (DerivedCategory.TStructure.t (C := A)).plus K) :
    let E := S.spectralSequence
    ∃ hF : ∀ n : ℤ, Monotone (canonicalExtFiltration S n),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ canonicalExtFiltration S n a = ⊥ ∧
        canonicalExtFiltration S n b = ⊤) ∧
      (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
      ∀ p q : ℤ, Nonempty
      (E.pageInfinity (p, q) ≅
          cokernel (Subobject.ofLE (canonicalExtFiltration S (p + q) (-p))
            (canonicalExtFiltration S (p + q) (-p + 1)) (hF (p + q) (by omega)))) := by
  obtain ⟨hzero, hiso⟩ := canonicalExtQuotientBounds S hM hK
  obtain ⟨hF', hfinite, hInf, hgraded⟩ := extSpectralSequence_convergesToExt K S.filtered hzero hiso
  let e' : DerivedCategory.Q.obj S.filtered.X ≅ M := DerivedCategory.Q.mapIso S.underlyingIso ≪≫ e
  let φ (n : ℤ) := Subobject.mapIsoToOrderIso (extGroupIso e' K n)
  have hF : ∀ n : ℤ, Monotone (canonicalExtFiltration S n) := by
    intro n p q hpq
    rw [canonicalExtFiltration_eq_map, canonicalExtFiltration_eq_map]
    show φ n (extQuotientFiltration K S.filtered n p) ≤
      φ n (extQuotientFiltration K S.filtered n q)
    exact (φ n).map_rel_iff'.2 (hF' n hpq)
  refine ⟨hF, fun n => ?_, hInf, fun p q => ?_⟩
  · obtain ⟨a, b, hab, ha, hb⟩ := hfinite n
    refine ⟨a, b, hab, ?_, ?_⟩
    · rw [canonicalExtFiltration_eq_map, ha]
      exact (φ n).map_bot
    · rw [canonicalExtFiltration_eq_map, hb]
      exact (φ n).map_top
  · obtain ⟨i⟩ := hgraded p q
    let n := p + q
    let P := extQuotientFiltration K S.filtered n (-p)
    let Q := extQuotientFiltration K S.filtered n (-p + 1)
    have hPQ : P ≤ Q := hF' n (by omega)
    have hP : (φ n) P = canonicalExtFiltration S n (-p) := by
      simpa [P, φ, e'] using (canonicalExtFiltration_eq_map S n (-p)).symm
    have hQ : (φ n) Q = canonicalExtFiltration S n (-p + 1) := by
      simpa [Q, φ, e'] using (canonicalExtFiltration_eq_map S n (-p + 1)).symm
    exact ⟨i ≪≫ subobjectQuotientMapIso (extGroupIso e' K n) P Q hPQ ≪≫
      Subobject.cokernelOfLEIsoOfEq ((φ n).map_rel_iff'.2 hPQ) (hF n (by omega)) hP hQ⟩

/-- **Stacks 0G20, boundedness after renumbering.** For `M ∈ D⁻(A)` and
`K ∈ D⁺(A)`, the renumbered canonical Ext spectral sequence is bounded. -/
@[stacks 0G20 "canonical_convergence"]
public theorem renumberedCanonicalExtSpectralSequence_isBounded
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    {M K : DerivedCategory A} {M' : CochainComplex A ℤ}
    {e : DerivedCategory.Q.obj M' ≅ M}
    (S : CanonicalExtSpectralSequence M K M' e)
    (hM : (DerivedCategory.TStructure.t (C := A)).minus M)
    (hK : (DerivedCategory.TStructure.t (C := A)).plus K) :
    IsBounded
      (renumberedCanonicalExtSpectralSequence S) :=
  truncationRenumber_finite_not_isZero_page_two _
    (canonicalExtSpectralSequence_isBounded S hM hK)

/-- **Stacks 0G20, convergence after renumbering.** For `M ∈ D⁻(A)` and
`K ∈ D⁺(A)`, the renumbered canonical Ext spectral sequence converges to
`Ext^(i+j)(M, K)`, with filtration index `j`. -/
@[stacks 0G20 "canonical_convergence"]
public theorem renumberedCanonicalExtSpectralSequence_convergesToExt
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    {M K : DerivedCategory A} {M' : CochainComplex A ℤ}
    {e : DerivedCategory.Q.obj M' ≅ M}
    (S : CanonicalExtSpectralSequence M K M' e)
    (hM : (DerivedCategory.TStructure.t (C := A)).minus M)
    (hK : (DerivedCategory.TStructure.t (C := A)).plus K) :
    let E := renumberedCanonicalExtSpectralSequence S
    ∃ hF : ∀ n : ℤ, Monotone (canonicalExtFiltration S n),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ canonicalExtFiltration S n a = ⊥ ∧
        canonicalExtFiltration S n b = ⊤) ∧
      (∀ i j : ℤ, E.HasPageInfinityAt (i, j)) ∧
      ∀ i j : ℤ, Nonempty
        (E.pageInfinity (i, j) ≅
          cokernel (Subobject.ofLE (canonicalExtFiltration S (i + j) j)
            (canonicalExtFiltration S (i + j) (j + 1)) (hF (i + j) (by omega)))) := by
  let Eold := S.spectralSequence
  obtain ⟨hF, hfinite, hpages, hgraded⟩ := canonicalExtSpectralSequence_convergesToExt S hM hK
  refine ⟨hF, hfinite, fun i j => ?_, fun i j => ?_⟩
  · have : Eold.HasPageInfinityAt (-j, i + 2 * j) := hpages (-j) (i + 2 * j)
    exact truncationRenumber_hasPageInfinityAt Eold i j
  · have : Eold.HasPageInfinityAt (-j, i + 2 * j) := hpages (-j) (i + 2 * j)
    obtain ⟨hiso⟩ := hgraded (-j) (i + 2 * j)
    rw [show -j + (i + 2 * j) = i + j by omega] at hiso
    have hP : canonicalExtFiltration S (i + j) (-(-j)) =
        canonicalExtFiltration S (i + j) j := by rw [neg_neg]
    have hQ : canonicalExtFiltration S (i + j) (-(-j) + 1) =
        canonicalExtFiltration S (i + j) (j + 1) := by rw [neg_neg]
    exact ⟨truncationRenumber_pageInfinityIso Eold i j ≪≫ hiso ≪≫
      Subobject.cokernelOfLEIsoOfEq (hF (i + j) (by omega)) (hF (i + j) (by omega)) hP hQ⟩

/-! ### The canonical Ext spectral sequence of a representative -/

/-- **Stacks 0G20, boundedness of the canonical Ext spectral sequence.** For `M ∈ D⁻(A)` and
`K ∈ D⁺(A)`, the Ext spectral sequence of the canonical truncation filtration
`F^p M^• = τ_{≤ -p} M^•` of a complex `M^•` representing `M` is bounded.  This is
`canonicalExtSpectralSequence_isBounded` at the filtration itself. -/
@[stacks 0G20 "canonical_convergence"]
public theorem isBounded_canonicalExtSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    (M K : DerivedCategory A) (M' : CochainComplex A ℤ)
    (e : DerivedCategory.Q.obj M' ≅ M)
    (hM : (DerivedCategory.TStructure.t (C := A)).minus M)
    (hK : (DerivedCategory.TStructure.t (C := A)).plus K) :
    IsBounded (canonicalExtSpectralSequence M K M' e).spectralSequence :=
  canonicalExtSpectralSequence_isBounded _ hM hK

/-- **Stacks 0G20, convergence of the canonical Ext spectral sequence.** For `M ∈ D⁻(A)` and
`K ∈ D⁺(A)`, the Ext spectral sequence of the canonical truncation filtration
`F^p M^• = τ_{≤ -p} M^•` of a complex `M^•` representing `M` converges to `Ext^{p+q}(M, K)`,
with filtration index `-p`.  This is `canonicalExtSpectralSequence_convergesToExt` at the
filtration itself. -/
@[stacks 0G20 "canonical_convergence"]
public theorem convergesToExt_canonicalExtSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    (M K : DerivedCategory A) (M' : CochainComplex A ℤ)
    (e : DerivedCategory.Q.obj M' ≅ M)
    (hM : (DerivedCategory.TStructure.t (C := A)).minus M)
    (hK : (DerivedCategory.TStructure.t (C := A)).plus K) :
    let S := canonicalExtSpectralSequence M K M' e
    let E := S.spectralSequence
    ∃ hF : ∀ n : ℤ, Monotone (canonicalExtFiltration S n),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ canonicalExtFiltration S n a = ⊥ ∧
        canonicalExtFiltration S n b = ⊤) ∧
      (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
      ∀ p q : ℤ, Nonempty
      (E.pageInfinity (p, q) ≅
          cokernel (Subobject.ofLE (canonicalExtFiltration S (p + q) (-p))
            (canonicalExtFiltration S (p + q) (-p + 1)) (hF (p + q) (by omega)))) :=
  canonicalExtSpectralSequence_convergesToExt _ hM hK

/-! ### The brutal truncation filtration -/

/-- The quotient of a complex by the `p`-th step of its brutal truncation filtration lives in
degrees `< p`: in every degree `≥ p` the inclusion `σ_{≥ p}M^• ⟶ M^•` is an isomorphism, so the
cokernel vanishes there. -/
private lemma isStrictlyLE_stupidFiltrationQuot
    {A : Type u} [Category.{v} A] [Abelian A]
    (M' : CochainComplex A ℤ) (p k : ℤ) (hk : k + 1 = p) :
    ((FilteredObject.quot (op p)).obj
      (CochainComplex.stupidTruncationFiltration M')).IsStrictlyLE k := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have hIso : IsIso (((CochainComplex.stupidTruncationFiltration M').filtration.ι.app
      (op p)).f i) := by
    rw [CochainComplex.stupidTruncationFiltration_filtration_ι_app,
      StacksDraft.StupidTruncation.ιStupidTruncGE_f M' p i (by omega)]
    exact (StacksDraft.StupidTruncation.stupidTruncGEXIso M' p i (by omega)).isIso_hom
  exact IsZero.of_iso
    (isZero_cokernel_of_epi
      (((CochainComplex.stupidTruncationFiltration M').filtration.ι.app (op p)).f i))
    (PreservesCokernel.iso (HomologicalComplex.eval A (ComplexShape.up ℤ) i)
      ((CochainComplex.stupidTruncationFiltration M').filtration.ι.app (op p)))

/-- Ext from a coconnective object into a connective one vanishes: if `X` lives in degrees `≤ a`
and `K⟦n⟧` in degrees `≥ c` with `a < c`, then `Ext^n(X, K) = 0`. -/
private lemma ext_isZero_of_isLE_of_isGE
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X K : DerivedCategory A) (a c n : ℤ) (hX : X.IsLE a) (hK : (K⟦n⟧).IsGE c)
    (hac : a < c) :
    IsZero (AddCommGrpCat.of (DerivedCategory.Ext X K n)) := by
  let : X.IsLE a := hX
  let : (K⟦n⟧).IsGE c := hK
  let : Subsingleton (DerivedCategory.Ext X K n) := ⟨fun f g => by
    rw [DerivedCategory.TStructure.t.zero f a c hac,
      DerivedCategory.TStructure.t.zero g a c hac]⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- For `K ∈ D⁺(A)` the Ext groups out of the quotients of `M^•` by its brutal truncations
vanish in each degree once the truncation degree is small enough: the quotient lives in degrees
`< p`, while `K⟦n⟧` is connective. -/
private lemma stupidExtQuotient_isZero
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    (K : DerivedCategory A) (M' : CochainComplex A ℤ)
    (hK : (DerivedCategory.TStructure.t (C := A)).plus K) (n : ℤ) :
    ∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
      IsZero (AddCommGrpCat.of (DerivedCategory.Ext
        (DerivedCategory.Q.obj ((FilteredObject.quot (op p)).obj
          (CochainComplex.stupidTruncationFiltration M'))) K n)) := by
  obtain ⟨b, hb⟩ := (DerivedCategory.plus_iff K).1 hK
  have : K.IsGE (b + 1) :=
    (DerivedCategory.isGE_iff K (b + 1)).2 (fun i hi => hb i (by omega))
  refine ⟨b - n, fun p hp => ?_⟩
  let Qt := (FilteredObject.quot (op p)).obj (CochainComplex.stupidTruncationFiltration M')
  let : Qt.IsStrictlyLE (p - 1) :=
    isStrictlyLE_stupidFiltrationQuot M' p (p - 1) (by omega)
  have hLE : (DerivedCategory.Q.obj Qt).IsLE (p - 1) :=
    (DerivedCategory.isLE_Q_obj_iff Qt (p - 1)).2 inferInstance
  have hKshift : (K⟦n⟧).IsGE (b + 1 - n) :=
    DerivedCategory.TStructure.t.isGE_shift K (b + 1) n (b + 1 - n) (by omega)
  exact ext_isZero_of_isLE_of_isGE _ K (p - 1) (b + 1 - n) n hLE hKshift (by omega)

/-- For `M^•` bounded above the quotient maps `Ext^n(M^•/σ_{≥ p}M^•, K) ⟶ Ext^n(M^•, K)` are
isomorphisms once the truncation degree is above the bound: the step `σ_{≥ p}M^•` then vanishes
in every degree, so the two outer Ext groups of the defining triangle vanish. -/
private lemma stupidExtQuotient_isIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    (K : DerivedCategory A) (M' : CochainComplex A ℤ)
    (hK : (DerivedCategory.TStructure.t (C := A)).plus K)
    (hM : CochainComplex.minus A M') (n : ℤ) :
    ∃ p₁ : ℤ, ∀ p : ℤ, p₁ ≤ p →
      IsIso (extFromFilteredQuotient K
        (CochainComplex.stupidTruncationFiltration M') p n) := by
  obtain ⟨b, hb⟩ := (DerivedCategory.plus_iff K).1 hK
  obtain ⟨m, hm⟩ := (CochainComplex.minus_iff M').1 hM
  let : M'.IsStrictlyLE m := hm
  have : K.IsGE (b + 1) :=
    (DerivedCategory.isGE_iff K (b + 1)).2 (fun i hi => hb i (by omega))
  refine ⟨m + 1, fun p hp => ?_⟩
  let F := CochainComplex.stupidTruncationFiltration M'
  have hstep : ∀ k : ℤ, (F.filtration.obj (op p)).IsStrictlyLE k := by
    intro k
    rw [CochainComplex.isStrictlyLE_iff]
    intro i _
    by_cases hip : p ≤ i
    · exact IsZero.of_iso (M'.isZero_of_isStrictlyLE m i (by omega))
        (StacksDraft.StupidTruncation.stupidTruncGEXIso M' p i hip)
    · exact M'.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE p) i
        (by rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]; omega)
  let : (F.filtration.obj (op p)).IsStrictlyLE (b - n) := hstep (b - n)
  exact isIso_extFromFilteredQuotient_of_isLE K F p n (b - n) (b + 1)
    ((DerivedCategory.isLE_Q_obj_iff (F.filtration.obj (op p)) (b - n)).2 inferInstance)
    inferInstance (by omega)

/-- **Stacks 0G20, boundedness of the brutal-truncation Ext spectral sequence.** If
`K ∈ D⁺(A)` and the cochain complex `M^•` is bounded above, the Ext spectral sequence of the
filtration `F^p M^• = σ_{≥ p} M^•` is bounded. -/
@[stacks 0G20 "stupid_convergence"]
public theorem stupidExtSpectralSequence_isBounded
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    (K : DerivedCategory A) (M' : CochainComplex A ℤ)
    (hK : (DerivedCategory.TStructure.t (C := A)).plus K)
    (hM : CochainComplex.minus A M') :
    IsBounded (stupidExtSpectralSequence K M') :=
  extSpectralSequence_isBounded K (CochainComplex.stupidTruncationFiltration M')
    (stupidExtQuotient_isZero K M' hK) (stupidExtQuotient_isIso K M' hK hM)

/-- **Stacks 0G20, convergence of the brutal-truncation Ext spectral sequence.** If
`K ∈ D⁺(A)` and the cochain complex `M^•` is bounded above, the Ext spectral sequence of the
filtration `F^p M^• = σ_{≥ p} M^•` converges to `Ext^{p+q}(M^•, K)`, the Ext groups of the
object `M` of the derived category represented by `M^•`, with filtration index `-p`. -/
@[stacks 0G20 "stupid_convergence"]
public theorem stupidExtSpectralSequence_convergesToExt
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    (K : DerivedCategory A) (M' : CochainComplex A ℤ)
    (hK : (DerivedCategory.TStructure.t (C := A)).plus K)
    (hM : CochainComplex.minus A M') :
    let E := stupidExtSpectralSequence K M'
    ∃ hF : ∀ n : ℤ, Monotone
        (extQuotientFiltration K (CochainComplex.stupidTruncationFiltration M') n),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧
        extQuotientFiltration K (CochainComplex.stupidTruncationFiltration M') n a = ⊥ ∧
        extQuotientFiltration K (CochainComplex.stupidTruncationFiltration M') n b = ⊤) ∧
      (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
      ∀ p q : ℤ, Nonempty
        (E.pageInfinity (p, q) ≅
          cokernel (Subobject.ofLE
            (extQuotientFiltration K
              (CochainComplex.stupidTruncationFiltration M') (p + q) (-p))
            (extQuotientFiltration K
              (CochainComplex.stupidTruncationFiltration M') (p + q) (-p + 1))
            (hF (p + q) (by omega)))) :=
  extSpectralSequence_convergesToExt K (CochainComplex.stupidTruncationFiltration M')
    (stupidExtQuotient_isZero K M' hK) (stupidExtQuotient_isIso K M' hK hM)

end Stacks.Injectives
