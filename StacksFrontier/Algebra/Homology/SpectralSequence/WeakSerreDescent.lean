module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToMap
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToWeakSerre

/-!
# Descending a spectral sequence along a fully faithful exact functor

Let `ι : 𝒜 ⥤ 𝒞` be a fully faithful exact functor between abelian categories whose essential
image is a weak Serre subcategory of `𝒞` ([Stacks, Tag 02MO], in the form of [Stacks, Tag 0754]).
A spectral sequence `E` of `𝒞` whose page `r₀` lies in the essential image of `ι` is the image of
a spectral sequence `E'` of `𝒜`: every later page is a subquotient of page `r₀`, hence lies in the
essential image too, and the pages, differentials and identifications of the homology of a page
with the next page are pulled back along `ι`. If moreover `E` abuts to a graded object `H`, then
`H` lies in the essential image — its filtration is finite with graded pieces in it — and `E'`
abuts to the preimage of `H`.

Composing with the transport along an exact functor
(`CategoryTheory.SpectralSequence.map`, `CategoryTheory.SpectralSequence.AbutsTo.map`) gives the
form used to apply a functor which is only exact on a weak Serre subcategory: a spectral sequence
of `𝒞` whose page `r₀` lies in a weak Serre subcategory `P` can be pushed along any exact functor
`G : P ⥤ 𝒟`, together with its abutment.

## Main definitions

* `CategoryTheory.SpectralSequence.descend`: the spectral sequence of `𝒜` whose image under `ι`
  is `E`.
* `CategoryTheory.SpectralSequence.descendPageXIso`: the identification of `ι` of a page of the
  descent with the page of `E`.

## Main results

* `CategoryTheory.SpectralSequence.essImage_page_X`: every page of `E` lies in the essential
  image once page `r₀` does.
* `CategoryTheory.SpectralSequence.essImage_of_abutsTo`: the abutment of `E` lies in the
  essential image.
* `CategoryTheory.SpectralSequence.exists_descend_abutsTo`: **descent of a spectral sequence and
  of its abutment along a fully faithful exact functor with weak Serre essential image.**
* `CategoryTheory.SpectralSequence.exists_map_abutsTo_of_isWeakSerreClass`: **a spectral
  sequence whose page `r₀` lies in a weak Serre subcategory `P`, with its abutment, can be pushed
  along an exact functor defined on `P` only.**
* `CategoryTheory.SpectralSequence.exists_map_abutsTo_of_isWeakSerreClass'`: the same for a
  functor `F : 𝒞 ⥤ 𝒟` whose restriction to `P` is exact.

## Implementation notes

The membership of the later pages, of the infinity page and of the abutment in a weak Serre
class is `CategoryTheory.SpectralSequence.prop_page_of_le`,
`CategoryTheory.SpectralSequence.prop_pageInfinity_of_prop_page` and
`CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page`, applied to the essential image. What
is added is that every term of the filtration witnessing the abutment lies in it as well, which is
what pulling the filtration back along `ι` needs.

The exactness of `ι` is asked for as `ι.Additive` and `ι.PreservesHomology`, the hypotheses of
`CategoryTheory.SpectralSequence.map`; for the push forward along `G`, `G.PreservesMonomorphisms`
is added, as `CategoryTheory.SpectralSequence.AbutsTo.map` asks.

## References

* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/

@[expose] public noncomputable section

universe v u v' u' v'' u''

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence


variable {A : Type u} [Category.{v} A] [Abelian A] {C : Type u'} [Category.{v'} C] [Abelian C]
  (ι : A ⥤ C) [ι.Full] [ι.Faithful] [ι.Additive] [ι.PreservesHomology]
  [ι.essImage.IsWeakSerreClass]

variable {r₀ : ℤ}

section Descend

variable {κ : Type*} {c : ℤ → ComplexShape κ} (E : SpectralSequence C c r₀)
  (hE : ∀ pq, ι.essImage ((E.page r₀ le_rfl).X pq))

omit [Abelian A] [ι.Full] [ι.Faithful] [ι.Additive] [ι.PreservesHomology] in
include hE in
/-- Every page of a spectral sequence lies in the essential image once its first page does:
`CategoryTheory.SpectralSequence.prop_page_of_le`. -/
theorem essImage_page_X (r : ℤ) (hr : r₀ ≤ r) (pq : κ) : ι.essImage ((E.page r hr).X pq) :=
  prop_page_of_le E ι.essImage le_rfl hE r hr hr pq

/-- The object of `𝒜` underlying a term of a page of the descent. -/
def descendX (r : ℤ) (hr : r₀ ≤ r) (pq : κ) : A :=
  (essImage_page_X ι E hE r hr pq).witness

/-- `ι` of a term of a page of the descent is the corresponding term of `E`. -/
def descendXIso (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    ι.obj (descendX ι E hE r hr pq) ≅ (E.page r hr).X pq :=
  (essImage_page_X ι E hE r hr pq).getIso

/-- The page `r` of the descent: the terms are the preimages of the terms of `E` and the
differentials the preimages of its differentials. -/
def descendPage (r : ℤ) (hr : r₀ ≤ r) : HomologicalComplex A (c r) where
  X pq := descendX ι E hE r hr pq
  d pq pq' := ι.preimage ((descendXIso ι E hE r hr pq).hom ≫ (E.page r hr).d pq pq' ≫
    (descendXIso ι E hE r hr pq').inv)
  shape pq pq' h := ι.map_injective (by simp [(E.page r hr).shape _ _ h])
  d_comp_d' pq pq' pq'' _ _ := ι.map_injective (by simp)

/-- `ι` of a page of the descent is the corresponding page of `E`. -/
def descendPageIso (r : ℤ) (hr : r₀ ≤ r) :
    (ι.mapHomologicalComplex (c r)).obj (descendPage ι E hE r hr) ≅ E.page r hr :=
  HomologicalComplex.Hom.isoOfComponents (fun pq => descendXIso ι E hE r hr pq)
    (fun pq pq' _ => by simp [descendPage])

/-- **The descent of a spectral sequence along a fully faithful exact functor with weak Serre
essential image**, when page `r₀` lies in the essential image. -/
def descend : SpectralSequence A c r₀ where
  page r hr := descendPage ι E hE r hr
  iso r r' pq hrr' hr := ι.preimageIso
    ((((descendPage ι E hE r hr).sc pq).mapHomologyIso ι).symm ≪≫
      ShortComplex.homologyMapIso
        ((HomologicalComplex.shortComplexFunctor C (c r) pq).mapIso
          (descendPageIso ι E hE r hr)) ≪≫
      E.iso r r' pq hrr' hr ≪≫ (descendXIso ι E hE r' (hrr' ▸ Int.le_add_one hr) pq).symm)

/-- `ι` of a term of a page of the descent is the corresponding term of `E`. -/
def descendPageXIso (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    ι.obj (((descend ι E hE).page r hr).X pq) ≅ (E.page r hr).X pq :=
  descendXIso ι E hE r hr pq

/-- `ι` of a differential of a page of the descent is the corresponding differential of `E`,
conjugated by `CategoryTheory.SpectralSequence.descendPageXIso`. -/
lemma map_descend_page_d (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) :
    ι.map (((descend ι E hE).page r hr).d pq pq') =
      (descendPageXIso ι E hE r hr pq).hom ≫ (E.page r hr).d pq pq' ≫
        (descendPageXIso ι E hE r hr pq').inv := by
  simp [descend, descendPage, descendPageXIso]

/-- A differential of a page of the descent vanishes if and only if the corresponding differential
of `E` does. -/
lemma descend_page_d_eq_zero_iff (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) :
    ((descend ι E hE).page r hr).d pq pq' = 0 ↔ (E.page r hr).d pq pq' = 0 := by
  rw [← ι.map_eq_zero_iff, map_descend_page_d]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  simpa using (descendPageXIso ι E hE r hr pq).inv ≫= h =≫ (descendPageXIso ι E hE r hr pq').hom

/-- The descent has an infinity page wherever `E` has one. -/
theorem hasPageInfinityAt_descend (pq : κ) [E.HasPageInfinityAt pq] :
    (descend ι E hE).HasPageInfinityAt pq := by
  constructor
  · obtain ⟨r, hr⟩ := E.nonempty_hasEdgeMonoSet pq
    refine ⟨r, hr.1, fun r' hrr' => ?_⟩
    have := hr.2 r' hrr'
    exact ⟨E.le₀_of_hasEdgeMonoAt pq r', fun pq' =>
      (descend_page_d_eq_zero_iff ι E hE r' _ pq' pq).2
        (E.d_eq_zero_of_hasEdgeMonoAt pq' pq r')⟩
  · obtain ⟨r, hr⟩ := E.nonempty_hasEdgeEpiSet pq
    refine ⟨r, hr.1, fun r' hrr' => ?_⟩
    have := hr.2 r' hrr'
    exact ⟨E.le₀_of_hasEdgeEpiAt pq r', fun pq' =>
      (descend_page_d_eq_zero_iff ι E hE r' _ pq pq').2
        (E.d_eq_zero_of_hasEdgeEpiAt pq pq' r')⟩

/-- `ι` of the infinity page of the descent is the infinity page of `E`. -/
def descendPageInfinityIso (pq : κ) [E.HasPageInfinityAt pq] :
    haveI := hasPageInfinityAt_descend ι E hE pq
    ι.obj ((descend ι E hE).pageInfinity pq) ≅ E.pageInfinity pq := by
  haveI := hasPageInfinityAt_descend ι E hE pq
  let r := max (E.rMin pq) ((descend ι E hE).rMin pq)
  have : E.HasEdgeMonoAtFrom pq r :=
    E.hasEdgeMonoAtFrom_of_GE pq (E.rMin pq) r (le_max_left _ _)
  have : E.HasEdgeEpiAtFrom pq r :=
    E.hasEdgeEpiAtFrom_of_GE pq (E.rMin pq) r (le_max_left _ _)
  have : (descend ι E hE).HasEdgeMonoAtFrom pq r :=
    (descend ι E hE).hasEdgeMonoAtFrom_of_GE pq ((descend ι E hE).rMin pq) r (le_max_right _ _)
  have : (descend ι E hE).HasEdgeEpiAtFrom pq r :=
    (descend ι E hE).hasEdgeEpiAtFrom_of_GE pq ((descend ι E hE).rMin pq) r (le_max_right _ _)
  exact ι.mapIso ((descend ι E hE).pageInfinityIso pq r) ≪≫
    descendPageXIso ι E hE r _ pq ≪≫ (E.pageInfinityIso pq r).symm

end Descend

section AbutsTo

variable {E : CohomologicalSpectralSequence C r₀}
  (hE : ∀ pq, ι.essImage ((E.page r₀ le_rfl).X pq))
  {H : ℤ → C}

omit [Abelian A] [ι.Full] [ι.Faithful] [ι.Additive] [ι.PreservesHomology] in
include hE in
/-- The infinity page lies in the essential image once the first page does:
`CategoryTheory.SpectralSequence.prop_pageInfinity_of_prop_page`. -/
theorem essImage_pageInfinity (pq : ℤ × ℤ) [E.HasPageInfinityAt pq] :
    ι.essImage (E.pageInfinity pq) :=
  prop_pageInfinity_of_prop_page E ι.essImage le_rfl hE pq

omit [Abelian A] [ι.Full] [ι.Faithful] [ι.Additive] [ι.PreservesHomology] in
include hE in
/-- **The terms of a finite filtration whose graded pieces are the terms of the infinity page lie
in the weak Serre subcategory**, by descending induction from the bottom, the filtration being
finite and each step an extension. -/
theorem essImage_filtration (hinf : ∀ p q : ℤ, E.HasPageInfinityAt (p, q))
    (F : ∀ n : ℤ, ℤ → Subobject (H n)) (hF : ∀ n : ℤ, Antitone (F n))
    (hbounds : ∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥)
    (hgr : ∀ p q : ℤ, Nonempty (E.pageInfinity (p, q) ≅
      cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
        (hF (p + q) (Int.le_add_one le_rfl)))))
    (n p : ℤ) : ι.essImage (F n p : C) := by
  have hcok : ∀ (n p : ℤ), ι.essImage
      (cokernel (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega)))) := by
    intro n p
    obtain ⟨m, rfl⟩ : ∃ m, n = p + m := ⟨n - p, by omega⟩
    have := hinf p m
    exact ι.essImage.prop_of_iso (hgr p m).some (essImage_pageInfinity ι hE (p, m))
  have hstep : ∀ p : ℤ, ι.essImage (F n (p + 1) : C) → ι.essImage (F n p : C) := fun p h =>
    ι.essImage.prop_X₂_of_shortExact
      (S := ShortComplex.mk (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega)))
        (cokernel.π _) (cokernel.condition _))
      { exact := ShortComplex.exact_cokernel _ } h (hcok n p)
  obtain ⟨a, b, -, -, hb⟩ := hbounds n
  have hge : ∀ p, b ≤ p → ι.essImage (F n p : C) := fun p hp => by
    rw [show F n p = ⊥ from le_bot_iff.1 (hb ▸ hF n hp)]
    exact ι.essImage.prop_of_isZero (Subobject.botCoeIsoZero.isZero_iff.2 (isZero_zero C))
  have hdown : ∀ k : ℕ, ι.essImage (F n (b - k) : C) := by
    intro k
    induction k with
    | zero => exact hge _ (by simp)
    | succ k ih =>
      refine hstep _ ?_
      rwa [show b - ((k + 1 : ℕ) : ℤ) + 1 = b - k by push_cast; ring]
  rcases le_or_gt b p with hp | hp
  · exact hge p hp
  · have := hdown (b - p).toNat
    rwa [show b - ((b - p).toNat : ℤ) = p by omega] at this

omit [Abelian A] [ι.Full] [ι.Faithful] [ι.Additive] [ι.PreservesHomology] in
include hE in
/-- The abutment lies in the essential image once the first page does:
`CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page`. -/
theorem essImage_of_abutsTo (habuts : AbutsTo E H) (n : ℤ) : ι.essImage (H n) :=
  habuts.prop_of_prop_page ι.essImage le_rfl hE n

/-- A subobject of `ι X` with underlying object in the essential image, pulled back to a
subobject of `X`. -/
def descendSubobject {X : A} {Y : C} (eX : ι.obj X ≅ Y) (T : Subobject Y)
    (hT : ι.essImage (T : C)) : Subobject X :=
  have : Mono (ι.preimage (hT.getIso.hom ≫ T.arrow ≫ eX.inv)) :=
    ι.mono_of_mono_map (by rw [Functor.map_preimage]; infer_instance)
  Subobject.mk (ι.preimage (hT.getIso.hom ≫ T.arrow ≫ eX.inv))

/-- `ι` of the pulled back subobject is the subobject. -/
def descendSubobjectIso {X : A} {Y : C} (eX : ι.obj X ≅ Y) (T : Subobject Y)
    (hT : ι.essImage (T : C)) : ι.obj (descendSubobject ι eX T hT : A) ≅ (T : C) :=
  have : Mono (ι.preimage (hT.getIso.hom ≫ T.arrow ≫ eX.inv)) :=
    ι.mono_of_mono_map (by rw [Functor.map_preimage]; infer_instance)
  ι.mapIso (Subobject.underlyingIso _) ≪≫ hT.getIso

omit [Abelian A] [Abelian C] [ι.Additive] [ι.PreservesHomology] [ι.essImage.IsWeakSerreClass] in
/-- The identification `CategoryTheory.SpectralSequence.descendSubobjectIso` commutes with the
inclusions into `ι X` and `Y`. -/
lemma descendSubobjectIso_hom_arrow {X : A} {Y : C} (eX : ι.obj X ≅ Y) (T : Subobject Y)
    (hT : ι.essImage (T : C)) :
    (descendSubobjectIso ι eX T hT).hom ≫ T.arrow =
      ι.map (descendSubobject ι eX T hT).arrow ≫ eX.hom := by
  have : Mono (ι.preimage (hT.getIso.hom ≫ T.arrow ≫ eX.inv)) :=
    ι.mono_of_mono_map (by rw [Functor.map_preimage]; infer_instance)
  simp only [descendSubobjectIso, descendSubobject, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [← Subobject.underlyingIso_hom_comp_eq_mk, Functor.map_comp, Functor.map_preimage]
  simp

omit [Abelian A] [Abelian C] [ι.Additive] [ι.PreservesHomology] [ι.essImage.IsWeakSerreClass] in
/-- Pulling back subobjects is monotone. -/
lemma descendSubobject_mono {X : A} {Y : C} (eX : ι.obj X ≅ Y) {T₁ T₂ : Subobject Y}
    (h : T₁ ≤ T₂) (hT₁ : ι.essImage (T₁ : C)) (hT₂ : ι.essImage (T₂ : C)) :
    descendSubobject ι eX T₁ hT₁ ≤ descendSubobject ι eX T₂ hT₂ := by
  refine Subobject.le_of_comm (ι.preimage ((descendSubobjectIso ι eX T₁ hT₁).hom ≫
    Subobject.ofLE _ _ h ≫ (descendSubobjectIso ι eX T₂ hT₂).inv)) (ι.map_injective ?_)
  rw [Functor.map_comp, Functor.map_preimage, ← cancel_mono eX.hom]
  simp only [Category.assoc, ← descendSubobjectIso_hom_arrow, Iso.inv_hom_id_assoc,
    Subobject.ofLE_arrow]

/-- `ι` of the cokernel of an inclusion of pulled back subobjects is the cokernel of the
inclusion of the subobjects. -/
def descendCokernelIso {X : A} {Y : C} (eX : ι.obj X ≅ Y) {T₁ T₂ : Subobject Y}
    (h : T₁ ≤ T₂) (hT₁ : ι.essImage (T₁ : C)) (hT₂ : ι.essImage (T₂ : C)) :
    ι.obj (cokernel (Subobject.ofLE _ _ (descendSubobject_mono ι eX h hT₁ hT₂))) ≅
      cokernel (Subobject.ofLE _ _ h) :=
  have := Functor.PreservesHomology.preservesCokernel ι
    (Subobject.ofLE _ _ (descendSubobject_mono ι eX h hT₁ hT₂))
  PreservesCokernel.iso ι _ ≪≫
    cokernel.mapIso _ _ (descendSubobjectIso ι eX T₁ hT₁) (descendSubobjectIso ι eX T₂ hT₂) (by
      rw [← cancel_mono T₂.arrow]
      simp only [Category.assoc, Subobject.ofLE_arrow, descendSubobjectIso_hom_arrow]
      rw [← Functor.map_comp_assoc, Subobject.ofLE_arrow])

include hE in
/-- **The descent of an abutting spectral sequence abuts to the preimage of the abutment.** If
`E` abuts to `H` and `ι (H' n) ≅ H n` for every `n`, the descent of `E` abuts to `H'`: the
filtration of `H n` is pulled back along `ι`, its terms lying in the essential image by
`CategoryTheory.SpectralSequence.essImage_filtration`. -/
theorem abutsTo_descend (habuts : AbutsTo E H) {H' : ℤ → A} (eH : ∀ n, ι.obj (H' n) ≅ H n) :
    AbutsTo (descend ι E hE) H' := by
  obtain ⟨hinf, F, hF, hbounds, hgr⟩ := habuts
  have hP := essImage_filtration ι hE hinf F hF hbounds hgr
  refine ⟨fun p q => have := hinf p q; hasPageInfinityAt_descend ι E hE (p, q),
    fun n p => descendSubobject ι (eH n) (F n p) (hP n p),
    fun n p p' hpp' => descendSubobject_mono ι (eH n) (hF n hpp') _ _, fun n => ?_,
    fun p q => ?_⟩
  · have key : ∀ p, ι.map (descendSubobject ι (eH n) (F n p) (hP n p)).arrow =
        (descendSubobjectIso ι (eH n) (F n p) (hP n p)).hom ≫ (F n p).arrow ≫ (eH n).inv :=
      fun p => by
        rw [reassoc_of% (descendSubobjectIso_hom_arrow ι (eH n) (F n p) (hP n p)),
          Iso.hom_inv_id, Category.comp_id]
    obtain ⟨a, b, hab, ha, hb⟩ := hbounds n
    refine ⟨a, b, hab, ?_, ?_⟩
    · rw [← Subobject.isIso_arrow_iff_eq_top]
      have : IsIso (F n a).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 ha
      have : IsIso (ι.map (descendSubobject ι (eH n) (F n a) (hP n a)).arrow) := by
        rw [key]
        infer_instance
      exact isIso_of_fully_faithful ι _
    · change descendSubobject ι (eH n) (F n b) (hP n b) = ⊥
      rw [← Subobject.mk_arrow (descendSubobject ι (eH n) (F n b) (hP n b)),
        Subobject.mk_eq_bot_iff_zero]
      apply ι.map_injective
      rw [key, show (F n b).arrow = 0 by rw [hb, Subobject.bot_arrow], zero_comp, comp_zero,
        Functor.map_zero]
  · have := hinf p q
    exact ⟨ι.preimageIso (descendPageInfinityIso ι E hE (p, q) ≪≫ (hgr p q).some ≪≫
      (descendCokernelIso ι (eH (p + q)) (hF (p + q) (by omega)) _ _).symm)⟩

include hE in
/-- **Descent of a spectral sequence and of its abutment along a fully faithful exact functor
with weak Serre essential image.** Let `ι : 𝒜 ⥤ 𝒞` be fully faithful and exact, with essential
image a weak Serre subcategory, and let `E` be a cohomological spectral sequence of `𝒞` whose
page `r₀` lies in the essential image and which abuts to `H`. Then there are a spectral sequence
`E'` of `𝒜` and a graded object `H'` of `𝒜` with `ι(E'_r^{p,q}) ≅ E_r^{p,q}` for all pages,
`ι(H' n) ≅ H n`, and `E'` abuts to `H'`. -/
theorem exists_descend_abutsTo (habuts : AbutsTo E H) :
    ∃ (E' : CohomologicalSpectralSequence A r₀) (H' : ℤ → A),
      (∀ (r : ℤ) (hr : r₀ ≤ r) (pq : ℤ × ℤ),
        Nonempty (ι.obj ((E'.page r hr).X pq) ≅ (E.page r hr).X pq)) ∧
      (∀ n, Nonempty (ι.obj (H' n) ≅ H n)) ∧ AbutsTo E' H' :=
  ⟨descend ι E hE, fun n => (essImage_of_abutsTo ι hE habuts n).witness,
    fun r hr pq => ⟨descendPageXIso ι E hE r hr pq⟩,
    fun n => ⟨(essImage_of_abutsTo ι hE habuts n).getIso⟩,
    abutsTo_descend ι hE habuts fun n => (essImage_of_abutsTo ι hE habuts n).getIso⟩

end AbutsTo

section WeakSerre

variable {C : Type u'} [Category.{v'} C] [Abelian C] (P : ObjectProperty C) [P.IsWeakSerreClass]
  {D : Type u''} [Category.{v''} D] [Abelian D]

omit [Abelian C] [P.IsWeakSerreClass] in
/-- The essential image of the inclusion of a strictly full subcategory is the subcategory. -/
theorem essImage_ι_eq [P.IsClosedUnderIsomorphisms] : P.ι.essImage = P := by
  ext Y
  exact ⟨fun ⟨X, ⟨e⟩⟩ => P.prop_of_iso e X.property, fun h => ⟨⟨Y, h⟩, ⟨Iso.refl _⟩⟩⟩

/-- The essential image of the inclusion of a weak Serre subcategory is a weak Serre class. -/
instance isWeakSerreClass_essImage_ι : P.ι.essImage.IsWeakSerreClass := by
  rw [essImage_ι_eq]
  infer_instance

/-- The inclusion of a weak Serre subcategory preserves homology. -/
instance preservesHomology_ι_of_isWeakSerreClass : P.ι.PreservesHomology :=
  have := ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
  have := ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
  inferInstance

/-- **A spectral sequence whose page `r₀` lies in a weak Serre subcategory `P`, together with its
abutment, can be pushed along an exact functor `G : P ⥤ 𝒟` defined on `P` only.** Every page
and the abutment lie in `P`, by `CategoryTheory.SpectralSequence.essImage_page_X` and
`CategoryTheory.SpectralSequence.essImage_of_abutsTo`; the spectral sequence descends to `P`
(`CategoryTheory.SpectralSequence.descend`) and is then transported along `G`
(`CategoryTheory.SpectralSequence.map`, `CategoryTheory.SpectralSequence.AbutsTo.map`). -/
theorem exists_map_abutsTo_of_isWeakSerreClass (G : P.FullSubcategory ⥤ D) [G.Additive]
    [G.PreservesHomology] [G.PreservesMonomorphisms] {E : CohomologicalSpectralSequence C r₀}
    (hE : ∀ pq, P ((E.page r₀ le_rfl).X pq)) {H : ℤ → C} (habuts : AbutsTo E H) :
    ∃ (hpage : ∀ (r : ℤ) (hr : r₀ ≤ r) (pq : ℤ × ℤ), P ((E.page r hr).X pq))
      (hH : ∀ n, P (H n)) (E' : CohomologicalSpectralSequence D r₀),
      (∀ (r : ℤ) (hr : r₀ ≤ r) (pq : ℤ × ℤ),
        Nonempty ((E'.page r hr).X pq ≅ G.obj ⟨(E.page r hr).X pq, hpage r hr pq⟩)) ∧
      AbutsTo E' (fun n => G.obj ⟨H n, hH n⟩) := by
  have hE' : ∀ pq, P.ι.essImage ((E.page r₀ le_rfl).X pq) := by
    rw [essImage_ι_eq]
    exact hE
  have hpage : ∀ (r : ℤ) (hr : r₀ ≤ r) (pq : ℤ × ℤ), P ((E.page r hr).X pq) := by
    rw [← essImage_ι_eq P]
    exact essImage_page_X P.ι E hE'
  have hH : ∀ n, P (H n) := by
    rw [← essImage_ι_eq P]
    exact essImage_of_abutsTo P.ι hE' habuts
  refine ⟨hpage, hH, (descend P.ι E hE').map G, fun r hr pq =>
    ⟨G.mapIso (P.fullyFaithfulι.preimageIso (descendPageXIso P.ι E hE' r hr pq))⟩,
    (abutsTo_descend P.ι hE' habuts (H' := fun n => ⟨H n, hH n⟩)
      fun n => Iso.refl _).map G⟩

/-- **A spectral sequence whose page `r₀` lies in a weak Serre subcategory `P`, together with its
abutment, can be pushed along a functor `F : 𝒞 ⥤ 𝒟` that is only exact on `P`**, in the sense that
its restriction `P ⥤ 𝒟` is additive, preserves homology and preserves monomorphisms. This is
`CategoryTheory.SpectralSequence.exists_map_abutsTo_of_isWeakSerreClass` for the restriction of
`F`, read back in `𝒞`. -/
theorem exists_map_abutsTo_of_isWeakSerreClass' (F : C ⥤ D) [(P.ι ⋙ F).Additive]
    [(P.ι ⋙ F).PreservesHomology] [(P.ι ⋙ F).PreservesMonomorphisms]
    {E : CohomologicalSpectralSequence C r₀} (hE : ∀ pq, P ((E.page r₀ le_rfl).X pq))
    {H : ℤ → C}
    (habuts : AbutsTo E H) :
    ∃ E' : CohomologicalSpectralSequence D r₀,
      (∀ (r : ℤ) (hr : r₀ ≤ r) (pq : ℤ × ℤ),
        Nonempty ((E'.page r hr).X pq ≅ F.obj ((E.page r hr).X pq))) ∧
      AbutsTo E' (fun n => F.obj (H n)) := by
  obtain ⟨_, _, E', hE', habuts'⟩ :=
    exists_map_abutsTo_of_isWeakSerreClass P (P.ι ⋙ F) hE habuts
  exact ⟨E', hE', habuts'⟩

end WeakSerre

end CategoryTheory.SpectralSequence

end
