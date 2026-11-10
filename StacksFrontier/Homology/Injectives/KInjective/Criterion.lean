module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksFrontier.Algebra.Homology.InverseLimit
public import StacksFrontier.Homology.Injectives.KInjective.AcyclicSubobjects
public import StacksFrontier.Homology.Injectives.KInjective.SmallAcyclicComplexes
import StacksCore.Tactic.StacksAttribute

/-!
# K-injectivity from a bound on acyclic test complexes

Let `C` be a Grothendieck abelian category. A complex `I` of injective objects of `C` is
K-injective as soon as every map to it from a bounded-above acyclic complex whose terms are
uniformly small is null-homotopic. The uniform bound is `acyclicComplexSizeBound C` of
Tag 079K.

## Main results

* `Stacks.Injectives.isKInjective_of_small_boundedAbove_acyclic`: the criterion with the
  hypothesis stated as null-homotopy of maps of complexes.
* `Stacks.Injectives.isKInjective_of_injective_of_small_boundedAbove_acyclic`: the same with the
  hypothesis stated as vanishing of the induced maps in the homotopy category.

## Implementation notes

Size is the cardinality of the type of subobjects of a term, shrunk to the Grothendieck
universe `w` in which the Grothendieck axioms hold, so that it is independent of the universes
of the objects and morphisms of `C`. Boundedness above is written as the vanishing of all terms
above some degree, the same form as in Tag 079K.

The two main theorems temporarily remove `CategoryTheory.catToReflQuiver`, respectively
`CategoryTheory.ReflQuiver.toQuiver`, from instance search and supply the instance they need by
hand. Those two instances send typeclass resolution around the whole quiver hierarchy on the
way to the `Category` instance of `C`, which makes the Zorn argument below elaborate
prohibitively slowly; naming the instance explicitly is what keeps it fast.

## References

* [Stacks Project, Tag 079L](https://stacks.math.columbia.edu/tag/079L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u


namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{w} C]

open CochainComplex.HomComplex

omit [IsGrothendieckAbelian.{w, v, u} C] in
private lemma cokernel_acyclic_of_mono_acyclic
    {K M : CochainComplex C ℤ} (i : K ⟶ M) [Mono i]
    (hK : K.Acyclic) (hM : M.Acyclic) : (cokernel i).Acyclic := by
  let S := ShortComplex.mk i (cokernel.π i) (by simp)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel i) inferInstance inferInstance
  exact acyclic_right_of_shortExact S hS hK hM

private structure SmallAcyclicSubcomplexData (Q : CochainComplex C ℤ) where
  N : CochainComplex C ℤ
  f : N ⟶ Q
  mono_f : Mono f
  nonzero : ¬ IsZero N
  acyclic : N.Acyclic
  boundedAbove : ∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (N.X n)
  sizeBound : ∀ n : ℤ,
    Cardinal.mk (Shrink.{w} (Subobject (N.X n))) ≤
      acyclicComplexSizeBound (C := C)

private noncomputable def acyclicSubobjectSmallData (M : CochainComplex C ℤ)
    (hM : M.Acyclic) (S : Subobject M) (hS : (S : CochainComplex C ℤ).Acyclic)
    (htop : S ≠ ⊤) : SmallAcyclicSubcomplexData (cokernel S.arrow) := by
  classical
  let Q := cokernel S.arrow
  have hQ : Q.Acyclic := cokernel_acyclic_of_mono_acyclic S.arrow hS hM
  have hQ₀ : ¬ IsZero Q := by
    intro h
    have : Epi S.arrow := (Preadditive.epi_iff_isZero_cokernel S.arrow).2 h
    have : IsIso S.arrow := isIso_of_mono_of_epi _
    exact htop ((Subobject.isIso_arrow_iff_eq_top S).1 this)
  let ex := exists_small_boundedAbove_acyclic_subcomplex Q hQ hQ₀
  let N := Classical.choose ex
  let exf := Classical.choose_spec ex
  let f := Classical.choose exf
  let hf := Classical.choose_spec exf
  exact ⟨N, f, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

private noncomputable def acyclicSubobjectExtension (M : CochainComplex C ℤ)
    (hM : M.Acyclic) (S : Subobject M) (hS : (S : CochainComplex C ℤ).Acyclic)
    (htop : S ≠ ⊤) : Subobject M :=
  let d := acyclicSubobjectSmallData M hM S hS htop
  letI : Mono d.f := d.mono_f
  (Subobject.pullback (cokernel.π S.arrow)).obj (Subobject.mk d.f)

private lemma acyclicSubobjectExtension_le (M : CochainComplex C ℤ) (hM : M.Acyclic)
    (S : Subobject M) (hS : (S : CochainComplex C ℤ).Acyclic) (htop : S ≠ ⊤) :
    S ≤ acyclicSubobjectExtension M hM S hS htop := by
  unfold acyclicSubobjectExtension
  apply subobject_le_pullback_of_comp_zero_subobject
  simp [cokernel.condition]

private lemma acyclicSubobjectExtension_acyclic (M : CochainComplex C ℤ) (hM : M.Acyclic)
    (S : Subobject M) (hS : (S : CochainComplex C ℤ).Acyclic) (htop : S ≠ ⊤) :
    (acyclicSubobjectExtension M hM S hS htop : CochainComplex C ℤ).Acyclic := by
  classical
  unfold acyclicSubobjectExtension
  let d := acyclicSubobjectSmallData M hM S hS htop
  let : Mono d.f := d.mono_f
  let T := Subobject.mk d.f
  obtain ⟨s, hsArrow, hs, hseq⟩ := pullbackPreimage_shortExact S.arrow T
  have hT : (T : CochainComplex C ℤ).Acyclic := fun n =>
    (d.acyclic n).of_iso (Subobject.underlyingIso d.f).symm
  exact acyclic_middle_of_shortExact _ hseq hS hT

private lemma acyclicSubobjectExtension_strict (M : CochainComplex C ℤ) (hM : M.Acyclic)
    (S : Subobject M) (hS : (S : CochainComplex C ℤ).Acyclic) (htop : S ≠ ⊤) :
    S < acyclicSubobjectExtension M hM S hS htop := by
  classical
  let hle' := acyclicSubobjectExtension_le M hM S hS htop
  apply lt_of_le_of_ne hle'
  intro hEq
  let d := acyclicSubobjectSmallData M hM S hS htop
  let : Mono d.f := d.mono_f
  let T := Subobject.mk d.f
  let P := (Subobject.pullback (cokernel.π S.arrow)).obj T
  have hP : acyclicSubobjectExtension M hM S hS htop = P := by
    simp [acyclicSubobjectExtension, d, T, P]
  rw [hP] at hEq
  obtain ⟨s, hsArrow, hs, hseq⟩ := pullbackPreimage_shortExact S.arrow T
  have hleP : S ≤ P := by simpa [P, hP] using hle'
  have hse : s = Subobject.ofLE S P hleP := by
    apply (cancel_mono P.arrow).1
    rw [hsArrow, Subobject.ofLE_arrow]
  have hsIso : IsIso s := by
    rw [hse]
    let e := Subobject.isoOfEq S P hEq
    have he : IsIso e.hom := inferInstance
    simpa [e] using he
  have : IsIso s := hsIso
  have : Epi s := inferInstance
  have : Epi (Subobject.pullbackπ (cokernel.π S.arrow) T) := hseq.epi_g
  have hpzero : Subobject.pullbackπ (cokernel.π S.arrow) T = 0 := by
    apply (cancel_epi s).1
    simpa using hs
  have hTzero : IsZero (T : CochainComplex C ℤ) :=
    IsZero.of_epi_eq_zero _ hpzero
  exact d.nonzero (IsZero.of_iso hTzero (Subobject.underlyingIso d.f).symm)

private noncomputable def homComplexPrecomp {K L I : CochainComplex C ℤ}
    (f : K ⟶ L) : CochainComplex.HomComplex L I ⟶ CochainComplex.HomComplex K I := by
  classical
  refine
    { f := fun n => AddCommGrpCat.ofHom
        { toFun := fun z => (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n)
          map_zero' := by simp
          map_add' := by simp }
      comm' := ?_ }
  intro n m hnm
  ext z
  change CochainComplex.HomComplex.δ n m
      ((CochainComplex.HomComplex.Cochain.ofHom f).comp
        (z : CochainComplex.HomComplex.Cochain L I n) (zero_add n)) =
    (CochainComplex.HomComplex.Cochain.ofHom f).comp
      (CochainComplex.HomComplex.δ n m
        (z : CochainComplex.HomComplex.Cochain L I n)) (zero_add m)
  exact CochainComplex.HomComplex.δ_ofHom_comp f
    (z : CochainComplex.HomComplex.Cochain L I n) m

omit [IsGrothendieckAbelian.{w, v, u} C] in
private lemma homComplexPrecomp_surjective {K L I : CochainComplex C ℤ}
    (f : K ⟶ L) (hf : ∀ n, Mono (f.f n)) (hI : ∀ n, Injective (I.X n)) (d : ℤ) :
    Function.Surjective (ConcreteCategory.hom ((homComplexPrecomp (I := I) f).f d)) := by
  classical
  intro z
  let z' : CochainComplex.HomComplex.Cochain L I d :=
    CochainComplex.HomComplex.Cochain.mk fun p q hpq => by
      let := hI q
      exact Injective.factorThru (z.v p q hpq) (f.f p)
  refine ⟨z', ?_⟩
  change (CochainComplex.HomComplex.Cochain.ofHom f).comp z' (zero_add d) = z
  ext p q hpq
  let := hI q
  let := hf p
  simp [z']

/-- Whiskering the cochain of a homotopy on the left by a morphism is the cochain of the
whiskered homotopy. -/
private lemma ofHom_comp_ofHomotopy {D : Type*} [Category D] [Preadditive D]
    {K L I : CochainComplex D ℤ} {f g : L ⟶ I}
    (e : K ⟶ L) (H : Homotopy f g) :
    (Cochain.ofHom e).comp (Cochain.ofHomotopy H) (zero_add (-1)) =
      Cochain.ofHomotopy (H.compLeft e) := by
  ext p q hpq
  simp [Cochain.ofHomotopy, Cochain.zero_cochain_comp_v]

omit [IsGrothendieckAbelian.{w, v, u} C] in
private lemma homotopyZero_of_shortExact
    {I : CochainComplex C ℤ} (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (f : S.X₂ ⟶ I)
    (H₁ : Homotopy (S.f ≫ f) 0)
    (hQzero : ∀ g : S.X₃ ⟶ I, Nonempty (Homotopy g 0))
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    ∃ H : Homotopy f 0,
      Cochain.ofHomotopy (H.compLeft S.f) = Cochain.ofHomotopy H₁ := by
  classical
  let : Mono S.f := hS.mono_f
  have hmono : ∀ n, Mono (S.f.f n) := by
    intro n
    exact (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_mono S.f
  obtain ⟨z, hz⟩ := homComplexPrecomp_surjective S.f hmono hI (-1)
      (Cochain.ofHomotopy H₁)
  let zB : Cochain S.X₂ I (-1) := z
  have hz' : (Cochain.ofHom S.f).comp zB (zero_add (-1)) =
      Cochain.ofHomotopy H₁ := hz
  have hdefC : δ 0 1 (Cochain.ofHom f - δ (-1) 0 zB) = 0 := by
    simp only [Int.reduceNeg, δ_sub, δ_ofHom, zero_sub, neg_eq_zero]
    exact δ_δ (-1) 0 1 zB
  let dC : Cocycle S.X₂ I 0 :=
    Cocycle.mk (Cochain.ofHom f - δ (-1) 0 zB) 1 (zero_add 1) hdefC
  let d : S.X₂ ⟶ I := Cocycle.homOf dC
  have hd : Cochain.ofHom d = Cochain.ofHom f - δ (-1) 0 zB := by
    simp [d, dC]
  have hfd : S.f ≫ d = 0 := by
    apply (Cocycle.equivHom S.X₁ I).injective
    change Cocycle.ofHom (S.f ≫ d) = Cocycle.ofHom 0
    apply Cocycle.ext
    rw [Cocycle.ofHom_coe, Cocycle.ofHom_coe, Cochain.ofHom_comp, hd, Cochain.comp_sub,
      ← Cochain.ofHom_comp, ← δ_ofHom_comp, hz', δ_ofHomotopy]
    simp
  let : Epi S.g := hS.epi_g
  let g := hS.exact.desc d hfd
  have hgd : S.g ≫ g = d := hS.exact.g_desc d hfd
  obtain ⟨H₂⟩ := hQzero g
  let zQ : Cochain S.X₂ I (-1) :=
    (Cochain.ofHom S.g).comp (Cochain.ofHomotopy H₂) (zero_add (-1))
  have hzQ : δ (-1) 0 zQ = Cochain.ofHom d := by
    change δ (-1) 0 ((Cochain.ofHom S.g).comp
      (Cochain.ofHomotopy H₂) (zero_add (-1))) = Cochain.ofHom d
    rw [δ_ofHom_comp, δ_ofHomotopy]
    simp only [Cochain.ofHom_zero, sub_zero]
    rw [← Cochain.ofHom_comp, hgd]
  have hδ : δ (-1) 0 (zB + zQ) = Cochain.ofHom f := by
    rw [δ_add, hzQ, hd]
    abel
  let H := (Cochain.equivHomotopy f 0).symm ⟨zB + zQ, by simp [hδ]⟩
  refine ⟨H, ?_⟩
  have hzQres :
      (Cochain.ofHom S.f).comp zQ (zero_add (-1)) = 0 := by
    dsimp [zQ]
    calc
      (Cochain.ofHom S.f).comp
          ((Cochain.ofHom S.g).comp (Cochain.ofHomotopy H₂) (zero_add (-1)))
          (zero_add (-1)) =
        ((Cochain.ofHom S.f).comp (Cochain.ofHom S.g) (zero_add 0)).comp
          (Cochain.ofHomotopy H₂) (zero_add (-1)) :=
            (Cochain.comp_assoc_of_first_is_zero_cochain
              (Cochain.ofHom S.f) (Cochain.ofHom S.g)
              (Cochain.ofHomotopy H₂) (zero_add (-1))).symm
      _ = (Cochain.ofHom (S.f ≫ S.g)).comp (Cochain.ofHomotopy H₂)
          (zero_add (-1)) := by rw [← Cochain.ofHom_comp]
      _ = 0 := by rw [S.zero]; simp
  have hzsum :
      (Cochain.ofHom S.f).comp (zB + zQ) (zero_add (-1)) =
        Cochain.ofHomotopy H₁ := by
    rw [Cochain.comp_add, hz', hzQres, add_zero]
  have hHco : Cochain.ofHomotopy H = zB + zQ :=
    congrArg Subtype.val
      ((Cochain.equivHomotopy f 0).apply_symm_apply ⟨zB + zQ, by simp [hδ]⟩)
  rw [← ofHom_comp_ofHomotopy, hHco]
  exact hzsum

private lemma acyclicSubobjectExtension_homotopy
    (I : CochainComplex C ℤ) (hI : ∀ n : ℤ, Injective (I.X n))
    (hvanish : ∀ (N : CochainComplex C ℤ), N.Acyclic →
      (∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (N.X n)) →
      (∀ n : ℤ, Cardinal.mk (Shrink.{w} (Subobject (N.X n))) ≤
        acyclicComplexSizeBound (C := C)) →
      ∀ g : N ⟶ I, Nonempty (Homotopy g 0))
    (M : CochainComplex C ℤ) (hM : M.Acyclic) (f : M ⟶ I)
    (S : Subobject M) (hS : (S : CochainComplex C ℤ).Acyclic) (htop : S ≠ ⊤)
    (H : Homotopy (S.arrow ≫ f) 0) :
    ∃ H' : Homotopy ((acyclicSubobjectExtension M hM S hS htop).arrow ≫ f) 0,
      (Cochain.ofHom (Subobject.ofLE S (acyclicSubobjectExtension M hM S hS htop)
          (acyclicSubobjectExtension_le M hM S hS htop))).comp
          (Cochain.ofHomotopy H') (zero_add (-1)) =
        Cochain.ofHomotopy H := by
  classical
  let d := acyclicSubobjectSmallData M hM S hS htop
  let : Mono d.f := d.mono_f
  let T := Subobject.mk d.f
  let P := (Subobject.pullback (cokernel.π S.arrow)).obj T
  have hP : acyclicSubobjectExtension M hM S hS htop = P := by
    simp [acyclicSubobjectExtension, d, T, P]
  obtain ⟨s, hsArrow, hs, hseq⟩ := pullbackPreimage_shortExact S.arrow T
  let R := ShortComplex.mk s (Subobject.pullbackπ (cokernel.π S.arrow) T) hs
  have hR : R.ShortExact := by simpa [R] using hseq
  have heq : s ≫ P.arrow ≫ f = S.arrow ≫ f := by
    dsimp [P]
    calc
      s ≫ ((Subobject.pullback (cokernel.π S.arrow)).obj T).arrow ≫ f =
          (s ≫ ((Subobject.pullback (cokernel.π S.arrow)).obj T).arrow) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = S.arrow ≫ f := congrArg (fun k => k ≫ f) hsArrow
  let H₁ : Homotopy (s ≫ (P.arrow ≫ f)) 0 :=
    (Homotopy.ofEq heq).trans H
  have hT : (T : CochainComplex C ℤ).Acyclic := fun n =>
    (d.acyclic n).of_iso (Subobject.underlyingIso d.f).symm
  have hTzero : ∀ g : (T : CochainComplex C ℤ) ⟶ I,
      Nonempty (Homotopy g 0) := by
    intro g
    let e := Subobject.underlyingIso d.f
    obtain ⟨H⟩ := hvanish d.N d.acyclic d.boundedAbove d.sizeBound (e.inv ≫ g)
    have heq : e.hom ≫ (e.inv ≫ g) = g := e.hom_inv_id_assoc g
    exact ⟨by simpa using (Homotopy.ofEq heq.symm).trans (H.compLeft e.hom)⟩
  let H₁' : Homotopy (R.f ≫ (P.arrow ≫ f)) 0 := by simpa [R] using H₁
  obtain ⟨H', hH'⟩ := homotopyZero_of_shortExact R hR (P.arrow ≫ f)
    H₁' hTzero hI
  have hSP : S ≤ P := by
    apply subobject_le_pullback_of_comp_zero_subobject (cokernel.π S.arrow) S T
    simp [cokernel.condition]
  have hsEq : s = Subobject.ofLE S P hSP := by
    apply (cancel_mono P.arrow).1
    rw [hsArrow, Subobject.ofLE_arrow]
  have hExt :
      (Cochain.ofHom (Subobject.ofLE S P hSP)).comp (Cochain.ofHomotopy H')
        (zero_add (-1)) = Cochain.ofHomotopy H := by
    rw [← hsEq, ofHom_comp_ofHomotopy, hH']
    have hH₁' : Cochain.ofHomotopy H₁' = Cochain.ofHomotopy H₁ := by
      ext i j hij
      rfl
    rw [hH₁']
    ext i j hij
    simp [H₁, Cochain.ofHomotopy, Homotopy.trans, Homotopy.ofEq]
  cases hP
  exact ⟨H', hExt⟩

omit [IsGrothendieckAbelian.{w, v, u} C] in
private lemma cochainOfCompatibleColimit.{t, q}
    {J : Type t} [Category.{q} J] [HasColimitsOfShape J C]
    (D : J ⥤ CochainComplex C ℤ) (c : Cocone D) (hc : IsColimit c)
    (I : CochainComplex C ℤ) (n : ℤ)
    (s : ∀ j, Cochain (D.obj j) I n)
    (hs : ∀ ⦃i j⦄ (f : i ⟶ j),
      (Cochain.ofHom (D.map f)).comp (s j) (zero_add n) = s i) :
    ∃ z : Cochain c.pt I n, ∀ j,
      (Cochain.ofHom (c.ι.app j)).comp z (zero_add n) = s j := by
  classical
  let cp (p q : ℤ) (hpq : p + n = q) :
      Cocone (D ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) p) :=
    Cocone.mk (I.X q) {
      app := fun j => (s j).v p q hpq
      naturality := fun i j f => by
        have hh := congrArg (fun z : Cochain (D.obj i) I n => z.v p q hpq) (hs f)
        simpa [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Functor.comp_map,
          HomologicalComplex.eval_map, Functor.const_obj_map] using hh }
  have hcol (p : ℤ) :
      IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone c) :=
    isColimitOfPreserves _ hc
  let z := Cochain.mk (fun p q hpq => (hcol p).desc (cp p q hpq))
  refine ⟨z, fun j => ?_⟩
  ext p q hpq
  dsimp [z]
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  have hf := (hcol p).fac (cp p q hpq) j
  change (HomologicalComplex.eval C (ComplexShape.up ℤ) p).map (c.ι.app j) ≫ _ = _ at hf
  rw [HomologicalComplex.eval_map] at hf
  change (c.ι.app j).f p ≫ _ = (s j).v p q hpq at hf
  convert hf

omit [IsGrothendieckAbelian.{w, v, u} C] in
private lemma homotopyOfCompatibleColimit.{t, q}
    {J : Type t} [Category.{q} J] [HasColimitsOfShape J C]
    (D : J ⥤ CochainComplex C ℤ) (c : Cocone D) (hc : IsColimit c)
    {I : CochainComplex C ℤ} (f : c.pt ⟶ I)
    (s : ∀ j, Cochain (D.obj j) I (-1))
    (hs : ∀ ⦃i j⦄ (g : i ⟶ j),
      (Cochain.ofHom (D.map g)).comp (s j) (zero_add (-1)) = s i)
    (hδ : ∀ j, δ (-1) 0 (s j) = Cochain.ofHom (c.ι.app j ≫ f)) :
    ∃ z : Cochain c.pt I (-1), δ (-1) 0 z = Cochain.ofHom f ∧
      ∀ j, (Cochain.ofHom (c.ι.app j)).comp z (zero_add (-1)) = s j := by
  obtain ⟨z, hz⟩ := cochainOfCompatibleColimit D c hc I (-1) s hs
  have hzδ : δ (-1) 0 z = Cochain.ofHom f := by
    ext p
    let ev := HomologicalComplex.eval C (ComplexShape.up ℤ) p
    have hcol : IsColimit (ev.mapCocone c) := isColimitOfPreserves ev hc
    apply hcol.hom_ext
    intro j
    calc
      (c.ι.app j).f p ≫ (δ (-1) 0 z).v p p (add_zero p) =
          ((Cochain.ofHom (c.ι.app j)).comp (δ (-1) 0 z) (zero_add 0)).v
            p p (add_zero p) := by simp []
      _ = (δ (-1) 0 ((Cochain.ofHom (c.ι.app j)).comp z (zero_add (-1)))).v
            p p (add_zero p) := by rw [δ_ofHom_comp]
      _ = (δ (-1) 0 (s j)).v p p (add_zero p) := by rw [hz j]
      _ = (Cochain.ofHom (c.ι.app j ≫ f)).v p p (add_zero p) := by rw [hδ]
      _ = (c.ι.app j).f p ≫ (Cochain.ofHom f).v p p (add_zero p) := by
        simp [Cochain.ofHom_comp]
  exact ⟨z, hzδ, hz⟩

private structure PartialNullHomotopy (M I : CochainComplex C ℤ) (f : M ⟶ I) where
  S : Subobject M
  acyclic : (S : CochainComplex C ℤ).Acyclic
  z : Cochain (S : CochainComplex C ℤ) I (-1)
  boundary : δ (-1) 0 z = Cochain.ofHom (S.arrow ≫ f)

private def partialNullHomotopyLE {M I : CochainComplex C ℤ} {f : M ⟶ I}
    (a b : PartialNullHomotopy M I f) : Prop :=
  ∃ h : a.S ≤ b.S,
    (Cochain.ofHom (Subobject.ofLE a.S b.S h)).comp b.z (zero_add (-1)) = a.z

private instance partialNullHomotopyPartialOrder {M I : CochainComplex C ℤ}
    {f : M ⟶ I} : PartialOrder (PartialNullHomotopy M I f) where
  le := partialNullHomotopyLE
  le_refl a := by
    refine ⟨le_rfl, ?_⟩
    simp [Subobject.ofLE_refl]
  le_trans a b c hab hbc := by
    rcases hab with ⟨hab, habz⟩
    rcases hbc with ⟨hbc, hbcz⟩
    refine ⟨hab.trans hbc, ?_⟩
    change (Cochain.ofHom (Subobject.ofLE a.S c.S (hab.trans hbc))).comp
      c.z (zero_add (-1)) = a.z
    rw [← Subobject.ofLE_comp_ofLE a.S b.S c.S hab hbc, Cochain.ofHom_comp,
      Cochain.comp_assoc_of_first_is_zero_cochain, hbcz, habz]
  le_antisymm a b hab hba := by
    rcases hab with ⟨hab, habz⟩
    rcases hba with ⟨hba, hbaz⟩
    cases a with
    | mk Sa ha za ba =>
      cases b with
      | mk Sb hb zb bb =>
        have hS : Sa = Sb := le_antisymm hab hba
        cases hS
        have hz : za = zb := by
          have habz' : zb = za := by simpa [Subobject.ofLE_refl] using habz
          exact habz'.symm
        cases hz
        rfl

omit [IsGrothendieckAbelian.{w, v, u} C] in
private lemma partialNullHomotopy_le_of_reverse
    {M I : CochainComplex C ℤ} {f : M ⟶ I}
    {a b : PartialNullHomotopy M I f} (habS : a.S ≤ b.S) (hba : b ≤ a) : a ≤ b := by
  rcases hba with ⟨hbaS, hbaz⟩
  let φ := Subobject.ofLE a.S b.S habS
  let ψ := Subobject.ofLE b.S a.S hbaS
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply (cancel_mono a.S.arrow).1
    dsimp [φ, ψ]
    simp only [Category.assoc, Subobject.ofLE_arrow, Category.id_comp]
  refine ⟨habS, ?_⟩
  calc
    (Cochain.ofHom φ).comp b.z (zero_add (-1)) =
        (Cochain.ofHom φ).comp
          ((Cochain.ofHom ψ).comp a.z (zero_add (-1))) (zero_add (-1)) := by rw [hbaz]
    _ = (Cochain.ofHom (φ ≫ ψ)).comp a.z (zero_add (-1)) := by
      rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
    _ = a.z := by rw [hφψ]; simp

omit [IsGrothendieckAbelian.{w, v, u} C] in
private lemma partialNullHomotopy_eq_of_same_subobject
    {M I : CochainComplex C ℤ} {f : M ⟶ I}
    {a b : PartialNullHomotopy M I f} (hS : a.S = b.S)
    (h : a ≤ b ∨ b ≤ a) : a = b := by
  rcases h with hab | hba
  · have hba' : b ≤ a := partialNullHomotopy_le_of_reverse
      (hS.symm ▸ le_rfl) hab
    exact le_antisymm hab hba'
  · have hab' : a ≤ b := partialNullHomotopy_le_of_reverse
      (hS ▸ le_rfl) hba
    exact le_antisymm hab' hba

private lemma partialNullHomotopy_chain_upperBound
    {M I : CochainComplex C ℤ} {f : M ⟶ I}
    (c : Set (PartialNullHomotopy M I f))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ b : PartialNullHomotopy M I f, ∀ a ∈ c, a ≤ b := by
  classical
  let R : Set (Subobject M) := {S | ∃ a, a ∈ c ∧ a.S = S}
  let J₀ := {S : Subobject M // S ∈ R}
  let : Small.{w} J₀ := inferInstance
  let : Category J₀ := Preorder.smallCategory J₀
  let J := Shrink.{w} J₀
  let : Category J := Preorder.smallCategory J
  let e : J₀ ≃ J := equivShrink.{w} J₀
  let SAt : J → Subobject M := fun j => (e.symm j).1
  let base : J → PartialNullHomotopy M I f := fun j =>
    Classical.choose (e.symm j).2
  have base_mem (j : J) : base j ∈ c := (Classical.choose_spec (e.symm j).2).1
  have base_sub (j : J) : (base j).S = SAt j :=
    (Classical.choose_spec (e.symm j).2).2
  have hbaseLE {i j : J} (hij : SAt i ≤ SAt j) : base i ≤ base j := by
    by_cases heq : base i = base j
    · simp [heq]
    · rcases hc (base_mem i) (base_mem j) heq with h | h
      · exact h
      · have hsub : (base i).S ≤ (base j).S := by
          calc
            (base i).S = SAt i := base_sub i
            _ ≤ SAt j := hij
            _ = (base j).S := (base_sub j).symm
        exact partialNullHomotopy_le_of_reverse hsub h
  have hJne : Nonempty J := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨equivShrink.{w} J₀ ⟨x.S, ⟨x, hx, rfl⟩⟩⟩
  let : IsFiltered J := {
    nonempty := hJne
    cocone_objs := by
      intro x y
      by_cases hxy : x = y
      · subst y
        exact ⟨x, 𝟙 x, 𝟙 x, trivial⟩
      · have hbase : base x ≠ base y := by
          intro hab
          apply hxy
          apply e.symm.injective
          apply Subtype.ext
          calc
            (e.symm x).1 = (base x).S := (base_sub x).symm
            _ = (base y).S := congrArg PartialNullHomotopy.S hab
            _ = (e.symm y).1 := base_sub y
        rcases hc (base_mem x) (base_mem y) hbase with h | h
        · have hs : SAt x ≤ SAt y := by
            calc
              SAt x = (base x).S := (base_sub x).symm
              _ ≤ (base y).S := h.1
              _ = SAt y := base_sub y
          have hxy : x ≤ y := by
            have hxy' := (equivShrink_le_equivShrink (α := J₀)).mpr hs
            rw [e.apply_symm_apply, e.apply_symm_apply] at hxy'
            exact hxy'
          exact ⟨y, homOfLE hxy, 𝟙 y, trivial⟩
        · have hs : SAt y ≤ SAt x := by
            calc
              SAt y = (base y).S := (base_sub y).symm
              _ ≤ (base x).S := h.1
              _ = SAt x := base_sub x
          have hyx : y ≤ x := by
            have hyx' := (equivShrink_le_equivShrink (α := J₀)).mpr hs
            rw [e.apply_symm_apply, e.apply_symm_apply] at hyx'
            exact hyx'
          exact ⟨x, 𝟙 x, homOfLE hyx, trivial⟩
    cocone_maps := by
      intro x y g h
      exact ⟨y, 𝟙 y, Subsingleton.elim _ _⟩ }
  let G : J → Subobject M := fun j => (base j).S
  let S : Subobject M := ⨆ j : J, G j
  let F : J ⥤ MonoOver M := {
    obj j := MonoOver.mk (G j).arrow
    map := fun {i j} g => MonoOver.homMk
      (Subobject.ofLE (G i) (G j) (by
        have h0 : (e.symm i) ≤ (e.symm j) :=
          (equivShrink_le_equivShrink (α := J₀)).mp (show e (e.symm i) ≤ e (e.symm j) from by
            rw [e.apply_symm_apply, e.apply_symm_apply]
            exact leOfHom g)
        have hij : base i ≤ base j := hbaseLE h0
        exact hij.1)) (by
        change Subobject.ofLE _ _ _ ≫ (G j).arrow = (G i).arrow
        rw [Subobject.ofLE_arrow])
    map_id := by intro j; apply Subsingleton.elim
    map_comp := by intro i j k g h; apply Subsingleton.elim }
  let cMono : Cocone F := {
    pt := MonoOver.mk S.arrow
    ι := {
      app := fun j => MonoOver.homMk (Subobject.ofLE (G j) S (le_iSup G j)) (by
        change Subobject.ofLE _ _ _ ≫ S.arrow = (G j).arrow
        rw [Subobject.ofLE_arrow])
      naturality := by intro i j g; apply Subsingleton.elim } }
  let cOver := (MonoOver.forget M).mapCocone cMono
  let : Mono cOver.pt.hom := by
    change Mono S.arrow
    exact Subobject.arrow_mono S
  have hsup : Subobject.mk cOver.pt.hom = ⨆ j, Subobject.mk (F.obj j).obj.hom := by
    calc
      Subobject.mk cOver.pt.hom = S := by simp [cOver, cMono, MonoOver.mk_arrow]
      _ = ⨆ j, G j := rfl
      _ = ⨆ j, Subobject.mk (F.obj j).obj.hom := by simp [F, G, MonoOver.mk_arrow]
  let : IsGrothendieckAbelian.{w} (CochainComplex C ℤ) := inferInstance
  have hcColim := IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
    F cOver hsup
  let D := F ⋙ MonoOver.forget M ⋙ Over.forget M
  let c := (Over.forget M).mapCocone cOver
  have hc' : IsColimit c := hcColim
  have hSacyclic : (S : CochainComplex C ℤ).Acyclic := by
    apply acyclic_of_filtered_colimit D c hc'
    intro j
    exact (base j).acyclic
  let g : (S : CochainComplex C ℤ) ⟶ I := S.arrow ≫ f
  have hcompat : ∀ ⦃i j⦄ (m : i ⟶ j),
      (Cochain.ofHom (D.map m)).comp (base j).z (zero_add (-1)) = (base i).z := by
    intro i j m
    have h0 : (e.symm i) ≤ (e.symm j) :=
      (equivShrink_le_equivShrink (α := J₀)).mp (show e (e.symm i) ≤ e (e.symm j) from by
        rw [e.apply_symm_apply, e.apply_symm_apply]
        exact leOfHom m)
    have hij : base i ≤ base j := hbaseLE h0
    obtain ⟨hSij, hz⟩ := hij
    change (Cochain.ofHom (Subobject.ofLE (base i).S (base j).S hSij)).comp
      (base j).z (zero_add (-1)) = (base i).z
    exact hz
  have hι (j : J) : c.ι.app j ≫ cOver.pt.hom = (G j).arrow := by
    change (cOver.ι.app j).left ≫ cOver.pt.hom = (G j).arrow
    exact (cOver.ι.app j).w
  have hsub : Subobject.mk cOver.pt.hom = Subobject.mk S.arrow := by
    rw [hsup]
    simp [S, F, G, MonoOver.mk_arrow]
  let eCS : c.pt ≅ (S : CochainComplex C ℤ) :=
    Subobject.isoOfMkEqMk cOver.pt.hom S.arrow hsub
  have heCS : eCS.hom ≫ S.arrow = cOver.pt.hom := by
    dsimp [eCS]
    simp
  have hinv : eCS.inv ≫ cOver.pt.hom = S.arrow := by
    rw [← heCS, eCS.inv_hom_id_assoc]
  let g₀ : c.pt ⟶ I := cOver.pt.hom ≫ f
  have hboundary₀ : ∀ j : J,
      δ (-1) 0 ((base j).z) = Cochain.ofHom (c.ι.app j ≫ g₀) := by
    intro j
    have hcomp : c.ι.app j ≫ (cOver.pt.hom ≫ f) = (G j).arrow ≫ f := by
      rw [← Category.assoc, hι]
      rfl
    change δ (-1) 0 ((base j).z) =
      Cochain.ofHom (c.ι.app j ≫ (cOver.pt.hom ≫ f))
    rw [hcomp]
    exact (base j).boundary
  obtain ⟨z₀, hzδ₀, hzj₀⟩ := homotopyOfCompatibleColimit D c hc' g₀
    (fun j => (base j).z) hcompat hboundary₀
  let z : Cochain (S : CochainComplex C ℤ) I (-1) :=
    (Cochain.ofHom eCS.inv).comp z₀ (zero_add (-1))
  have hres (j : J) :
      Subobject.ofLE (G j) S (le_iSup G j) ≫ eCS.inv = c.ι.app j := by
    apply (cancel_mono cOver.pt.hom).1
    have h1 :
        (Subobject.ofLE (G j) S (le_iSup G j) ≫ eCS.inv) ≫ cOver.pt.hom =
          (G j).arrow := by
      rw [Category.assoc, hinv, Subobject.ofLE_arrow]
    exact h1.trans (hι j).symm
  have hzj (j : J) :
      (Cochain.ofHom (Subobject.ofLE (G j) S (le_iSup G j))).comp z
        (zero_add (-1)) = (base j).z := by
    change (Cochain.ofHom (Subobject.ofLE (G j) S (le_iSup G j))).comp
      ((Cochain.ofHom eCS.inv).comp z₀ (zero_add (-1))) (zero_add (-1)) = (base j).z
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hres]
    exact hzj₀ j
  have hzδ : δ (-1) 0 z = Cochain.ofHom g := by
    change δ (-1) 0 ((Cochain.ofHom eCS.inv).comp z₀ (zero_add (-1))) =
      Cochain.ofHom (S.arrow ≫ f)
    rw [δ_ofHom_comp, hzδ₀, ← Cochain.ofHom_comp]
    apply congrArg Cochain.ofHom
    calc
      eCS.inv ≫ (cOver.pt.hom ≫ f) = (eCS.inv ≫ cOver.pt.hom) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = S.arrow ≫ f := by rw [hinv]
  let b : PartialNullHomotopy M I f := ⟨S, hSacyclic, z, hzδ⟩
  refine ⟨b, ?_⟩
  intro a ha
  let j : J := equivShrink.{w} J₀ ⟨a.S, ⟨a, ha, rfl⟩⟩
  have hjbase : base j = a := by
    have hj0 : e.symm j = ⟨a.S, ⟨a, ha, rfl⟩⟩ := e.symm_apply_apply _
    have hs : (base j).S = a.S := by
      rw [base_sub j]
      change (e.symm j).1 = a.S
      rw [hj0]
    by_cases heq : base j = a
    · exact heq
    · exact partialNullHomotopy_eq_of_same_subobject hs
        (hc (base_mem j) ha heq)
  have hlePair : base j ≤ b := ⟨le_iSup G j, hzj j⟩
  exact hjbase ▸ hlePair

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A complex of injective objects is K-injective provided that all maps to it from
bounded-above acyclic complexes within the uniform size bound are null-homotopic. -/
@[stacks 079L]
theorem isKInjective_of_small_boundedAbove_acyclic (I : CochainComplex C ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n))
    (hvanish : ∀ (M : CochainComplex C ℤ), M.Acyclic →
      (∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (M.X n)) →
      (∀ n : ℤ, Cardinal.mk (Shrink.{w} (Subobject (M.X n))) ≤
        acyclicComplexSizeBound (C := C)) →
      ∀ f : M ⟶ I, Nonempty (Homotopy f 0)) :
    I.IsKInjective := by
  refine { nonempty_homotopy_zero := ?_ }
  intro M f hM
  let : CategoryTheory.ReflQuiver C := CategoryTheory.catToReflQuiver
  let : Quiver C := CategoryTheory.ReflQuiver.toQuiver
  classical
  let P₀ : PartialNullHomotopy M I f := by
    let e := Subobject.botCoeIsoZero (B := M)
    have hbot : IsZero ((⊥ : Subobject M) : CochainComplex C ℤ) :=
      IsZero.of_iso (isZero_zero (C := CochainComplex C ℤ)) e
    have hac : ((⊥ : Subobject M) : CochainComplex C ℤ).Acyclic := by
      intro n
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      let F := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n
      have hzero : IsZero (F.obj (HomologicalComplex.zero)) :=
        F.map_isZero HomologicalComplex.isZero_zero
      let e' := hbot.iso HomologicalComplex.isZero_zero
      exact IsZero.of_iso hzero (F.mapIso e')
    have hzero : (⊥ : Subobject M).arrow = 0 := Subobject.bot_arrow
    refine ⟨⊥, hac, 0, ?_⟩
    simp [hzero]
  have hne : Nonempty (PartialNullHomotopy M I f) := ⟨P₀⟩
  obtain ⟨P, hPmax⟩ := zorn_le_nonempty (α := PartialNullHomotopy M I f)
    (fun c hc hcne => partialNullHomotopy_chain_upperBound c hc hcne)
  by_cases htop : P.S = ⊤
  · let e : (P.S : CochainComplex C ℤ) ≅ M :=
      (Subobject.isoOfEq P.S ⊤ htop).trans (Subobject.underlyingIso (𝟙 M))
    have he : e.hom = P.S.arrow := by
      dsimp [e, Subobject.isoOfEq]
      simp [Subobject.ofLE_arrow, Subobject.underlyingIso_top_hom]
    have hPB : δ (-1) 0 P.z = Cochain.ofHom (P.S.arrow ≫ f) := P.boundary
    let H := (Cochain.equivHomotopy (P.S.arrow ≫ f) 0).symm
      ⟨P.z, by simp [hPB]⟩
    have heq : e.inv ≫ P.S.arrow ≫ f = f := by
      calc
        e.inv ≫ P.S.arrow ≫ f = e.inv ≫ (e.hom ≫ f) := by rw [he]
        _ = (e.inv ≫ e.hom) ≫ f := (Category.assoc _ _ _).symm
        _ = f := by rw [e.inv_hom_id]; simp
    exact ⟨((Homotopy.ofEq heq.symm).trans (H.compLeft e.inv)).trans
      (.ofEq (by simp))⟩
  · have hPB : δ (-1) 0 P.z = Cochain.ofHom (P.S.arrow ≫ f) := P.boundary
    let H := (Cochain.equivHomotopy (P.S.arrow ≫ f) 0).symm
      ⟨P.z, by simp [hPB]⟩
    obtain ⟨H', hH'⟩ := acyclicSubobjectExtension_homotopy I hI hvanish
      M hM f P.S P.acyclic htop H
    let E := acyclicSubobjectExtension M hM P.S P.acyclic htop
    have hExtAcyclic : (E : CochainComplex C ℤ).Acyclic :=
      acyclicSubobjectExtension_acyclic M hM P.S P.acyclic htop
    let zE : Cochain (E : CochainComplex C ℤ) I (-1) := Cochain.ofHomotopy H'
    have hEboundary : δ (-1) 0 zE = Cochain.ofHom (E.arrow ≫ f) := by
      change δ (-1) 0 (Cochain.ofHomotopy H') = Cochain.ofHom (E.arrow ≫ f)
      rw [δ_ofHomotopy]
      simp [E]
    have hEH :
        (Cochain.ofHom (Subobject.ofLE P.S E
          (acyclicSubobjectExtension_le M hM P.S P.acyclic htop))).comp zE
          (zero_add (-1)) = P.z := by
      have hHval : Cochain.ofHomotopy H = P.z :=
        congrArg Subtype.val
          ((Cochain.equivHomotopy (P.S.arrow ≫ f) 0).apply_symm_apply
            ⟨P.z, by simp [hPB]⟩)
      simpa [zE, hHval] using hH'
    let Q : PartialNullHomotopy M I f := ⟨E, hExtAcyclic, zE, hEboundary⟩
    have hPQ : P ≤ Q :=
      ⟨acyclicSubobjectExtension_le M hM P.S P.acyclic htop, hEH⟩
    have hQmax : Q ≤ P := hPmax hPQ
    have hlt : P.S < E := acyclicSubobjectExtension_strict M hM P.S P.acyclic htop
    exact False.elim ((not_le_of_gt hlt) hQmax.1)
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver in
/-- A complex of injective objects in a Grothendieck abelian category is K-injective if every
map to it in the homotopy category from a uniformly small bounded-above acyclic complex is zero. -/
@[stacks 079L]
theorem isKInjective_of_injective_of_small_boundedAbove_acyclic
    (I : CochainComplex C ℤ) [∀ n : ℤ, Injective (I.X n)]
    (hI : ∀ (M : CochainComplex C ℤ), M.Acyclic →
      (∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (M.X n)) →
      (∀ n : ℤ, Cardinal.mk (Shrink.{w} (Subobject (M.X n))) ≤
        acyclicComplexSizeBound (C := C)) →
      ∀ f : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I, f = 0) :
    I.IsKInjective :=
  isKInjective_of_small_boundedAbove_acyclic I (fun _ => inferInstance) fun M hM hb hs g =>
    (HomotopyCategory.quotient_map_eq_zero_iff g).1
      (hI M hM hb hs ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g))

end Stacks.Injectives
