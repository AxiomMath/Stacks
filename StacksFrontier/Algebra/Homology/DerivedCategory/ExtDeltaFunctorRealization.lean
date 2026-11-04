module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories

/-!
# Realizing a map of `Ext` `δ`-functors by a morphism of the derived category

Let `C` be an abelian category. An object `L` of `D(C)` defines the `δ`-functor
`F ↦ Hom_{D(C)}(L, F[n])` on `C`: it is functorial in `F`, and a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of `C` gives connecting maps, composition with the connecting morphism
`F₃ ⟶ F₁[1]` of `D(C)` (`CategoryTheory.ShortComplex.ShortExact.singleδ`). This file proves that
for bounded above `L`, `L'` (and `C` with enough projectives and injectives, e.g. modules over a
ring) every map of such `δ`-functors that is bijective on injective objects is composition with
an isomorphism `L' ≅ L`. It is the derived-category input of the affine case of the module-level
uniqueness in [Stacks, Tag 0DJV].

## The argument

Represent `L` and `L'` by bounded above complexes of projectives `P`, `P'` (Stacks 05T7), which
are K-projective. Then a morphism `P ⟶ F[n]` of `D(C)` is the class of a map `f : P^{-n} → F`
killed by the differential, two maps having the same class when they differ by `h ∘ d`
(`Stacks.ExtDeltaFunctorRealization.cls` with `cls_surjective` and `cls_eq_cls_iff`). Put
`M_p = coker(P^{p-1} → P^p)`; every class factors through the tautological class
`can_p : P ⟶ M_p[-p]` (`exists_eq_can_comp`).

* `φ(can_p)` is the class of a map `a_p : M'_p ⟶ M_p` (precomposed with `P'^p ↠ M'_p`), and by
  naturality `φ` is determined by the `a_p`.
* The connecting morphism of a short exact sequence acts on classes as the snake map: if
  `f : K^p → X₃` lifts to `f̃ : K^p → X₂`, the class of `f` composed with `X₃ ⟶ X₁[1]` is
  `(-1)^m` times the class of the map `K^{p-1} → X₁` through which `d ≫ f̃` factors
  (`cls_comp_singleδ`, `cls_toSingleMk_comp_singleδ`). This is computed on the mapping cone
  of `X₁[0] ⟶ X₂[0]`, through which Mathlib defines the connecting morphism.
* Applying the compatibility of `φ` with the connecting morphism of
  `0 → ker(P^p ↠ M_p) → P^p → M_p → 0` to `can_p` lets one choose lifts
  `b_p : P'^p ⟶ P^p` of `a_p` compatible with the differentials (projectivity of `P'^p`); they
  form a chain map `g : P' ⟶ P` with `φ = g^*` (`exists_hom_eq_comp_of_isKProjective`).
* Bijectivity on injective objects makes `g` an isomorphism: the cone `Z` of `g` has
  `Hom(Z, I[n]) = 0` for injective `I`, and if `Z ≠ 0` its top cohomology `H^m(Z)` embeds in an
  injective `I`, giving a nonzero map `Z ⟶ I[-m]` by [Stacks, Tag 06XS]
  (`isIso_of_bijective_comp_singleFunctor_injective`).

The realizing morphism is not unique in general (module-level ghosts exist), so only existence is
asserted.

## Main results

* `Stacks.ExtDeltaFunctorRealization.exists_hom_eq_comp_of_isKProjective` — fullness: a natural,
  `δ`-compatible map out of a K-projective complex into one with projective terms is `g^*`.
* `Stacks.ExtDeltaFunctorRealization.isIso_of_bijective_comp_singleFunctor_injective` —
  shifted injective objects detect isomorphisms between bounded above objects.
* `Stacks.ExtDeltaFunctorRealization.exists_isIso_eq_comp_of_isLE` and its module form
  `Stacks.ExtDeltaFunctorRealization.exists_isIso_eq_comp_of_isLE_moduleCat` — the realization
  by an isomorphism.

## Implementation notes

Everything is stated over an arbitrary model `[HasDerivedCategory C]` of the derived category.

## References

* [Stacks Project, Tag 0DJV](https://stacks.math.columbia.edu/tag/0DJV)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive Pretriangulated
open CochainComplex HomComplex DerivedCategory ZeroObject

universe w v u

namespace Stacks.ExtDeltaFunctorRealization

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-! ### Classes of cocycles in the derived category -/

/-- The morphism `K ⟶ L⟦n⟧` of the derived category given by a cocycle of degree `n` of the
Hom complex `Hom(K, L)`. -/
def cls {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n) : Q.obj K ⟶ (Q.obj L)⟦n⟧ :=
  Q.map (Cocycle.equivHomShift.symm z) ≫ (Q.commShiftIso n).hom.app L

variable {K L : CochainComplex C ℤ} {n : ℤ}

/-- The class of a sum of cocycles is the sum of their classes. -/
lemma cls_add (z z' : Cocycle K L n) : cls (z + z') = cls z + cls z' := by
  simp [cls, map_add, Functor.map_add, add_comp]

/-- The class of the negative of a cocycle is the negative of its class. -/
lemma cls_neg (z : Cocycle K L n) : cls (-z) = -cls z := by
  simp [cls, map_neg, Functor.map_neg, neg_comp]

/-- The class of a difference of cocycles is the difference of their classes. -/
lemma cls_sub (z z' : Cocycle K L n) : cls (z - z') = cls z - cls z' := by
  rw [sub_eq_add_neg, cls_add, cls_neg, ← sub_eq_add_neg]

/-- The class of the zero cocycle is zero. -/
lemma cls_zero : cls (0 : Cocycle K L n) = 0 := by
  simp [cls]

/-- The class of a cocycle postcomposed with a morphism of complexes `g : L ⟶ L'` is the class of
the cocycle followed by the shift of `Q.map g`. -/
lemma cls_postcomp (z : Cocycle K L n) {L' : CochainComplex C ℤ} (g : L ⟶ L') :
    cls (z.postcomp g) = cls z ≫ (Q.map g)⟦n⟧' := by
  simp only [cls, Cocycle.equivHomShift_symm_postcomp, Functor.map_comp, assoc]
  rw [← Functor.commShiftIso_hom_naturality]

/-- The class of a cocycle precomposed with a morphism of complexes `g : K' ⟶ K` is `Q.map g`
followed by the class of the cocycle. -/
lemma cls_precomp (z : Cocycle K L n) {K' : CochainComplex C ℤ} (g : K' ⟶ K) :
    cls (z.precomp g) = Q.map g ≫ cls z := by
  simp only [cls, Cocycle.equivHomShift_symm_precomp, Functor.map_comp, assoc]

/-- A coboundary has zero class. -/
lemma cls_eq_zero_of_mem_coboundaries (z : Cocycle K L n)
    (hz : z ∈ HomComplex.coboundaries K L n) : cls z = 0 := by
  rw [← CohomologyClass.toHom_mk_eq_zero_iff, CohomologyClass.toHom_mk] at hz
  have h : Q.map (Cocycle.equivHomShift.symm z) = 0 := by
    rw [← cancel_epi ((quotientCompQhIso C).hom.app K), ← quotientCompQhIso_hom_naturality,
      hz, Functor.map_zero, zero_comp, comp_zero]
  simp [cls, h]

/-- If `K` is K-projective, every morphism `Q.obj K ⟶ Q.obj L` of the derived category is the
image of a morphism of complexes `K ⟶ L`. -/
lemma Q_map_surjective_of_isKProjective (K L : CochainComplex C ℤ) [K.IsKProjective]
    (g : Q.obj K ⟶ Q.obj L) : ∃ f : K ⟶ L, Q.map f = g := by
  obtain ⟨u, hu⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C _).obj L)).surjective
    ((quotientCompQhIso C).hom.app K ≫ g ≫ (quotientCompQhIso C).inv.app L)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective u
  refine ⟨f, ?_⟩
  rw [← cancel_epi ((quotientCompQhIso C).hom.app K), ← quotientCompQhIso_hom_naturality, hu]
  simp

/-- If `K` is K-projective, a morphism of complexes `f : K ⟶ L` is zero in the derived category
if and only if it is zero in the homotopy category. -/
lemma Q_map_eq_zero_iff_of_isKProjective {K L : CochainComplex C ℤ} [K.IsKProjective]
    (f : K ⟶ L) : Q.map f = 0 ↔ (HomotopyCategory.quotient C _).map f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply (CochainComplex.IsKProjective.Qh_map_bijective K
      ((HomotopyCategory.quotient C _).obj L)).injective
    rw [Functor.map_zero, ← cancel_mono ((quotientCompQhIso C).hom.app L),
      quotientCompQhIso_hom_naturality, h, comp_zero, zero_comp]
  · rw [← cancel_epi ((quotientCompQhIso C).hom.app K), ← quotientCompQhIso_hom_naturality,
      h, Functor.map_zero, zero_comp, comp_zero]

/-- If `K` is K-projective, every morphism `Q.obj K ⟶ (Q.obj L)⟦n⟧` is the class of a cocycle. -/
lemma cls_surjective [K.IsKProjective] : Function.Surjective (cls : Cocycle K L n → _) := by
  intro x
  obtain ⟨f, hf⟩ := Q_map_surjective_of_isKProjective K (L⟦n⟧)
    (x ≫ (Q.commShiftIso n).inv.app L)
  refine ⟨Cocycle.equivHomShift f, ?_⟩
  simp [cls, hf]

/-- If `K` is K-projective, a cocycle with zero class is a coboundary. -/
lemma mem_coboundaries_of_cls_eq_zero [K.IsKProjective] (z : Cocycle K L n) (hz : cls z = 0) :
    z ∈ HomComplex.coboundaries K L n := by
  rw [← CohomologyClass.toHom_mk_eq_zero_iff, CohomologyClass.toHom_mk,
    ← Q_map_eq_zero_iff_of_isKProjective, ← cancel_mono ((Q.commShiftIso n).hom.app L),
    zero_comp]
  exact hz

/-- If `K` is K-projective, two cocycles have the same class if and only if their difference is
a coboundary. -/
lemma cls_eq_cls_iff [K.IsKProjective] (z z' : Cocycle K L n) :
    cls z = cls z' ↔ z - z' ∈ HomComplex.coboundaries K L n := by
  refine ⟨fun h ↦ mem_coboundaries_of_cls_eq_zero _ (by rw [cls_sub, h, sub_self]),
    fun h ↦ ?_⟩
  rw [← sub_eq_zero, ← cls_sub]
  exact cls_eq_zero_of_mem_coboundaries _ h

/-! ### The connecting morphism of a short exact sequence on cocycle classes -/

omit [HasDerivedCategory.{w} C] in
/-- The cocycle of a composite of shifted morphisms of complexes is the composite of the
cocycles. -/
lemma equivHomShift_shiftedHom_comp {K L M : CochainComplex C ℤ} {a b c : ℤ}
    (f : K ⟶ L⟦a⟧) (g : L ⟶ M⟦b⟧) (h : b + a = c) :
    (Cocycle.equivHomShift (ShiftedHom.comp (f : ShiftedHom K L a) (g : ShiftedHom L M b) h) :
      Cochain K M c) =
      (Cocycle.equivHomShift f : Cochain K L a).comp
        (Cocycle.equivHomShift g : Cochain L M b) (by omega) := by
  ext p q hpq
  rw [Cochain.comp_v _ _ (show a + b = c by omega) p (p + a) q rfl (by omega)]
  simp [ShiftedHom.comp, Cocycle.equivHomShift_apply,
    Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p),
    Cochain.rightUnshift_v _ _ _ (p + a) q _ (p + a) (add_zero _),
    shiftFunctorAdd'_inv_app_f', shiftFunctorObjXIso]

variable {S : ShortComplex C} (hS : S.ShortExact)

/-- **The connecting morphism on cocycle classes.** Let `0 → X₁ → X₂ → X₃ → 0` be short exact,
`x₃` a cocycle of degree `n` from `K` to `X₃[0]`, `β` a cochain to `X₂[0]` lifting it and `α` a
cocycle of degree `m = n + 1` to `X₁[0]` with `δ β + α ∘ f = 0`. Then composing the class of
`x₃` with the connecting morphism `X₃ ⟶ X₁[1]` of the sequence gives minus the class of
`α`. -/
theorem cls_comp_singleδ {n m : ℤ} (hnm : 1 + n = m)
    (x₃ : Cocycle K ((CochainComplex.singleFunctor C 0).obj S.X₃) n)
    (β : Cochain K ((CochainComplex.singleFunctor C 0).obj S.X₂) n)
    (hβ : β.comp (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map S.g)) (add_zero n) =
      (x₃ : Cochain _ _ n))
    (α : Cocycle K ((CochainComplex.singleFunctor C 0).obj S.X₁) m)
    (hα : δ n m β + (α : Cochain _ _ m).comp
      (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map S.f)) (add_zero m) = 0) :
    ShiftedHom.comp (cls x₃ : ShiftedHom (Q.obj K) ((DerivedCategory.singleFunctor C 0).obj S.X₃) n)
      hS.singleδ hnm = -cls α := by
  let T := S.map (HomologicalComplex.single C (ComplexShape.up ℤ) 0)
  have hT : T.ShortExact := hS.map_of_exact _
  let y : Cocycle K (mappingCone T.f) n :=
    mappingCone.liftCocycle T.f α β (by omega) hα
  have h1 : x₃ = y.postcomp (mappingCone.descShortComplex T) := by
    ext : 1
    simp only [Cocycle.postcomp_coe, y, mappingCone.liftCocycle_coe,
      mappingCone.descShortComplex, mappingCone.ofHom_desc,
      mappingCone.liftCochain_descCochain, Cochain.comp_zero, zero_add]
    exact hβ.symm
  let ψ : ShiftedHom (mappingCone T.f) T.X₁ (1 : ℤ) :=
    Cocycle.homOf ((-mappingCone.fst T.f).rightShift 1 0 (zero_add 1))
  have h2 : (Cocycle.equivHomShift ψ).1 = -(mappingCone.fst T.f).1 := by
    simp [ψ, Cocycle.equivHomShift_apply]
  have h3 : ShiftedHom.comp (Cocycle.equivHomShift.symm y : ShiftedHom K (mappingCone T.f) n)
      ψ hnm = Cocycle.equivHomShift.symm (-α) := by
    apply Cocycle.equivHomShift.injective
    rw [AddEquiv.apply_symm_apply]
    ext : 1
    rw [equivHomShift_shiftedHom_comp, AddEquiv.apply_symm_apply, h2]
    simp [y]
  have h4 : (cls x₃ : ShiftedHom (Q.obj K) (Q.obj T.X₃) n) =
      (ShiftedHom.map (Cocycle.equivHomShift.symm y : ShiftedHom K (mappingCone T.f) n) Q).comp
        (ShiftedHom.mk₀ 0 rfl (Q.map (mappingCone.descShortComplex T))) (zero_add n) := by
    rw [h1, cls_postcomp, ShiftedHom.comp_mk₀]
    rfl
  show ShiftedHom.comp (cls x₃ : ShiftedHom (Q.obj K) (Q.obj T.X₃) n)
    (triangleOfSESδ hT) hnm = _
  rw [h4, ShiftedHom.comp_assoc _ _ _ (zero_add n) (add_zero 1) (by omega), ShiftedHom.mk₀_comp,
    descShortComplex_triangleOfSESδ]
  show (ShiftedHom.map (Cocycle.equivHomShift.symm y : ShiftedHom K (mappingCone T.f) n) Q).comp
    (ShiftedHom.map ψ Q) hnm = _
  rw [← ShiftedHom.map_comp, h3, ← cls_neg]
  rfl

omit [HasDerivedCategory.{w} C] in
/-- The cochain to a single complex given by `k • f` is `k` times the cochain given by `f`. -/
lemma Cochain.toSingleMk_zsmul' {X : C} {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (k : ℤ) : Cochain.toSingleMk (k • f) h = k • Cochain.toSingleMk f h :=
  map_zsmul (Cochain.toSingleEquiv (K := K) (X := X) h).symm k f

/-- **The connecting morphism on degreewise classes.** For a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` and a map `f : K^p → X₃` killed by the differential, which lifts to
`f̃ : K^p → X₂`, let `h : K^{p-1} → X₁` be the map with `h ≫ (X₁ → X₂) = d ≫ f̃`. Composing the
class of `f` in degree `n = -p` with the connecting morphism `X₃ ⟶ X₁[1]` gives the class of
`± h` in degree `m = n + 1`, with the universal sign `(-1)^m`. -/
theorem cls_toSingleMk_comp_singleδ {p p' p'' n m : ℤ} (hpn : p + n = 0) (hp' : p' + 1 = p)
    (hp'' : p'' + 1 = p') (hnm : 1 + n = m)
    (f : K.X p ⟶ S.X₃) (hf : K.d p' p ≫ f = 0) (f' : K.X p ⟶ S.X₂) (hf' : f' ≫ S.g = f)
    (h : K.X p' ⟶ S.X₁) (hh : h ≫ S.f = K.d p' p ≫ f') :
    ShiftedHom.comp (cls (Cocycle.toSingleMk f hpn p' hp' hf) :
        ShiftedHom (Q.obj K) ((DerivedCategory.singleFunctor C 0).obj S.X₃) n)
      hS.singleδ hnm =
      cls (Cocycle.toSingleMk (((m.negOnePow : ℤˣ) : ℤ) • h) (show p' + m = 0 by omega) p'' hp''
        (by
          have := hS.mono_f
          rw [Preadditive.comp_zsmul]
          have : (K.d p'' p' ≫ h) ≫ S.f = 0 := by
            rw [assoc, hh, ← assoc, HomologicalComplex.d_comp_d, zero_comp]
          rw [(cancel_mono S.f).1 (this.trans zero_comp.symm), zsmul_zero])) := by
  have := hS.mono_f
  have hm : p' + m = 0 := by omega
  have hd : K.d p'' p' ≫ (-(((m.negOnePow : ℤˣ) : ℤ) • h)) = 0 := by
    rw [comp_neg, Preadditive.comp_zsmul, show K.d p'' p' ≫ h = 0 by
      rw [← cancel_mono S.f, assoc, hh, ← assoc, HomologicalComplex.d_comp_d, zero_comp,
        zero_comp], zsmul_zero, neg_zero]
  have key := cls_comp_singleδ hS hnm (Cocycle.toSingleMk f hpn p' hp' hf)
    (Cochain.toSingleMk f' hpn) (by rw [← Cochain.toSingleMk_postcomp, hf']; rfl)
    (Cocycle.toSingleMk (-(((m.negOnePow : ℤˣ) : ℤ) • h)) hm p'' hp'' hd)
    (by
      rw [Cochain.δ_toSingleMk f' hpn m p' hm, Cocycle.toSingleMk_coe,
        ← Cochain.toSingleMk_postcomp, Units.smul_def, ← Cochain.toSingleMk_zsmul',
        ← Cochain.toSingleMk_add, neg_comp, Preadditive.zsmul_comp, hh, add_neg_cancel]
      simp)
  rw [key, ← cls_neg, Cocycle.toSingleMk_neg, neg_neg]

/-! ### The tautological classes of a complex -/

section Tautological

variable (P : CochainComplex C ℤ)

/-- The cokernel `M_p = coker(d : P^{p-1} → P^p)`. -/
abbrev coker (p : ℤ) : C := cokernel (P.d (p - 1) p)

/-- The projection `P^p ⟶ M_p`. -/
abbrev cokerπ (p : ℤ) : P.X p ⟶ coker P p := cokernel.π _

omit [HasDerivedCategory.{w} C] in
/-- The differential into `P^p` followed by the projection `P^p ⟶ M_p` is zero. -/
lemma d_cokerπ {i p : ℤ} (h : i + 1 = p) : P.d i p ≫ cokerπ P p = 0 := by
  obtain rfl : i = p - 1 := by omega
  exact cokernel.condition _

/-- The map `M_{p-1} ⟶ P^p` induced by the differential. -/
abbrev cokerD (p : ℤ) : coker P (p - 1) ⟶ P.X p :=
  cokernel.desc _ (P.d (p - 1) p) (HomologicalComplex.d_comp_d _ _ _ _)

omit [HasDerivedCategory.{w} C] in
/-- The projection `P^{p-1} ⟶ M_{p-1}` followed by `M_{p-1} ⟶ P^p` is the differential. -/
@[reassoc]
lemma cokerπ_cokerD (p : ℤ) : cokerπ P (p - 1) ≫ cokerD P p = P.d (p - 1) p :=
  cokernel.π_desc _ _ _

omit [HasDerivedCategory.{w} C] in
/-- The composite `M_{p-1} ⟶ P^p ⟶ M_p` is zero. -/
@[reassoc]
lemma cokerD_cokerπ (p : ℤ) : cokerD P p ≫ cokerπ P p = 0 := by
  rw [← cancel_epi (cokerπ P (p - 1)), cokerπ_cokerD_assoc, d_cokerπ P (by omega), comp_zero]

/-- The kernel of `P^p ⟶ M_p`. -/
abbrev ker (p : ℤ) : C := kernel (cokerπ P p)

/-- The inclusion of the kernel of `P^p ⟶ M_p`. -/
abbrev kerι (p : ℤ) : ker P p ⟶ P.X p := kernel.ι _

/-- The map `M_{p-1} ⟶ ker(P^p ⟶ M_p)` induced by the differential. -/
abbrev cokerToKer (p : ℤ) : coker P (p - 1) ⟶ ker P p :=
  kernel.lift _ (cokerD P p) (cokerD_cokerπ P p)

omit [HasDerivedCategory.{w} C] in
/-- The map `M_{p-1} ⟶ ker(P^p ⟶ M_p)` followed by the inclusion into `P^p` is the map
`M_{p-1} ⟶ P^p` induced by the differential. -/
@[reassoc (attr := simp)]
lemma cokerToKer_kerι (p : ℤ) : cokerToKer P p ≫ kerι P p = cokerD P p :=
  kernel.lift_ι _ _ _

/-- The short complex `0 → ker → P^p → M_p → 0`. -/
abbrev sc (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (kerι P p) (cokerπ P p) (kernel.condition _)

omit [HasDerivedCategory.{w} C] in
/-- The short complex `0 → ker → P^p → M_p → 0` is short exact. -/
lemma sc_shortExact (p : ℤ) : (sc P p).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  mono_f := by dsimp [sc]; infer_instance
  epi_g := by dsimp [sc]; infer_instance

/-- The tautological class `P ⟶ M_p[n]`, `p + n = 0`. -/
def can (p n : ℤ) (h : p + n = 0) :
    Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj (coker P p))⟦n⟧ :=
  cls (Cocycle.toSingleMk (cokerπ P p) h (p - 1) (by omega) (d_cokerπ P (by omega)))

/-- The tautological class followed by the map induced by `f : M_p ⟶ F` is the class of
`P^p ⟶ M_p ⟶ F`. -/
lemma can_comp_map {F : C} (p n : ℤ) (h : p + n = 0) (f : coker P p ⟶ F) :
    can P p n h ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦n⟧' =
      cls (Cocycle.toSingleMk (cokerπ P p ≫ f) h (p - 1) (by omega)
        (by rw [← assoc, d_cokerπ P (by omega), zero_comp])) := by
  rw [Cocycle.toSingleMk_postcomp, cls_postcomp]
  rfl

/-- If `P` is K-projective, every morphism `P ⟶ F[n]` with `p + n = 0` is the tautological class
`P ⟶ M_p[n]` followed by the map induced by some `f : M_p ⟶ F`. -/
lemma exists_eq_can_comp [P.IsKProjective] {F : C} {n : ℤ}
    (x : Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧) (p : ℤ) (h : p + n = 0) :
    ∃ f : coker P p ⟶ F, x = can P p n h ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦n⟧' := by
  obtain ⟨z, rfl⟩ := cls_surjective (K := P) (L := (CochainComplex.singleFunctor C 0).obj F) x
  obtain ⟨f, hf, rfl⟩ := Cocycle.toSingleMk_surjective z p h (p - 1) (by omega)
  refine ⟨cokernel.desc _ f hf, ?_⟩
  rw [can_comp_map]
  congr 2
  exact (cokernel.π_desc _ _ _).symm

/-- **The connecting morphism of `0 → ker → P^p → M_p → 0` on the tautological class.** -/
lemma can_comp_singleδ (p n m : ℤ) (hn : p + n = 0) (hm : p - 1 + m = 0) (hnm : 1 + n = m) :
    ShiftedHom.comp (can P p n hn :
        ShiftedHom (Q.obj P) ((DerivedCategory.singleFunctor C 0).obj (sc P p).X₃) n)
      (sc_shortExact P p).singleδ hnm =
      can P (p - 1) m hm ≫
        ((DerivedCategory.singleFunctor C 0).map
          ((((m.negOnePow : ℤˣ) : ℤ)) • cokerToKer P p))⟦m⟧' := by
  have hw : (cokerπ P (p - 1) ≫ cokerToKer P p) ≫ (sc P p).f = P.d (p - 1) p ≫ 𝟙 _ := by
    show (cokerπ P (p - 1) ≫ cokerToKer P p) ≫ kerι P p = P.d (p - 1) p ≫ 𝟙 _
    rw [comp_id, assoc, cokerToKer_kerι, cokerπ_cokerD]
  refine (cls_toSingleMk_comp_singleδ (sc_shortExact P p) hn (by omega)
    (show p - 1 - 1 + 1 = p - 1 by omega) hnm (cokerπ P p) (d_cokerπ P (by omega)) (𝟙 _)
    (id_comp _) _ hw).trans ?_
  rw [can_comp_map]
  congr 2
  exact (Preadditive.comp_zsmul _ _ _).symm

end Tautological

/-! ### Realization of a `δ`-compatible natural transformation -/

/-- **Fullness: a natural, `δ`-compatible map of `Ext`-groups out of K-projective complexes is
induced by a morphism.** Let `P` and `P'` be K-projective complexes, the terms of `P'` being
projective, and let `φ` be a family of maps
`Hom_{D}(P, F[n]) → Hom_{D}(P', F[n])`, for `n ∈ ℤ` and `F` in `C`, natural in `F` and
compatible with the connecting morphisms of short exact sequences of `C`. Then
`φ = g^*` for a morphism `g : P' ⟶ P` of the derived category (in fact of complexes). -/
theorem exists_hom_eq_comp_of_isKProjective {P P' : CochainComplex C ℤ} [P.IsKProjective]
    [P'.IsKProjective] (hP' : ∀ i, Projective (P'.X i))
    (φ : ∀ (n : ℤ) (F : C), (Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧) →
      (Q.obj P' ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧))
    (hnat : ∀ (n : ℤ) {F F' : C} (f : F ⟶ F')
      (x : Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧),
      φ n F' (x ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦n⟧') =
        φ n F x ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦n⟧')
    (hδ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n m : ℤ) (hnm : 1 + n = m)
      (x : ShiftedHom (Q.obj P) ((DerivedCategory.singleFunctor C 0).obj S.X₃) n),
      φ m S.X₁ (x.comp hS.singleδ hnm) = ShiftedHom.comp (φ n S.X₃ x) hS.singleδ hnm) :
    ∃ g : P' ⟶ P, ∀ (n : ℤ) (F : C)
      (x : Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧), φ n F x = Q.map g ≫ x := by
  have ha₀ : ∀ p : ℤ, ∃ a : coker P' p ⟶ coker P p,
      φ (-p) _ (can P p (-p) (by omega)) =
        can P' p (-p) (by omega) ≫ ((DerivedCategory.singleFunctor C 0).map a)⟦-p⟧' :=
    fun p ↦ exists_eq_can_comp P' _ p _
  choose a ha₀ using ha₀
  have ha : ∀ (p n : ℤ) (h : p + n = 0), φ n _ (can P p n h) =
      can P' p n h ≫ ((DerivedCategory.singleFunctor C 0).map (a p))⟦n⟧' := by
    intro p n h
    obtain rfl : n = -p := by omega
    exact ha₀ p
  have hb : ∀ p : ℤ, ∃ b : P'.X p ⟶ P.X p, b ≫ cokerπ P p = cokerπ P' p ≫ a p ∧
      P'.d (p - 1) p ≫ b = cokerπ P' (p - 1) ≫ a (p - 1) ≫ cokerD P p := by
    intro p
    have := hP' p
    let ε : ℤ := (((-(p - 1)).negOnePow : ℤˣ) : ℤ)
    have hεε : ε * ε = 1 := by
      simp only [ε, ← Units.val_mul, Int.units_mul_self, Units.val_one]
    let b₀ : P'.X p ⟶ P.X p := Projective.factorThru (cokerπ P' p ≫ a p) (cokerπ P p)
    have hb₀ : b₀ ≫ cokerπ P p = cokerπ P' p ≫ a p := Projective.factorThru_comp _ _
    let u : P'.X (p - 1) ⟶ ker P p := kernel.lift _ (P'.d (p - 1) p ≫ b₀) (by
      rw [assoc, hb₀, ← assoc, d_cokerπ P' (by omega), zero_comp])
    have hu : u ≫ kerι P p = P'.d (p - 1) p ≫ b₀ := kernel.lift_ι _ _ _
    let v : P'.X (p - 1) ⟶ ker P p := cokerπ P' (p - 1) ≫ a (p - 1) ≫ cokerToKer P p
    have hv : v ≫ kerι P p = cokerπ P' (p - 1) ≫ a (p - 1) ≫ cokerD P p := by
      simp only [v, assoc, cokerToKer_kerι]
    have hdu : P'.d (p - 1 - 1) (p - 1) ≫ (ε • u) = 0 := by
      rw [Preadditive.comp_zsmul, ← cancel_mono (kerι P p), Preadditive.zsmul_comp, assoc, hu,
        ← assoc, HomologicalComplex.d_comp_d, zero_comp, zsmul_zero, zero_comp]
    have hf1 : P'.d (p - 1) p ≫ (cokerπ P' p ≫ a p) = 0 := by
      rw [← assoc, d_cokerπ P' (by omega), zero_comp]
    have hdv : P'.d (p - 1 - 1) (p - 1) ≫ (ε • v) = 0 := by
      rw [Preadditive.comp_zsmul, ← assoc, d_cokerπ P' (by omega), zero_comp, zsmul_zero]
    have key : cls (Cocycle.toSingleMk (ε • u) (show p - 1 + -(p - 1) = 0 by omega)
        (p - 1 - 1) (by omega) hdu) =
        cls (Cocycle.toSingleMk (ε • v) (show p - 1 + -(p - 1) = 0 by omega)
          (p - 1 - 1) (by omega) hdv) := by
      have e1 := cls_toSingleMk_comp_singleδ (K := P') (sc_shortExact P p)
        (show p + -p = 0 by omega) (show p - 1 + 1 = p by omega)
        (show p - 1 - 1 + 1 = p - 1 by omega) (show 1 + -p = -(p - 1) by omega)
        (cokerπ P' p ≫ a p) hf1 b₀ hb₀ u hu
      have e2 := (congrArg (φ (-(p - 1)) (ker P p))
        (can_comp_singleδ P p (-p) (-(p - 1)) (by omega) (by omega) (by omega))).symm.trans
        (hδ (sc_shortExact P p) (-p) (-(p - 1)) (by omega) (can P p (-p) (by omega)))
      rw [hnat,
        ha (p - 1) (-(p - 1)) (by omega), ha p (-p) (by omega),
        can_comp_map P' p (-p) (by omega)] at e2
      refine e1.symm.trans (e2.symm.trans ?_)
      rw [assoc, ← Functor.map_comp, ← Functor.map_comp, can_comp_map]
      congr 2
      simp only [v, ε, Preadditive.comp_zsmul]
    rw [cls_eq_cls_iff, ← Cocycle.toSingleMk_sub,
      Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ p (by omega)] at key
    obtain ⟨g', hg'⟩ := key
    refine ⟨b₀ - (ε • g') ≫ kerι P p, ?_, ?_⟩
    · rw [sub_comp, hb₀, assoc, kernel.condition, comp_zero, sub_zero]
    · rw [comp_sub, ← hu, ← assoc, Preadditive.comp_zsmul, hg', ← hv, smul_sub, smul_smul,
        smul_smul, hεε, one_smul, one_smul, sub_comp, sub_sub_cancel]
  choose b hb₁ hb₂ using hb
  let g : P' ⟶ P :=
    { f := b
      comm' := by
        rintro i j (hij : i + 1 = j)
        obtain rfl : i = j - 1 := by omega
        rw [hb₂ j, ← cokerπ_cokerD P j, ← assoc, hb₁, assoc] }
  have hg : ∀ (p n : ℤ) (h : p + n = 0), Q.map g ≫ can P p n h =
      can P' p n h ≫ ((DerivedCategory.singleFunctor C 0).map (a p))⟦n⟧' := by
    intro p n h
    rw [can, ← cls_precomp, ← Cocycle.toSingleMk_precomp, can_comp_map]
    congr 2
    exact hb₁ p
  refine ⟨g, fun n F x ↦ ?_⟩
  obtain ⟨f, rfl⟩ := exists_eq_can_comp P x (-n) (by omega)
  rw [hnat, ha, ← assoc, hg]

/-! ### Detection of isomorphisms by injective objects -/

/-- **Injective objects placed in one degree detect isomorphisms between bounded above objects.**
Let `C` have enough injectives and let `g : X ⟶ Y` be a morphism of `D(C)` between objects with
bounded above cohomology. If `x ↦ g ≫ x` is bijective on morphisms into `I[n]` for every
injective `I` and every `n`, then `g` is an isomorphism. -/
theorem isIso_of_bijective_comp_singleFunctor_injective [EnoughInjectives C]
    {X Y : DerivedCategory C} (g : X ⟶ Y) (a b : ℤ) [X.IsLE a] [Y.IsLE b]
    (h : ∀ (n : ℤ) (I : C), Injective I →
      Function.Bijective (fun x : Y ⟶ ((DerivedCategory.singleFunctor C 0).obj I)⟦n⟧ ↦ g ≫ x)) :
    IsIso g := by
  obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle g
  have hvan : ∀ (n : ℤ) (I : C), Injective I →
      ∀ x : Z ⟶ ((DerivedCategory.singleFunctor C 0).obj I)⟦n⟧, x = 0 := by
    intro n I hI x
    have hgv : g ≫ v = 0 := comp_distTriang_mor_zero₁₂ _ hT
    have h1 : v ≫ x = 0 := (h n I hI).injective (show g ≫ v ≫ x = g ≫ 0 by
      rw [reassoc_of% hgv, zero_comp, comp_zero])
    obtain ⟨y, rfl⟩ := Triangle.yoneda_exact₃ _ hT x h1
    let e : ((DerivedCategory.singleFunctor C 0).obj I)⟦n⟧ ≅
        (((DerivedCategory.singleFunctor C 0).obj I)⟦n - 1⟧)⟦(1 : ℤ)⟧ :=
      (CategoryTheory.shiftFunctorAdd' (DerivedCategory C) (n - 1) 1 n (by omega)).app _
    obtain ⟨y', hy'⟩ := (CategoryTheory.shiftFunctor (DerivedCategory C) (1 : ℤ)).map_surjective
      (y ≫ e.hom)
    obtain ⟨z, hz⟩ := (h (n - 1) I hI).surjective y'
    have hy : y = g⟦(1 : ℤ)⟧' ≫ z⟦(1 : ℤ)⟧' ≫ e.inv := by
      rw [← assoc, ← Functor.map_comp, show g ≫ z = y' from hz, hy', assoc, Iso.hom_inv_id,
        comp_id]
    have hwg : w ≫ g⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
    rw [hy]
    show w ≫ _ = 0
    rw [reassoc_of% hwg, zero_comp]
  have hrot := rot_of_distTriang _ hT
  have : (X⟦(1 : ℤ)⟧).IsLE (a - 1) := TStructure.t.isLE_shift X a 1 (a - 1) (by omega)
  have : Z.IsLE (max a b) := TStructure.t.isLE₂ _ hrot (max a b)
    (TStructure.t.isLE_of_le Y b (max a b) (le_max_right a b))
    (TStructure.t.isLE_of_le (X⟦(1 : ℤ)⟧) (a - 1) (max a b) (by omega))
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  show IsZero Z
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  by_contra hne
  simp only [not_forall] at hne
  have hex : ∃ j : ℕ, ¬ IsZero ((homologyFunctor C (max a b - j)).obj Z) := by
    obtain ⟨i, hi⟩ := hne
    have hi' : i ≤ max a b := by
      by_contra hlt
      exact hi (DerivedCategory.isZero_of_isLE Z (max a b) i (by omega))
    exact ⟨(max a b - i).toNat, by rwa [show max a b - ((max a b - i).toNat : ℤ) = i by omega]⟩
  classical
  let j := Nat.find hex
  let m : ℤ := max a b - j
  have hm : ¬ IsZero ((homologyFunctor C m).obj Z) := Nat.find_spec hex
  have : Z.IsLE m := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    by_cases hi' : max a b < i
    · exact DerivedCategory.isZero_of_isLE Z (max a b) i hi'
    · have := Nat.find_min hex (m := (max a b - i).toNat) (by omega)
      rw [show max a b - ((max a b - i).toNat : ℤ) = i by omega] at this
      simpa using this
  obtain ⟨x, hx⟩ := (bijective_homologyFunctor_shiftMap_of_isLE_of_isGE Z
    ((DerivedCategory.singleFunctor C 0).obj (Injective.under ((homologyFunctor C m).obj Z)))
    m 0 (-m) 0 (by omega) le_rfl).surjective
    (Injective.ι ((homologyFunctor C m).obj Z) ≫
      (singleFunctorCompHomologyFunctorIso C 0).inv.app _)
  dsimp only at hx
  rw [hvan (-m) _ inferInstance x, Functor.shiftMap_zero] at hx
  apply hm
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (Injective.ι ((homologyFunctor C m).obj Z)),
    ← cancel_mono ((singleFunctorCompHomologyFunctorIso C 0).inv.app _), zero_comp, zero_comp,
    id_comp]
  exact hx.symm

/-! ### The `δ`-functor of `Ext` into objects determines a bounded above complex -/

/-- **A bounded above complex of projectives is determined by its `Ext` `δ`-functor.** Let `P`,
`P'` be bounded above complexes of projective objects of an abelian category with enough
injectives, and `φ_n(F) : Hom_{D}(P, F[n]) → Hom_{D}(P', F[n])` maps, for `n ∈ ℤ` and `F` in
`C`, natural in `F`, compatible with the connecting morphisms of short exact sequences, and
bijective when `F` is injective. Then `φ = g^*` for an isomorphism `g : P' ≅ P` of `D(C)`. -/
theorem exists_isIso_eq_comp_of_projective [EnoughInjectives C] {P P' : CochainComplex C ℤ}
    (d d' : ℤ) [P.IsStrictlyLE d] [P'.IsStrictlyLE d'] (hP : ∀ i, Projective (P.X i))
    (hP' : ∀ i, Projective (P'.X i))
    (φ : ∀ (n : ℤ) (F : C), (Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧) →
      (Q.obj P' ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧))
    (hnat : ∀ (n : ℤ) {F F' : C} (f : F ⟶ F')
      (x : Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧),
      φ n F' (x ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦n⟧') =
        φ n F x ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦n⟧')
    (hδ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n m : ℤ) (hnm : 1 + n = m)
      (x : ShiftedHom (Q.obj P) ((DerivedCategory.singleFunctor C 0).obj S.X₃) n),
      φ m S.X₁ (x.comp hS.singleδ hnm) = ShiftedHom.comp (φ n S.X₃ x) hS.singleδ hnm)
    (hinj : ∀ (n : ℤ) (I : C), Injective I → Function.Bijective (φ n I)) :
    ∃ g : Q.obj P' ⟶ Q.obj P, IsIso g ∧ ∀ (n : ℤ) (F : C)
      (x : Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧), φ n F x = g ≫ x := by
  have : ∀ i, Projective (P.X i) := hP
  have : ∀ i, Projective (P'.X i) := hP'
  have : P.IsKProjective := isKProjective_of_projective P d
  have : P'.IsKProjective := isKProjective_of_projective P' d'
  obtain ⟨g, hg⟩ := exists_hom_eq_comp_of_isKProjective hP' φ hnat hδ
  refine ⟨Q.map g, isIso_of_bijective_comp_singleFunctor_injective (Q.map g) d' d
    (fun n I hI ↦ ?_), hg⟩
  convert hinj n I hI using 1
  exact funext fun x ↦ (hg n I x).symm

/-- **[Stacks, Tag 0DJV], module-level uniqueness, the derived-category input.** Let `C` be an
abelian category with enough projectives and enough injectives, and let `L`, `L'` be objects of
`D(C)` with bounded above cohomology. Let
`φ_n(F) : Hom_{D(C)}(L, F[n]) → Hom_{D(C)}(L', F[n])`, for `n ∈ ℤ` and `F` in `C`, be maps that
are natural in `F`, compatible with the connecting morphisms `F₃ ⟶ F₁[1]` of short exact
sequences `0 → F₁ → F₂ → F₃ → 0` of `C`, and bijective when `F` is injective (for instance, the
maps of an isomorphism of `δ`-functors `Ext^*(L, -) ≅ Ext^*(L', -)` on `C`). Then there is an
isomorphism `g : L' ⟶ L` with `φ_n(F)(x) = g ≫ x` for all `n`, `F` and `x`. -/
theorem exists_isIso_eq_comp_of_isLE [EnoughProjectives C] [EnoughInjectives C]
    (L L' : DerivedCategory C) (a a' : ℤ) [L.IsLE a] [L'.IsLE a']
    (φ : ∀ (n : ℤ) (F : C), (L ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧) →
      (L' ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧))
    (hnat : ∀ (n : ℤ) {F F' : C} (f : F ⟶ F')
      (x : L ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧),
      φ n F' (x ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦n⟧') =
        φ n F x ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦n⟧')
    (hδ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n m : ℤ) (hnm : 1 + n = m)
      (x : ShiftedHom L ((DerivedCategory.singleFunctor C 0).obj S.X₃) n),
      φ m S.X₁ (x.comp hS.singleδ hnm) = ShiftedHom.comp (φ n S.X₃ x) hS.singleδ hnm)
    (hinj : ∀ (n : ℤ) (I : C), Injective I → Function.Bijective (φ n I)) :
    ∃ g : L' ⟶ L, IsIso g ∧ ∀ (n : ℤ) (F : C)
      (x : L ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧), φ n F x = g ≫ x := by
  let W : ObjectProperty C := fun X ↦ Projective X
  have : W.ContainsZero := ⟨0, isZero_zero C, (inferInstance : Projective (0 : C))⟩
  have hW : ∀ X : C, ∃ (Y : C) (_ : W Y) (p : Y ⟶ X), Epi p :=
    fun X ↦ ⟨Projective.over X, (inferInstance : Projective _), Projective.π X, inferInstance⟩
  have hrep : ∀ (M : DerivedCategory C) (b : ℤ) [M.IsLE b], ∃ P : CochainComplex C ℤ,
      (∀ i, Projective (P.X i)) ∧ P.IsStrictlyLE b ∧ Nonempty (Q.obj P ≅ M) := by
    intro M b _
    obtain ⟨K, ⟨e⟩⟩ : ∃ K : CochainComplex C ℤ, Nonempty (Q.obj K ≅ M) :=
      ⟨Q.objPreimage M, ⟨Q.objObjPreimageIso M⟩⟩
    have : K.IsLE b := by
      rw [CochainComplex.isLE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact (DerivedCategory.isZero_of_isLE M b i hi).of_iso
        (((homologyFunctorFactors C i).app K).symm ≪≫ (homologyFunctor C i).mapIso e)
    obtain ⟨P, π, hπ, hP, hPb⟩ := (CochainComplex.exists_quasiIso_prop W hW b).2 K
    exact ⟨P, hP, hPb, ⟨asIso (Q.map π) ≪≫ e⟩⟩
  obtain ⟨P, hP, hPa, ⟨E⟩⟩ := hrep L a
  obtain ⟨P', hP', hPa', ⟨E'⟩⟩ := hrep L' a'
  let ψ : ∀ (n : ℤ) (F : C), (Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧) →
      (Q.obj P' ⟶ ((DerivedCategory.singleFunctor C 0).obj F)⟦n⟧) :=
    fun n F x ↦ E'.hom ≫ φ n F (E.inv ≫ x)
  have bij₁ : ∀ {T : DerivedCategory C}, Function.Bijective (fun y : L' ⟶ T ↦ E'.hom ≫ y) :=
    fun {T} ↦ ⟨fun y y' h ↦ (cancel_epi E'.hom).1 h, fun z ↦ ⟨E'.inv ≫ z, by simp⟩⟩
  have bij₂ : ∀ {T : DerivedCategory C}, Function.Bijective (fun y : Q.obj P ⟶ T ↦ E.inv ≫ y) :=
    fun {T} ↦ ⟨fun y y' h ↦ (cancel_epi E.inv).1 h, fun z ↦ ⟨E.hom ≫ z, by simp⟩⟩
  obtain ⟨g₀, hg₀, hψ⟩ := exists_isIso_eq_comp_of_projective (P := P) (P' := P') a a' hP hP' ψ
    (fun n F F' f x ↦ by
      simp only [ψ]
      rw [← assoc, hnat, assoc])
    (fun hS n m hnm x ↦ by
      show E'.hom ≫ φ m _ (E.inv ≫ ShiftedHom.comp x hS.singleδ hnm) = _
      rw [show E.inv ≫ ShiftedHom.comp x hS.singleδ hnm =
        ShiftedHom.comp (E.inv ≫ x) hS.singleδ hnm by simp [ShiftedHom.comp], hδ]
      simp [ShiftedHom.comp, ψ])
    (fun n I hI ↦ bij₁.comp ((hinj n I hI).comp bij₂))
  refine ⟨E'.inv ≫ g₀ ≫ E.hom, inferInstance, fun n F x ↦ ?_⟩
  have := hψ n F (E.hom ≫ x)
  simp only [ψ, Iso.inv_hom_id_assoc] at this
  rw [assoc, assoc, ← this, Iso.inv_hom_id_assoc]

/-- **The `δ`-functor of `Ext` into modules determines a bounded above complex of modules.** For
a ring `A` and objects `L`, `L'` of `D(A)` (at any model of the derived category) with bounded
above cohomology, maps `φ_n(F) : Hom_{D(A)}(L, F[n]) → Hom_{D(A)}(L', F[n])` for `n ∈ ℤ` and
`F` an `A`-module, natural in `F`, compatible with the connecting morphisms of short exact
sequences of modules and bijective on injective modules are composition with an isomorphism
`g : L' ⟶ L`. -/
theorem exists_isIso_eq_comp_of_isLE_moduleCat {A : Type u} [Ring A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (L L' : DerivedCategory (ModuleCat.{u} A)) (a a' : ℤ) [L.IsLE a] [L'.IsLE a']
    (φ : ∀ (n : ℤ) (F : ModuleCat.{u} A),
      (L ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj F)⟦n⟧) →
        (L' ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj F)⟦n⟧))
    (hnat : ∀ (n : ℤ) {F F' : ModuleCat.{u} A} (f : F ⟶ F')
      (x : L ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj F)⟦n⟧),
      φ n F' (x ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f)⟦n⟧') =
        φ n F x ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f)⟦n⟧')
    (hδ : ∀ {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n m : ℤ) (hnm : 1 + n = m)
      (x : ShiftedHom L ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj S.X₃) n),
      φ m S.X₁ (x.comp hS.singleδ hnm) = ShiftedHom.comp (φ n S.X₃ x) hS.singleδ hnm)
    (hinj : ∀ (n : ℤ) (I : ModuleCat.{u} A), Injective I → Function.Bijective (φ n I)) :
    ∃ g : L' ⟶ L, IsIso g ∧ ∀ (n : ℤ) (F : ModuleCat.{u} A)
      (x : L ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj F)⟦n⟧),
        φ n F x = g ≫ x :=
  exists_isIso_eq_comp_of_isLE L L' a a' φ hnat hδ hinj

end Stacks.ExtDeltaFunctorRealization
