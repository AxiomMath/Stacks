module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ClosedImmersionIdealSheaves

/-!
# The scheme theoretic union of two closed subschemes is a pushout

Let `I` and `J` be quasi-coherent sheaves of ideals on a scheme `S`. The subscheme cut out by
`I ⊓ J` is the scheme theoretic union of the subschemes cut out by `I` and by `J`, and the
subscheme cut out by `I ⊔ J` is their scheme theoretic intersection. The square formed by the
four canonical inclusions is a pushout square: a pair of morphisms out of the two subschemes
agreeing on their intersection glues to a unique morphism out of their union.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isPushout_subscheme_inf`: the canonical square is a
  pushout square.

## Implementation notes

The existence half of the universal property is local on the target and on the ambient scheme,
and the reduction is in two steps. Over an affine ambient scheme with affine target the two
morphisms are a pair of ring maps out of `Γ(S, ⊤) ⧸ I` and `Γ(S, ⊤) ⧸ J` agreeing on
`Γ(S, ⊤) ⧸ (I ⊔ J)`, so they are a single ring map out of `Γ(S, ⊤) ⧸ (I ⊓ J)` by the
cartesian square of quotient rings; that square is `quotientInfSquare_isPullback`. The general
affine-target case follows because a morphism out of the union is determined by its underlying
continuous map together with its restrictions to the two pieces, and the underlying map is built
from the two closed covers by `continuous_of_closed_cover`. The global case then glues over the
open cover of the union by the preimages of affine opens of the target, which is
`union_exists_lift`.

Uniqueness is `union_hom_ext`: the two inclusions are jointly surjective on points and jointly
epimorphic, so a morphism out of the union is determined by its two restrictions.

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {R : Type*} [CommRing R]

private def quotientInfToI (I J : Ideal R) : R ⧸ (I ⊓ J) →+* R ⧸ I :=
  Ideal.quotientMap I (RingHom.id R) (by simp)
private def quotientInfToJ (I J : Ideal R) : R ⧸ (I ⊓ J) →+* R ⧸ J :=
  Ideal.quotientMap J (RingHom.id R) (by simp)
private def quotientIToSup (I J : Ideal R) : R ⧸ I →+* R ⧸ (I ⊔ J) :=
  Ideal.quotientMap (I ⊔ J) (RingHom.id R) (by simp)
private def quotientJToSup (I J : Ideal R) : R ⧸ J →+* R ⧸ (I ⊔ J) :=
  Ideal.quotientMap (I ⊔ J) (RingHom.id R) (by simp)

private theorem exists_quotientInf_lift_pair (I J : Ideal R) (x : R ⧸ I) (y : R ⧸ J)
    (h : quotientIToSup I J x = quotientJToSup I J y) :
    ∃ z : R ⧸ (I ⊓ J), quotientInfToI I J z = x ∧ quotientInfToJ I J z = y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hab : Ideal.Quotient.mk (I ⊔ J) a = Ideal.Quotient.mk (I ⊔ J) b := by
    simpa only [quotientIToSup, quotientJToSup, Ideal.quotientMap_mk, RingHom.id_apply] using h
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp (Ideal.Quotient.eq.mp hab)
  refine ⟨Ideal.Quotient.mk (I ⊓ J) (a - i), ?_, ?_⟩
  · simp only [quotientInfToI, Ideal.quotientMap_mk, RingHom.id_apply]
    apply Ideal.Quotient.eq.mpr
    show (a - i) - a ∈ I
    rw [show (a - i) - a = -i by ring]
    simpa using I.neg_mem hi
  · simp only [quotientInfToJ, Ideal.quotientMap_mk, RingHom.id_apply]
    apply Ideal.Quotient.eq.mpr
    show (a - i) - b ∈ J
    rwa [show a - i - b = j by linear_combination -hij]

private theorem existsUnique_function_of_cover
    {A B X Y : Type*} (a : A → X) (b : B → X) (f : A → Y) (g : B → Y)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hcover : Set.range a ∪ Set.range b = Set.univ)
    (hcompat : ∀ x y, a x = b y → f x = g y) :
    ∃! h : X → Y, (∀ x, h (a x) = f x) ∧ (∀ y, h (b y) = g y) := by
  classical
  have memCover (z : X) : z ∈ Set.range a ∪ Set.range b := by
    rw [hcover]
    exact Set.mem_univ z
  have memB (z : X) (hz : z ∉ Set.range a) : z ∈ Set.range b := (memCover z).resolve_left hz
  let h : X → Y := fun z => if hz : z ∈ Set.range a then f (Classical.choose hz) else
    g (Classical.choose (memB z hz))
  have hA (x : A) : h (a x) = f x := by
    have hx : a x ∈ Set.range a := ⟨x, rfl⟩
    have hxchoose : Classical.choose hx = x := ha (Classical.choose_spec hx)
    show (if hz : a x ∈ Set.range a then f (Classical.choose hz) else _) = f x
    rw [dite_eq_left hx, hxchoose]
  have hB (y : B) : h (b y) = g y := by
    dsimp [h]
    by_cases hz : b y ∈ Set.range a
    · rw [dite_eq_left hz]
      exact hcompat (Classical.choose hz) y (Classical.choose_spec hz)
    · rw [dite_eq_right hz]
      exact congrArg g (hb (Classical.choose_spec (memB (b y) hz)))
  refine ⟨h, ⟨hA, hB⟩, ?_⟩
  intro k hk
  funext z
  rcases memCover z with ⟨x, hx⟩ | ⟨y, hy⟩
  · calc
      k z = k (a x) := congrArg k hx.symm
      _ = f x := hk.1 x
      _ = h (a x) := (hA x).symm
      _ = h z := congrArg h hx
  · calc
      k z = k (b y) := congrArg k hy.symm
      _ = g y := hk.2 y
      _ = h (b y) := (hB y).symm
      _ = h z := congrArg h hy

private theorem continuous_of_closed_cover
    {A B X Y : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : A → X) (b : B → X) (f : A → Y) (g : B → Y) (h : X → Y)
    (ha : Topology.IsClosedEmbedding a) (hb : Topology.IsClosedEmbedding b)
    (hcover : Set.range a ∪ Set.range b = Set.univ)
    (hf : Continuous f) (hg : Continuous g)
    (hfa : h ∘ a = f) (hgb : h ∘ b = g) :
    Continuous h := by
  have hca : ContinuousOn h (Set.range a) := by
    rw [← Set.image_univ, ha.isInducing.continuousOn_image_iff, hfa]
    exact hf.continuousOn
  have hcb : ContinuousOn h (Set.range b) := by
    rw [← Set.image_univ, hb.isInducing.continuousOn_image_iff, hgb]
    exact hg.continuousOn
  have hcu : ContinuousOn h (Set.range a ∪ Set.range b) :=
    hca.union_of_isClosed hcb ha.isClosed_range hb.isClosed_range
  rwa [hcover, continuousOn_univ] at hcu

private noncomputable def quotientInfLift (I J : Ideal R) (x : R ⧸ I) (y : R ⧸ J)
    (h : quotientIToSup I J x = quotientJToSup I J y) : R ⧸ (I ⊓ J) :=
  Classical.choose (exists_quotientInf_lift_pair I J x y h)
private theorem quotientInfLift_fst (I J : Ideal R) (x : R ⧸ I) (y : R ⧸ J)
    (h : quotientIToSup I J x = quotientJToSup I J y) :
    quotientInfToI I J (quotientInfLift I J x y h) = x :=
  (Classical.choose_spec (exists_quotientInf_lift_pair I J x y h)).1
private theorem quotientInfLift_snd (I J : Ideal R) (x : R ⧸ I) (y : R ⧸ J)
    (h : quotientIToSup I J x = quotientJToSup I J y) :
    quotientInfToJ I J (quotientInfLift I J x y h) = y :=
  (Classical.choose_spec (exists_quotientInf_lift_pair I J x y h)).2

private theorem quotientInfPair_injective (I J : Ideal R) :
    Function.Injective (fun z : R ⧸ (I ⊓ J) => (quotientInfToI I J z, quotientInfToJ I J z)) := by
  intro x y h
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hI : a - b ∈ I := by
    apply (Ideal.Quotient.eq).mp
    simpa only [quotientInfToI, Ideal.quotientMap_mk, RingHom.id_apply] using congrArg Prod.fst h
  have hJ : a - b ∈ J := by
    apply (Ideal.Quotient.eq).mp
    simpa only [quotientInfToJ, Ideal.quotientMap_mk, RingHom.id_apply] using congrArg Prod.snd h
  exact Ideal.Quotient.eq.mpr (Ideal.mem_inf.mpr ⟨hI, hJ⟩)

private theorem quotientInfSquare_isPullback (I J : Ideal R) :
    IsPullback
      (CommRingCat.ofHom (quotientInfToI I J))
      (CommRingCat.ofHom (quotientInfToJ I J))
      (CommRingCat.ofHom (quotientIToSup I J))
      (CommRingCat.ofHom (quotientJToSup I J)) := by
  have w : (quotientIToSup I J).comp (quotientInfToI I J) =
      (quotientJToSup I J).comp (quotientInfToJ I J) := by
    ext z
    simp [quotientInfToI, quotientInfToJ, quotientIToSup, quotientJToSup,
      Ideal.quotientMap_mk, RingHom.id_apply]
  have compatible (s : PullbackCone (CommRingCat.ofHom (quotientIToSup I J))
      (CommRingCat.ofHom (quotientJToSup I J))) (t : s.pt) :
      quotientIToSup I J (s.fst.hom t) = quotientJToSup I J (s.snd.hom t) :=
    congrArg (fun f : s.pt ⟶ CommRingCat.of (R ⧸ (I ⊔ J)) => f.hom t) s.condition
  let lift (s : PullbackCone (CommRingCat.ofHom (quotientIToSup I J))
      (CommRingCat.ofHom (quotientJToSup I J))) :
      CommRingCat.of s.pt ⟶ CommRingCat.of (R ⧸ (I ⊓ J)) := by
    let φ : s.pt →+* R ⧸ (I ⊓ J) := {
        toFun := fun t => quotientInfLift I J (s.fst.hom t) (s.snd.hom t) (compatible s t)
        map_one' := by
          apply quotientInfPair_injective I J
          apply Prod.ext <;> simp [quotientInfLift_fst, quotientInfLift_snd]
        map_mul' := by
          intro x y
          apply quotientInfPair_injective I J
          apply Prod.ext <;> simp [quotientInfLift_fst, quotientInfLift_snd]
        map_zero' := by
          apply quotientInfPair_injective I J
          apply Prod.ext <;> simp [quotientInfLift_fst, quotientInfLift_snd]
        map_add' := by
          intro x y
          apply quotientInfPair_injective I J
          apply Prod.ext <;> simp [quotientInfLift_fst, quotientInfLift_snd]
      }
    exact CommRingCat.ofHom φ
  have fac₁ (s : PullbackCone (CommRingCat.ofHom (quotientIToSup I J))
      (CommRingCat.ofHom (quotientJToSup I J))) :
      lift s ≫ CommRingCat.ofHom (quotientInfToI I J) = s.fst := by
    apply CommRingCat.hom_ext
    ext t
    exact quotientInfLift_fst I J _ _ (compatible s t)
  have fac₂ (s : PullbackCone (CommRingCat.ofHom (quotientIToSup I J))
      (CommRingCat.ofHom (quotientJToSup I J))) :
      lift s ≫ CommRingCat.ofHom (quotientInfToJ I J) = s.snd := by
    apply CommRingCat.hom_ext
    ext t
    exact quotientInfLift_snd I J _ _ (compatible s t)
  refine IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk (CommRingCat.hom_ext w) lift fac₁ fac₂ fun s m hm₁ hm₂ => ?_)
  apply CommRingCat.hom_ext
  ext t
  apply quotientInfPair_injective I J
  apply Prod.ext
  · exact (congrArg (fun f : s.pt ⟶ CommRingCat.of (R ⧸ I) => f.hom t) hm₁).trans
      (congrArg (fun f : s.pt ⟶ CommRingCat.of (R ⧸ I) => f.hom t) (fac₁ s)).symm
  · exact (congrArg (fun f : s.pt ⟶ CommRingCat.of (R ⧸ J) => f.hom t) hm₂).trans
      (congrArg (fun f : s.pt ⟶ CommRingCat.of (R ⧸ J) => f.hom t) (fac₂ s)).symm


private noncomputable def topSubschemeIso {S : Scheme.{u}} [IsAffine S]
    (I : S.IdealSheafData) :
    Γ(I.subscheme, ⊤) ≅ CommRingCat.of
      (Γ(S, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top S⟩) :=
  I.subschemeObjIso ⟨⊤, isAffineOpen_top S⟩

private theorem topSubschemeRestriction_compat {S : Scheme.{u}} [IsAffine S]
    {I J : S.IdealSheafData} (h : I ≤ J) :
    (topSubschemeIso I).inv ≫ (Scheme.IdealSheafData.inclusion h).appTop ≫
        (topSubschemeIso J).hom =
      CommRingCat.ofHom (Ideal.quotientMap
        (J.ideal ⟨⊤, isAffineOpen_top S⟩) (RingHom.id (Γ(S, ⊤))) (by
          simpa using h ⟨⊤, isAffineOpen_top S⟩)) := by
  let U : S.affineOpens := ⟨⊤, isAffineOpen_top S⟩
  let qI : Γ(S, ⊤) ⟶ CommRingCat.of (Γ(S, ⊤) ⧸ I.ideal U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  let qJ : Γ(S, ⊤) ⟶ CommRingCat.of (Γ(S, ⊤) ⧸ J.ideal U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U))
  let q : CommRingCat.of (Γ(S, ⊤) ⧸ I.ideal U) ⟶
      CommRingCat.of (Γ(S, ⊤) ⧸ J.ideal U) :=
    CommRingCat.ofHom (Ideal.quotientMap (J.ideal U) (RingHom.id (Γ(S, ⊤))) (by
      simpa using h U))
  have : Epi qI := ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
  have hIapp : I.subschemeι.appTop = qI ≫ (topSubschemeIso I).inv := by
    show I.subschemeι.app (⊤ : S.Opens) = _
    simpa [qI, topSubschemeIso, U] using I.subschemeι_app U
  have hJapp : J.subschemeι.appTop = qJ ≫ (topSubschemeIso J).inv := by
    show J.subschemeι.app (⊤ : S.Opens) = _
    simpa [qJ, topSubschemeIso, U] using J.subschemeι_app U
  apply (cancel_epi qI).mp
  calc
    qI ≫ (topSubschemeIso I).inv ≫ (Scheme.IdealSheafData.inclusion h).appTop ≫
        (topSubschemeIso J).hom =
      I.subschemeι.appTop ≫ (Scheme.IdealSheafData.inclusion h).appTop ≫
        (topSubschemeIso J).hom := by simp only [hIapp, Category.assoc]
    _ = J.subschemeι.appTop ≫ (topSubschemeIso J).hom := by
      rw [← Category.assoc, ← Scheme.Hom.comp_appTop, Scheme.IdealSheafData.inclusion_subschemeι]
    _ = qJ := by
      rw [hJapp]
      simp
    _ = qI ≫ q := by
      apply CommRingCat.hom_ext
      simp [qI, qJ, q, U, Ideal.quotientMap_comp_mk]

private theorem topGammaUnionSquare_isPullback {S : Scheme.{u}} [IsAffine S]
    (I J : S.IdealSheafData) :
    IsPullback
      (CommRingCat.ofHom
        (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left).appTop.hom)
      (CommRingCat.ofHom
        (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right).appTop.hom)
      (CommRingCat.ofHom
        (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left).appTop.hom)
      (CommRingCat.ofHom
        (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right).appTop.hom) := by
  let eU := topSubschemeIso (I ⊓ J)
  let eI := topSubschemeIso I
  let eJ := topSubschemeIso J
  let eP := topSubschemeIso (I ⊔ J)
  let fI := Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left
  let fJ := Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right
  let gI := Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left
  let gJ := Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right
  have hcompatI : eU.inv ≫ fI.appTop ≫ eI.hom = CommRingCat.ofHom (quotientInfToI
      (I.ideal ⟨⊤, isAffineOpen_top S⟩) (J.ideal ⟨⊤, isAffineOpen_top S⟩)) :=
    topSubschemeRestriction_compat (S := S) (I := I ⊓ J) (J := I) inf_le_left
  have hcompatJ : eU.inv ≫ fJ.appTop ≫ eJ.hom = CommRingCat.ofHom (quotientInfToJ
      (I.ideal ⟨⊤, isAffineOpen_top S⟩) (J.ideal ⟨⊤, isAffineOpen_top S⟩)) :=
    topSubschemeRestriction_compat (S := S) (I := I ⊓ J) (J := J) inf_le_right
  have hcompatPI : eI.inv ≫ gI.appTop ≫ eP.hom = CommRingCat.ofHom (quotientIToSup
      (I.ideal ⟨⊤, isAffineOpen_top S⟩) (J.ideal ⟨⊤, isAffineOpen_top S⟩)) :=
    topSubschemeRestriction_compat (S := S) (I := I) (J := I ⊔ J) le_sup_left
  have hcompatPJ : eJ.inv ≫ gJ.appTop ≫ eP.hom = CommRingCat.ofHom (quotientJToSup
      (I.ideal ⟨⊤, isAffineOpen_top S⟩) (J.ideal ⟨⊤, isAffineOpen_top S⟩)) :=
    topSubschemeRestriction_compat (S := S) (I := J) (J := I ⊔ J) le_sup_right
  have cI : eU.hom ≫ CommRingCat.ofHom (quotientInfToI
      (I.ideal ⟨⊤, isAffineOpen_top S⟩) (J.ideal ⟨⊤, isAffineOpen_top S⟩)) =
      CommRingCat.ofHom fI.appTop.hom ≫ eI.hom := by
    rw [← hcompatI]
    simp
  have cJ : eU.hom ≫ CommRingCat.ofHom (quotientInfToJ
      (I.ideal ⟨⊤, isAffineOpen_top S⟩) (J.ideal ⟨⊤, isAffineOpen_top S⟩)) =
      CommRingCat.ofHom fJ.appTop.hom ≫ eJ.hom := by
    rw [← hcompatJ]
    simp
  have cPI : eI.hom ≫ CommRingCat.ofHom (quotientIToSup
      (I.ideal ⟨⊤, isAffineOpen_top S⟩) (J.ideal ⟨⊤, isAffineOpen_top S⟩)) =
      CommRingCat.ofHom gI.appTop.hom ≫ eP.hom := by
    calc
      _ = eI.hom ≫ (eI.inv ≫ gI.appTop ≫ eP.hom) := by rw [← hcompatPI]; simp
      _ = gI.appTop ≫ eP.hom := by simp
  have cPJ : eJ.hom ≫ CommRingCat.ofHom (quotientJToSup
      (I.ideal ⟨⊤, isAffineOpen_top S⟩) (J.ideal ⟨⊤, isAffineOpen_top S⟩)) =
      CommRingCat.ofHom gJ.appTop.hom ≫ eP.hom := by
    calc
      _ = eJ.hom ≫ (eJ.inv ≫ gJ.appTop ≫ eP.hom) := by rw [← hcompatPJ]; simp
      _ = gJ.appTop ≫ eP.hom := by simp
  exact IsPullback.of_iso' (quotientInfSquare_isPullback
      (I.ideal ⟨⊤, isAffineOpen_top S⟩) (J.ideal ⟨⊤, isAffineOpen_top S⟩))
    eU eI eJ eP cI cJ cPI cPJ

private theorem affineTarget_lift {S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (I J : S.IdealSheafData)
    (f : I.subscheme ⟶ T) (g : J.subscheme ⟶ T)
    (hcompat : (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left) ≫ f =
      (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) ≫ g) :
    ∃ k : (I ⊓ J).subscheme ⟶ T,
      (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left) ≫ k = f ∧
      (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right) ≫ k = g := by
  have _ : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have _ : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  have _ : IsAffine (I ⊓ J).subscheme := isAffine_of_isAffineHom (I ⊓ J).subschemeι
  have _ : IsAffine (I ⊔ J).subscheme := isAffine_of_isAffineHom (I ⊔ J).subschemeι
  have hring := topGammaUnionSquare_isPullback I J
  let uI := Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left
  let uJ := Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right
  let iP := Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left
  let jP := Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right
  have w : CommRingCat.ofHom f.appTop.hom ≫ CommRingCat.ofHom iP.appTop.hom =
      CommRingCat.ofHom g.appTop.hom ≫ CommRingCat.ofHom jP.appTop.hom := by
    have hh := congrArg Scheme.Hom.appTop hcompat
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hh
    exact congrArg (fun q => CommRingCat.ofHom q.hom) hh
  let φ : CommRingCat.of Γ(T, ⊤) ⟶ CommRingCat.of Γ((I ⊓ J).subscheme, ⊤) :=
    hring.lift (CommRingCat.ofHom f.appTop.hom) (CommRingCat.ofHom g.appTop.hom) w
  have hφI : φ ≫ CommRingCat.ofHom uI.appTop.hom = CommRingCat.ofHom f.appTop.hom :=
    hring.lift_fst _ _ w
  have hφJ : φ ≫ CommRingCat.ofHom uJ.appTop.hom = CommRingCat.ofHom g.appTop.hom :=
    hring.lift_snd _ _ w
  let k : (I ⊓ J).subscheme ⟶ T :=
    (I ⊓ J).subscheme.isoSpec.hom ≫ Spec.map φ ≫ T.isoSpec.inv
  have key {A : Scheme.{u}} [IsAffine A] (u : A ⟶ (I ⊓ J).subscheme) (h : A ⟶ T)
      (hφ : φ ≫ CommRingCat.ofHom u.appTop.hom = CommRingCat.ofHom h.appTop.hom) :
      u ≫ k = h := by
    have hSpec : Spec.map u.appTop ≫ Spec.map φ = Spec.map h.appTop := by
      rw [← Spec.map_comp]
      exact congrArg Spec.map hφ
    apply (cancel_mono T.isoSpec.hom).mp
    calc
      u ≫ k ≫ T.isoSpec.hom = u ≫ ((I ⊓ J).subscheme.isoSpec.hom ≫ Spec.map φ) := by
        dsimp [k]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = A.isoSpec.hom ≫ Spec.map u.appTop ≫ Spec.map φ := by
        rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality u, Category.assoc]
      _ = h ≫ T.isoSpec.hom := by
        rw [hSpec]
        exact Scheme.isoSpec_hom_naturality h
  exact ⟨k, key uI f hφI, key uJ g hφJ⟩

private theorem affineTarget_existsUnique {S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (I J : S.IdealSheafData) :
    ∀ (f : I.subscheme ⟶ T) (g : J.subscheme ⟶ T)
      (_h : (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left) ≫ f =
        (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) ≫ g),
      ∃! k : (I ⊓ J).subscheme ⟶ T,
        (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left) ≫ k = f ∧
        (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right) ≫ k = g := by
  intro f g h
  have _ : IsAffine (I ⊓ J).subscheme := isAffine_of_isAffineHom (I ⊓ J).subschemeι
  have hring := topGammaUnionSquare_isPullback I J
  obtain ⟨k, hk₁, hk₂⟩ := affineTarget_lift I J f g h
  refine ⟨k, ⟨hk₁, hk₂⟩, ?_⟩
  intro k' hk'
  apply (cancel_mono T.isoSpec.hom).mp
  have hmaps : CommRingCat.ofHom k'.appTop.hom = CommRingCat.ofHom k.appTop.hom := by
    apply hring.hom_ext
    · have h₁ := congrArg Scheme.Hom.appTop hk₁
      have h₁' := congrArg Scheme.Hom.appTop hk'.1
      rw [Scheme.Hom.comp_appTop] at h₁ h₁'
      simpa only [← CommRingCat.ofHom_comp] using
        congrArg (fun z => CommRingCat.ofHom z.hom) (h₁'.trans h₁.symm)
    · have h₂ := congrArg Scheme.Hom.appTop hk₂
      have h₂' := congrArg Scheme.Hom.appTop hk'.2
      rw [Scheme.Hom.comp_appTop] at h₂ h₂'
      simpa only [← CommRingCat.ofHom_comp] using
        congrArg (fun z => CommRingCat.ofHom z.hom) (h₂'.trans h₂.symm)
  have hSpec : Spec.map k'.appTop = Spec.map k.appTop := by
    simpa only [CommRingCat.ofHom_hom] using
      (congrArg (fun q => Spec.map q) hmaps)
  calc
    k' ≫ T.isoSpec.hom = (I ⊓ J).subscheme.isoSpec.hom ≫ Spec.map k'.appTop :=
      (Scheme.isoSpec_hom_naturality k').symm
    _ = (I ⊓ J).subscheme.isoSpec.hom ≫
        Spec.map k.appTop := by rw [hSpec]
    _ = k ≫ T.isoSpec.hom := Scheme.isoSpec_hom_naturality k

private theorem factors_through_affineOpen {X T : Scheme.{u}} (U : T.affineOpens)
    (f : X ⟶ T) (h : ∀ x, f x ∈ (U : T.Opens)) :
    ∃ g : X ⟶ U.1.toScheme, g ≫ U.1.ι = f :=
  ⟨IsOpenImmersion.lift U.1.ι f (by simpa [Set.range_subset_iff] using h),
    IsOpenImmersion.lift_fac _ _ _⟩

private theorem support_inf_eq_sup {S : Scheme.{u}} (I J : S.IdealSheafData) :
    (I ⊓ J).support = I.support ⊔ J.support := by
  apply le_antisymm
  · rw [← Scheme.IdealSheafData.support_mul]
    apply Scheme.IdealSheafData.support_antitone
    apply le_inf
    · intro U
      show I.ideal U * J.ideal U ≤ I.ideal U
      exact Ideal.mul_le_left
    · intro U
      show I.ideal U * J.ideal U ≤ J.ideal U
      exact Ideal.mul_le_right
  · exact sup_le (Scheme.IdealSheafData.support_antitone inf_le_left)
      (Scheme.IdealSheafData.support_antitone inf_le_right)

/-- Every point of `I ⊓ J` comes from `I` or from `J`. -/
private theorem exists_inclusion_eq_or {S : Scheme.{u}} (I J : S.IdealSheafData)
    (x : (I ⊓ J).subscheme) :
    (∃ y, Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left y = x) ∨
      ∃ y, Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right y = x := by
    have key {K : S.IdealSheafData} (h : I ⊓ J ≤ K)
        (hx : (I ⊓ J).subschemeι x ∈ (K.support : Set S)) :
        ∃ y, Scheme.IdealSheafData.inclusion h y = x := by
      obtain ⟨y, hy⟩ : (I ⊓ J).subschemeι x ∈ Set.range K.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact hx
      refine ⟨y, (IsClosedImmersion.isClosedEmbedding (I ⊓ J).subschemeι).injective ?_⟩
      simpa only [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι] using hy
    have hx : (I ⊓ J).subschemeι x ∈ ((I ⊓ J).support : Set S) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩
    rw [support_inf_eq_sup] at hx
    rcases hx with hx | hx
    · exact Or.inl (key _ hx)
    · exact Or.inr (key _ hx)

private theorem affineOpenTarget_existsUnique {S T : Scheme.{u}} [IsAffine S]
    (I J : S.IdealSheafData) (U : T.affineOpens)
    (f : I.subscheme ⟶ T) (g : J.subscheme ⟶ T)
    (hcompat : (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left) ≫ f =
      (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) ≫ g)
    (hf : ∀ x, f x ∈ (U : T.Opens)) (hg : ∀ x, g x ∈ (U : T.Opens)) :
    ∃! k : (I ⊓ J).subscheme ⟶ T,
    (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left) ≫ k = f ∧
    (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right) ≫ k = g := by
  obtain ⟨f', hf'⟩ := factors_through_affineOpen U f hf
  obtain ⟨g', hg'⟩ := factors_through_affineOpen U g hg
  have hcompat' :
      (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left) ≫ f' =
        (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) ≫ g' := by
    apply (cancel_mono U.1.ι).mp
    rwa [Category.assoc, hf', Category.assoc, hg']
  obtain ⟨k', ⟨hkI, hkJ⟩, hk_unique⟩ := affineTarget_existsUnique I J f' g' hcompat'
  refine ⟨k' ≫ U.1.ι, ⟨by rw [← Category.assoc, hkI, hf'], by rw [← Category.assoc, hkJ, hg']⟩,
    fun l hl => ?_⟩
  have hlrange (x) : l x ∈ (U : T.Opens) := by
    rcases exists_inclusion_eq_or I J x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · rw [← Scheme.Hom.comp_apply, hl.1]
      exact hf y
    · rw [← Scheme.Hom.comp_apply, hl.2]
      exact hg y
  obtain ⟨l', hl'⟩ := factors_through_affineOpen U l hlrange
  have hlI :
      (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left) ≫ l' = f' := by
    apply (cancel_mono U.1.ι).mp
    rw [Category.assoc, hl', hl.1, hf']
  have hlJ :
      (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right) ≫ l' = g' := by
    apply (cancel_mono U.1.ι).mp
    rw [Category.assoc, hl', hl.2, hg']
  rw [← hl', hk_unique l' ⟨hlI, hlJ⟩]

private theorem comap_inf_of_isOpenImmersion {X Y : Scheme.{u}}
    (I J : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (I ⊓ J).comap f = I.comap f ⊓ J.comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  let V : Y.affineOpens := ⟨f ''ᵁ (U : X.Opens), U.2.image_of_isOpenImmersion f⟩
  show ((I ⊓ J).comap f).ideal U = (I.comap f ⊓ J.comap f).ideal U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (I := I ⊓ J) f U]
  have h₁ : (I ⊓ J).ideal V = I.ideal V ⊓ J.ideal V :=
    congrArg (fun F => F V) (Scheme.IdealSheafData.ideal_inf (I := I) (J := J))
  have h₂ : (I.comap f ⊓ J.comap f).ideal U = (I.comap f).ideal U ⊓ (J.comap f).ideal U :=
    congrArg (fun F => F U) (Scheme.IdealSheafData.ideal_inf (I := I.comap f) (J := J.comap f))
  rw [h₁, h₂, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (I := I) f U,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (I := J) f U]
  exact Ideal.comap_inf _ _ _

private theorem branchMaps_agree_on_overlap {S T : Scheme.{u}}
    (I J : S.IdealSheafData) (f : I.subscheme ⟶ T) (g : J.subscheme ⟶ T)
    (hcompat :
      (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left) ≫ f =
        (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) ≫ g)
    {x : I.subscheme} {y : J.subscheme}
    (hxy :
      (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left) x =
        (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right) y) :
    f x = g y := by
  let C := I ⊔ J
  let cI := Scheme.IdealSheafData.inclusion (I := I) (J := C) le_sup_left
  let cJ := Scheme.IdealSheafData.inclusion (I := J) (J := C) le_sup_right
  have hS : I.subschemeι x = J.subschemeι y := by
    have h := congrArg (I ⊓ J).subschemeι hxy
    simpa only [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι] using h
  have hx : I.subschemeι x ∈ (I.support : Set S) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨x, rfl⟩
  have hy : J.subschemeι y ∈ (J.support : Set S) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  have hC : I.subschemeι x ∈ (C.support : Set S) := by
    rw [Scheme.IdealSheafData.support_sup]
    exact ⟨hx, hS ▸ hy⟩
  have hCrange : I.subschemeι x ∈ Set.range C.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hC
  obtain ⟨z, hz⟩ := hCrange
  have hzI' : I.subschemeι (cI z) = I.subschemeι x := by
    show ((cI ≫ I.subschemeι) z) = I.subschemeι x
    rw [Scheme.IdealSheafData.inclusion_subschemeι]
    exact hz
  have hzI : cI z = x :=
    (IsClosedImmersion.isClosedEmbedding I.subschemeι).injective hzI'
  have hzJ' : J.subschemeι (cJ z) = J.subschemeι y := by
    show ((cJ ≫ J.subschemeι) z) = J.subschemeι y
    rw [Scheme.IdealSheafData.inclusion_subschemeι]
    exact hz.trans hS
  have hzJ : cJ z = y :=
    (IsClosedImmersion.isClosedEmbedding J.subschemeι).injective hzJ'
  have heval := congrArg (fun q : C.subscheme ⟶ T => q z) hcompat
  have heval' : f (cI z) = g (cJ z) := by
    simpa only [Scheme.Hom.comp_apply] using heval
  rw [hzI, hzJ] at heval'
  exact heval'

private theorem existsUnique_continuous_unionBase {S T : Scheme.{u}}
    (I J : S.IdealSheafData) (f : I.subscheme ⟶ T) (g : J.subscheme ⟶ T)
    (hcompat :
      (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left) ≫ f =
        (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) ≫ g) :
    ∃! h : (I ⊓ J).subscheme → T,
      Continuous h ∧
        (∀ x, h ((Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left) x) = f x) ∧
        (∀ y, h ((Scheme.IdealSheafData.inclusion
          (I := I ⊓ J) (J := J) inf_le_right) y) = g y) := by
  let uI := Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left
  let uJ := Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right
  have hcover : Set.range uI ∪ Set.range uJ = Set.univ :=
    Set.eq_univ_iff_forall.mpr (exists_inclusion_eq_or I J)
  obtain ⟨h, ⟨hhI, hhJ⟩, huniq⟩ := existsUnique_function_of_cover uI uJ f g
    (IsClosedImmersion.isClosedEmbedding uI).injective
    (IsClosedImmersion.isClosedEmbedding uJ).injective hcover
    (fun x y hxy => branchMaps_agree_on_overlap I J f g hcompat hxy)
  refine ⟨h, ⟨continuous_of_closed_cover uI uJ f g h
    (IsClosedImmersion.isClosedEmbedding uI) (IsClosedImmersion.isClosedEmbedding uJ)
    hcover f.continuous g.continuous (funext hhI) (funext hhJ), hhI, hhJ⟩,
    fun k hk => huniq k ⟨hk.2.1, hk.2.2⟩⟩

private theorem exists_affineOpen_neighborhood_in_open {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ V : Y.affineOpens, i x ∈ (V : Y.Opens) ∧
      ∀ y : X, i y ∈ (V : Y.Opens) → y ∈ U := by
  have hInd : Topology.IsInducing i.base :=
    (IsClosedImmersion.isClosedEmbedding i).isInducing
  let V' : Y.Opens := hInd.functorObj U
  have hxV' : i x ∈ V' := (hInd.mem_functorObj_iff U).2 hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxV' V'.2
  exact ⟨⟨V, hV⟩, hxV, fun y hy => (hInd.mem_functorObj_iff U).1 (hVU hy)⟩

private theorem exists_affineChart_neighborhood {X S T : Scheme.{u}}
    (i : X ⟶ S) [IsClosedImmersion i] (h : X → T) (hh : Continuous h) (x : X) :
    ∃ (U : T.affineOpens) (V : S.affineOpens), i x ∈ (V : S.Opens) ∧
      ∀ y : X, i y ∈ (V : S.Opens) → h y ∈ (U : T.Opens) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (h x)) isOpen_univ
  let W : X.Opens := ⟨h ⁻¹' (U : Set T), U.2.preimage hh⟩
  obtain ⟨V, hxV, hVW⟩ := exists_affineOpen_neighborhood_in_open i W x hxU
  exact ⟨⟨U, hU⟩, V, hxV, hVW⟩

private noncomputable def restrictSubschemeToAffine {S : Scheme.{u}} (I : S.IdealSheafData)
    (V : S.affineOpens) : (I.comap V.1.ι).subscheme ⟶ I.subscheme :=
  (I.comapIso V.1.ι).hom ≫ pullback.snd V.1.ι I.subschemeι

@[reassoc]
private theorem restrictSubschemeToAffine_subschemeι {S : Scheme.{u}}
    (I : S.IdealSheafData) (V : S.affineOpens) :
    restrictSubschemeToAffine I V ≫ I.subschemeι =
      (I.comap V.1.ι).subschemeι ≫ V.1.ι := by
  dsimp [restrictSubschemeToAffine]
  rw [Scheme.IdealSheafData.comapIso_hom_snd,
    Scheme.IdealSheafData.subschemeMap_subschemeι]

attribute [local simp] restrictSubschemeToAffine_subschemeι
attribute [local simp] restrictSubschemeToAffine_subschemeι_assoc

private theorem restrictedBranchMaps_compatible {S T : Scheme.{u}}
    (I J : S.IdealSheafData) (V : S.affineOpens)
    (f : I.subscheme ⟶ T) (g : J.subscheme ⟶ T)
    (hcompat :
      Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left ≫ f =
        Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right ≫ g) :
    Scheme.IdealSheafData.inclusion
        (I := I.comap V.1.ι) (J := I.comap V.1.ι ⊔ J.comap V.1.ι) le_sup_left ≫
        (restrictSubschemeToAffine I V ≫ f) =
      Scheme.IdealSheafData.inclusion
        (I := J.comap V.1.ι) (J := I.comap V.1.ι ⊔ J.comap V.1.ι) le_sup_right ≫
        (restrictSubschemeToAffine J V ≫ g) := by
  let IV := I.comap V.1.ι
  let JV := J.comap V.1.ι
  let PV := IV ⊔ JV
  let lI := Scheme.IdealSheafData.inclusion (I := IV) (J := PV) le_sup_left
  let lJ := Scheme.IdealSheafData.inclusion (I := JV) (J := PV) le_sup_right
  let rI := restrictSubschemeToAffine I V
  let rJ := restrictSubschemeToAffine J V
  let pI : PV.subscheme ⟶ I.subscheme := lI ≫ rI
  let pJ : PV.subscheme ⟶ J.subscheme := lJ ≫ rJ
  have hbase : pI ≫ I.subschemeι = pJ ≫ J.subschemeι := by
    calc
      pI ≫ I.subschemeι = lI ≫ (rI ≫ I.subschemeι) := by
        simp [pI, Category.assoc]
      _ = lI ≫ (IV.subschemeι ≫ V.1.ι) := by
        rw [restrictSubschemeToAffine_subschemeι]
      _ = PV.subschemeι ≫ V.1.ι := by
        simp [lI]
      _ = lJ ≫ (JV.subschemeι ≫ V.1.ι) := by
        simp [lJ]
      _ = lJ ≫ (rJ ≫ J.subschemeι) := by
        rw [restrictSubschemeToAffine_subschemeι]
      _ = pJ ≫ J.subschemeι := by
        simp [pJ, Category.assoc]
  let P := I ⊔ J
  let iP := Scheme.IdealSheafData.inclusion (I := I) (J := P) le_sup_left
  let jP := Scheme.IdealSheafData.inclusion (I := J) (J := P) le_sup_right
  let hPB := isPullback_subscheme_sup S I J
  let q : PV.subscheme ⟶ P.subscheme := hPB.lift pI pJ hbase
  calc
    lI ≫ (rI ≫ f) = pI ≫ f := rfl
    _ = (q ≫ iP) ≫ f := by rw [hPB.lift_fst pI pJ hbase]
    _ = (q ≫ jP) ≫ g := by
      rw [Category.assoc, Category.assoc, hcompat]
    _ = pJ ≫ g := by rw [hPB.lift_snd pI pJ hbase]
    _ = lJ ≫ (rJ ≫ g) := rfl

private noncomputable def subschemeOpenInclusion {S : Scheme.{u}}
    {I J : S.IdealSheafData} (h : I ≤ J) (V : S.Opens) :
    (J.subschemeι ⁻¹ᵁ V).toScheme ⟶ (I.subschemeι ⁻¹ᵁ V).toScheme :=
  (Scheme.IdealSheafData.inclusion h).resLE _ _ (by
    rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])

@[reassoc]
private lemma subschemeOpenInclusion_ι {S : Scheme.{u}}
    {I J : S.IdealSheafData} (h : I ≤ J) (V : S.Opens) :
    subschemeOpenInclusion h V ≫ (I.subschemeι ⁻¹ᵁ V).ι =
      (J.subschemeι ⁻¹ᵁ V).ι ≫ Scheme.IdealSheafData.inclusion h := by
  simp [subschemeOpenInclusion]

attribute [local simp] subschemeOpenInclusion_ι subschemeOpenInclusion_ι_assoc

private noncomputable def subschemeOpenIso {S : Scheme.{u}}
    (I : S.IdealSheafData) (V : S.Opens) :
    (I.comap V.ι).subscheme ≅ (I.subschemeι ⁻¹ᵁ V).toScheme :=
  I.comapIso V.ι ≪≫ pullbackSymmetry _ _ ≪≫ pullbackRestrictIsoRestrict I.subschemeι V

@[reassoc]
private lemma subschemeOpenIso_hom_ι {S : Scheme.{u}}
    (I : S.IdealSheafData) (V : S.Opens) :
    (subschemeOpenIso I V).hom ≫ (I.subschemeι ⁻¹ᵁ V).ι =
      (I.comapIso V.ι).hom ≫ pullback.snd _ _ := by
  simp [subschemeOpenIso]

attribute [local simp] subschemeOpenIso_hom_ι subschemeOpenIso_hom_ι_assoc

@[reassoc]
private lemma subschemeOpenIso_hom_ι_subschemeι {S : Scheme.{u}}
    (I : S.IdealSheafData) (V : S.Opens) :
    (subschemeOpenIso I V).hom ≫ (I.subschemeι ⁻¹ᵁ V).ι ≫ I.subschemeι =
      (I.comap V.ι).subschemeι ≫ V.ι := by
  simp

attribute [local simp] subschemeOpenIso_hom_ι_subschemeι subschemeOpenIso_hom_ι_subschemeι_assoc

private lemma subscheme_eqToHom {S : Scheme.{u}} {I J : S.IdealSheafData} (h : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

private noncomputable def unionOpenIso {S : Scheme.{u}}
    (I J : S.IdealSheafData) (V : S.Opens) :
    (I.comap V.ι ⊓ J.comap V.ι).subscheme ≅ ((I ⊓ J).subschemeι ⁻¹ᵁ V).toScheme :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (comap_inf_of_isOpenImmersion I J V.ι).symm) ≪≫ subschemeOpenIso (I ⊓ J) V

@[reassoc]
private lemma unionOpenIso_hom_ι_subschemeι {S : Scheme.{u}}
    (I J : S.IdealSheafData) (V : S.Opens) :
    (unionOpenIso I J V).hom ≫ ((I ⊓ J).subschemeι ⁻¹ᵁ V).ι ≫ (I ⊓ J).subschemeι =
      (I.comap V.ι ⊓ J.comap V.ι).subschemeι ≫ V.ι := by
  dsimp [unionOpenIso]
  rw [Category.assoc, subschemeOpenIso_hom_ι_subschemeι]
  rw [← Category.assoc, subscheme_eqToHom (comap_inf_of_isOpenImmersion I J V.ι).symm]

attribute [local simp] unionOpenIso_hom_ι_subschemeι unionOpenIso_hom_ι_subschemeι_assoc

@[reassoc]
private lemma unionOpenIso_inclusion_left {S : Scheme.{u}}
    (I J : S.IdealSheafData) (V : S.Opens) :
    Scheme.IdealSheafData.inclusion
        (I := I.comap V.ι ⊓ J.comap V.ι) (J := I.comap V.ι) inf_le_left ≫
        (unionOpenIso I J V).hom =
      (subschemeOpenIso I V).hom ≫ subschemeOpenInclusion inf_le_left V := by
  apply (cancel_mono (((I ⊓ J).subschemeι ⁻¹ᵁ V).ι ≫ (I ⊓ J).subschemeι)).mp
  simp

attribute [local simp] unionOpenIso_inclusion_left unionOpenIso_inclusion_left_assoc

@[reassoc]
private lemma unionOpenIso_inclusion_right {S : Scheme.{u}}
    (I J : S.IdealSheafData) (V : S.Opens) :
    Scheme.IdealSheafData.inclusion
        (I := I.comap V.ι ⊓ J.comap V.ι) (J := J.comap V.ι) inf_le_right ≫
        (unionOpenIso I J V).hom =
      (subschemeOpenIso J V).hom ≫ subschemeOpenInclusion inf_le_right V := by
  apply (cancel_mono (((I ⊓ J).subschemeι ⁻¹ᵁ V).ι ≫ (I ⊓ J).subschemeι)).mp
  simp

attribute [local simp] unionOpenIso_inclusion_right unionOpenIso_inclusion_right_assoc

private lemma union_hom_ext {S T : Scheme.{u}} (I J : S.IdealSheafData)
    (k l : (I ⊓ J).subscheme ⟶ T)
    (hI : Scheme.IdealSheafData.inclusion inf_le_left ≫ k =
      Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left ≫ l)
    (hJ : Scheme.IdealSheafData.inclusion inf_le_right ≫ k =
      Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right ≫ l) : k = l := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨U, V, hxV, hVU⟩ :=
    exists_affineChart_neighborhood (I ⊓ J).subschemeι k k.continuous x
  let W := (I ⊓ J).subschemeι ⁻¹ᵁ V.1
  let e := unionOpenIso I J V.1
  let k' := e.hom ≫ W.ι ≫ k
  let l' := e.hom ≫ W.ι ≫ l
  let a := Scheme.IdealSheafData.inclusion
    (I := I.comap V.1.ι ⊓ J.comap V.1.ι) (J := I.comap V.1.ι) inf_le_left
  let b := Scheme.IdealSheafData.inclusion
    (I := I.comap V.1.ι ⊓ J.comap V.1.ι) (J := J.comap V.1.ι) inf_le_right
  have hI' : a ≫ k' = a ≫ l' := by
    simpa [a, k', l', e, W] using
      congrArg (fun t => (subschemeOpenIso I V.1).hom ≫
        (I.subschemeι ⁻¹ᵁ V.1).ι ≫ t) hI
  have hJ' : b ≫ k' = b ≫ l' := by
    simpa [b, k', l', e, W] using
      congrArg (fun t => (subschemeOpenIso J V.1).hom ≫
        (J.subschemeι ⁻¹ᵁ V.1).ι ≫ t) hJ
  have hk' (z) : k' z ∈ (U : T.Opens) := hVU _ (e.hom z).property
  obtain ⟨t, ht, huniq⟩ := affineOpenTarget_existsUnique
    (I.comap V.1.ι) (J.comap V.1.ι) U (a ≫ k') (b ≫ k')
    (by simp [a, b, Scheme.IdealSheafData.inclusion_comp_assoc])
    (fun z => hk' (a z)) (fun z => hk' (b z))
  have heq : k' = l' := (huniq k' ⟨rfl, rfl⟩).trans
    (huniq l' ⟨hI'.symm, hJ'.symm⟩).symm
  exact ⟨W, hxV, (cancel_epi e.hom).mp heq⟩

private lemma unionOpen_hom_ext {S T : Scheme.{u}} (I J : S.IdealSheafData)
    (V : S.Opens) (k l : ((I ⊓ J).subschemeι ⁻¹ᵁ V).toScheme ⟶ T)
    (hI : subschemeOpenInclusion (I := I ⊓ J) (J := I) inf_le_left V ≫ k =
      subschemeOpenInclusion inf_le_left V ≫ l)
    (hJ : subschemeOpenInclusion (I := I ⊓ J) (J := J) inf_le_right V ≫ k =
      subschemeOpenInclusion inf_le_right V ≫ l) : k = l := by
  apply (cancel_epi (unionOpenIso I J V).hom).mp
  apply union_hom_ext (I.comap V.ι) (J.comap V.ι)
  · simpa using congrArg (fun t => (subschemeOpenIso I V).hom ≫ t) hI
  · simpa using congrArg (fun t => (subschemeOpenIso J V).hom ≫ t) hJ

@[reassoc]
private lemma subschemeOpenInclusion_map {S : Scheme.{u}}
    {I J : S.IdealSheafData} (h : I ≤ J) {V W : S.Opens} (hVW : V ≤ W) :
    subschemeOpenInclusion h V ≫ I.subscheme.homOfLE (I.subschemeι.preimage_mono hVW) =
      J.subscheme.homOfLE (J.subschemeι.preimage_mono hVW) ≫ subschemeOpenInclusion h W := by
  apply (cancel_mono (I.subschemeι ⁻¹ᵁ W).ι).mp
  simp

attribute [local simp] subschemeOpenInclusion_map subschemeOpenInclusion_map_assoc

private lemma exists_unionOpen_lift {S T : Scheme.{u}} (I J : S.IdealSheafData)
    (f : I.subscheme ⟶ T) (g : J.subscheme ⟶ T)
    (hcompat : Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left ≫ f =
      Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right ≫ g)
    (x : (I ⊓ J).subscheme) :
    ∃ V : S.affineOpens, (I ⊓ J).subschemeι x ∈ (V : S.Opens) ∧
      ∃ k : ((I ⊓ J).subschemeι ⁻¹ᵁ V.1).toScheme ⟶ T,
        subschemeOpenInclusion (I := I ⊓ J) (J := I) inf_le_left V.1 ≫ k =
          (I.subschemeι ⁻¹ᵁ V.1).ι ≫ f ∧
        subschemeOpenInclusion (I := I ⊓ J) (J := J) inf_le_right V.1 ≫ k =
          (J.subschemeι ⁻¹ᵁ V.1).ι ≫ g := by
  obtain ⟨b, ⟨hb, hbI, hbJ⟩, _⟩ := existsUnique_continuous_unionBase I J f g hcompat
  obtain ⟨U, V, hxV, hVU⟩ :=
    exists_affineChart_neighborhood (I ⊓ J).subschemeι b hb x
  let f' := (subschemeOpenIso I V.1).hom ≫ (I.subschemeι ⁻¹ᵁ V.1).ι ≫ f
  let g' := (subschemeOpenIso J V.1).hom ≫ (J.subschemeι ⁻¹ᵁ V.1).ι ≫ g
  have hcompat' :
      Scheme.IdealSheafData.inclusion
          (I := I.comap V.1.ι) (J := I.comap V.1.ι ⊔ J.comap V.1.ι) le_sup_left ≫ f' =
        Scheme.IdealSheafData.inclusion
          (I := J.comap V.1.ι) (J := I.comap V.1.ι ⊔ J.comap V.1.ι) le_sup_right ≫ g' := by
    simpa [f', g', restrictSubschemeToAffine, Category.assoc] using
      restrictedBranchMaps_compatible I J V f g hcompat
  have hmem {K : S.IdealSheafData} (hK : I ⊓ J ≤ K) (φ : K.subscheme ⟶ T)
      (hb : ∀ y, b (Scheme.IdealSheafData.inclusion hK y) = φ y) (z) :
      ((subschemeOpenIso K V.1).hom ≫ (K.subschemeι ⁻¹ᵁ V.1).ι ≫ φ) z ∈ (U : T.Opens) := by
    let y := (K.subschemeι ⁻¹ᵁ V.1).ι ((subschemeOpenIso K V.1).hom z)
    show φ y ∈ (U : T.Opens)
    rw [← hb y]
    apply hVU
    rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
    show K.subschemeι ((K.subschemeι ⁻¹ᵁ V.1).ι ((subschemeOpenIso K V.1).hom z)) ∈ V.1
    rw [Scheme.Opens.ι_apply _ ((subschemeOpenIso K V.1).hom z)]
    exact ((subschemeOpenIso K V.1).hom z).property
  have hf' (z) : f' z ∈ (U : T.Opens) := hmem inf_le_left f hbI z
  have hg' (z) : g' z ∈ (U : T.Opens) := hmem inf_le_right g hbJ z
  obtain ⟨k, hkI, hkJ⟩ := (affineOpenTarget_existsUnique
    (I.comap V.1.ι) (J.comap V.1.ι) U f' g' hcompat' hf' hg').exists
  refine ⟨V, hxV, (unionOpenIso I J V.1).inv ≫ k, ?_, ?_⟩
  · apply (cancel_epi (subschemeOpenIso I V.1).hom).mp
    rw [← unionOpenIso_inclusion_left_assoc]
    simpa [f'] using hkI
  · apply (cancel_epi (subschemeOpenIso J V.1).hom).mp
    rw [← unionOpenIso_inclusion_right_assoc]
    simpa [g'] using hkJ

private lemma union_exists_lift {S T : Scheme.{u}} (I J : S.IdealSheafData)
    (f : I.subscheme ⟶ T) (g : J.subscheme ⟶ T)
    (hcompat : Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left ≫ f =
      Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right ≫ g) :
    ∃ k : (I ⊓ J).subscheme ⟶ T,
      Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left ≫ k = f ∧
      Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right ≫ k = g := by
  classical
  choose V hV k hkI hkJ using exists_unionOpen_lift I J f g hcompat
  have hcover (K : S.IdealSheafData) (hK : I ⊓ J ≤ K) :
      TopologicalSpace.IsOpenCover (fun x : (I ⊓ J).subscheme => K.subschemeι ⁻¹ᵁ (V x).1) := by
    apply TopologicalSpace.IsOpenCover.mk
    apply top_unique
    intro z _
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨Scheme.IdealSheafData.inclusion hK z, ?_⟩
    have hz := hV (Scheme.IdealSheafData.inclusion hK z)
    simpa only [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι,
      Scheme.Hom.mem_preimage] using hz
  let C (K : S.IdealSheafData) (hK : I ⊓ J ≤ K) : K.subscheme.OpenCover :=
    K.subscheme.openCoverOfIsOpenCover _ (hcover K hK)
  let D := C (I ⊓ J) le_rfl
  have hglue : ∀ x y : D.I₀,
      pullback.fst (D.f x) (D.f y) ≫ k x = pullback.snd (D.f x) (D.f y) ≫ k y := by
    intro x y
    change (I ⊓ J).subscheme at x y
    show pullback.fst ((I ⊓ J).subschemeι ⁻¹ᵁ (V x).1).ι
        ((I ⊓ J).subschemeι ⁻¹ᵁ (V y).1).ι ≫ k x =
      pullback.snd ((I ⊓ J).subschemeι ⁻¹ᵁ (V x).1).ι
        ((I ⊓ J).subschemeι ⁻¹ᵁ (V y).1).ι ≫ k y
    let hx := isPullback_opens_inf
      ((I ⊓ J).subschemeι ⁻¹ᵁ (V x).1) ((I ⊓ J).subschemeι ⁻¹ᵁ (V y).1)
    apply (cancel_epi hx.isoPullback.hom).mp
    rw [hx.isoPullback_hom_fst_assoc, hx.isoPullback_hom_snd_assoc]
    have key : (I ⊓ J).subscheme.homOfLE ((I ⊓ J).subschemeι.preimage_mono
          (inf_le_left : (V x).1 ⊓ (V y).1 ≤ (V x).1)) ≫ k x =
        (I ⊓ J).subscheme.homOfLE ((I ⊓ J).subschemeι.preimage_mono
          (inf_le_right : (V x).1 ⊓ (V y).1 ≤ (V y).1)) ≫ k y := by
      apply unionOpen_hom_ext I J ((V x).1 ⊓ (V y).1)
      · rw [subschemeOpenInclusion_map_assoc inf_le_left inf_le_left, hkI x,
          subschemeOpenInclusion_map_assoc inf_le_left inf_le_right, hkI y]
        simp
      · rw [subschemeOpenInclusion_map_assoc inf_le_right inf_le_left, hkJ x,
          subschemeOpenInclusion_map_assoc inf_le_right inf_le_right, hkJ y]
        simp
    exact key
  have glue_incl {K : S.IdealSheafData} (hK : I ⊓ J ≤ K) (φ : K.subscheme ⟶ T)
      (hφ : ∀ x, subschemeOpenInclusion hK (V x).1 ≫ k x = (K.subschemeι ⁻¹ᵁ (V x).1).ι ≫ φ) :
      Scheme.IdealSheafData.inclusion hK ≫ D.glueMorphisms k hglue = φ := by
    apply (C K hK).hom_ext
    intro x
    change (I ⊓ J).subscheme at x
    show (K.subschemeι ⁻¹ᵁ (V x).1).ι ≫ _ = _
    rw [← subschemeOpenInclusion_ι_assoc]
    show subschemeOpenInclusion hK (V x).1 ≫ D.f x ≫ D.glueMorphisms k hglue = _
    exact (congrArg (fun t => subschemeOpenInclusion hK (V x).1 ≫ t)
      (D.ι_glueMorphisms k hglue x)).trans (hφ x)
  exact ⟨D.glueMorphisms k hglue, glue_incl inf_le_left f hkI, glue_incl inf_le_right g hkJ⟩

/-- The canonical square from the scheme-theoretic intersection of two closed subschemes
to the two subschemes and then to their scheme-theoretic union is a pushout square. -/
@[stacks 0C4J "union_pushout"]
theorem isPushout_subscheme_inf {S : Scheme.{u}} (I J : S.IdealSheafData) :
    IsPushout
      (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left)
      (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right)
      (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left)
      (Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right) := by
  classical
  have w :
      Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left ≫
        Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := I) inf_le_left =
      Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right ≫
        Scheme.IdealSheafData.inclusion (I := I ⊓ J) (J := J) inf_le_right := by
    simp [Scheme.IdealSheafData.inclusion_comp]
  choose lift hleft hright using fun s : PushoutCocone
    (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left)
    (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) =>
      union_exists_lift I J s.inl s.inr s.condition
  exact IsPushout.of_isColimit (PushoutCocone.IsColimit.mk w lift hleft hright
    (fun s m hmI hmJ => union_hom_ext I J m (lift s)
      (hmI.trans (hleft s).symm) (hmJ.trans (hright s).symm)))

end AlgebraicGeometry.Scheme.IdealSheafData
