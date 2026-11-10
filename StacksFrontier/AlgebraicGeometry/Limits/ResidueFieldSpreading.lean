module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalFullyFaithful
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# The residue field of a point of a limit as a colimit of locally closed pieces of the stages

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms, let
`y ∈ S` and let `U₀` be an affine open of a stage `S_{i₀}` containing the image of `y`. Write
`U_k ⊆ S_k` for the preimage of `U₀` in a later stage `k`, `A_k = Γ(S_k, U_k)` and
`χ_k : A_k → κ(y)` for evaluation at `y`. Its kernel `𝔭_k` is the prime of the image `y_k` of `y`.
Then `κ(y)` is the filtered colimit of the rings `(A_k / 𝔭_k)[1/g]`, over the pairs `(k, g)`
with `g ∈ A_k`, `g(y) ≠ 0`. Geometrically, `Spec κ(y)` is the limit of the locally closed
subschemes `V(𝔭_k) ∩ D(g)` of the stages: the "irreducible locally closed neighbourhoods" of
the images of `y`.

## Main definitions

* `AlgebraicGeometry.ResidueFieldSpreading.Index`: the pairs `(k, g)`, directed.
* `AlgebraicGeometry.ResidueFieldSpreading.ring`: the rings `(A_k / 𝔭_k)[1/g]`.
* `AlgebraicGeometry.ResidueFieldSpreading.cocone`: their maps to `κ(y)`.

## Main results

* `AlgebraicGeometry.ResidueFieldSpreading.isColimit`: `κ(y)` is their colimit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

/-- Equal morphisms have equal `appLE` maps, whatever the proofs of the inclusions. -/
lemma Scheme.Hom.appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

/-- For `x` in an affine open `U`, the canonical map `Spec κ(x) → X` is the spectrum of evaluation
at `x` followed by `Spec Γ(X, U) → X`. -/
@[reassoc]
lemma IsAffineOpen.SpecMap_evaluation_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) :
    Spec.map (X.evaluation U x hx) ≫ hU.fromSpec = X.fromSpecResidueField x := by
  rw [Scheme.fromSpecResidueField, ← hU.fromSpecStalk_eq_fromSpecStalk hx,
    IsAffineOpen.fromSpecStalk, ← Scheme.germ_residue, Spec.map_comp, Category.assoc]

namespace ResidueFieldSpreading

variable {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {i₀ : I}
  (U₀ : (D.obj (op i₀)).Opens) (y : c.pt) (hy : c.π.app (op i₀) y ∈ U₀)

/-- The preimage of `U₀` in a stage over `i₀`. -/
abbrev stageOpen (k : Over (op i₀)) : (D.obj k.left).Opens := D.map k.hom ⁻¹ᵁ U₀

/-- The preimage of `U₀` in the limit lies in the preimage of `stageOpen D U₀ k`. -/
lemma le_stageOpen (k : Over (op i₀)) :
    c.π.app (op i₀) ⁻¹ᵁ U₀ ≤ c.π.app k.left ⁻¹ᵁ stageOpen D U₀ k := by
  rw [← Scheme.Hom.comp_preimage, c.w]

include hy in
/-- The image of `y` in a stage over `i₀` lies in the preimage of `U₀`. -/
lemma mem_stageOpen (k : Over (op i₀)) : c.π.app k.left y ∈ stageOpen D U₀ k :=
  le_stageOpen D c U₀ k hy

include hy in
/-- The point `y` lies in the preimage of `U₀` in the limit. -/
lemma mem_basePreimage : y ∈ c.π.app (op i₀) ⁻¹ᵁ U₀ := hy

/-- Evaluation at `y` of a section of a stage over the preimage of `U₀`. -/
def stageEval (k : Over (op i₀)) : Γ(D.obj k.left, stageOpen D U₀ k) ⟶ c.pt.residueField y :=
  (c.π.app k.left).appLE (stageOpen D U₀ k) (c.π.app (op i₀) ⁻¹ᵁ U₀) (le_stageOpen D c U₀ k) ≫
    c.pt.evaluation _ y (mem_basePreimage D c U₀ y hy)

/-- `stageOpen D U₀ k'` lies in the preimage of `stageOpen D U₀ k` for `k'` over `k`. -/
lemma stageOpen_le {k k' : Over (op i₀)} (m : k' ⟶ k) :
    stageOpen D U₀ k' ≤ D.map m.left ⁻¹ᵁ stageOpen D U₀ k := by
  rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w m]

/-- Restriction of sections from one stage to a later one. -/
def stageRes {k k' : Over (op i₀)} (m : k' ⟶ k) :
    Γ(D.obj k.left, stageOpen D U₀ k) ⟶ Γ(D.obj k'.left, stageOpen D U₀ k') :=
  (D.map m.left).appLE _ _ (stageOpen_le D U₀ m)

/-- There is at most one morphism between two stages over `i₀`. -/
instance {k k' : Over (op i₀)} : Subsingleton (k' ⟶ k) :=
  ⟨fun _ _ => Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

/-- Restriction of sections is compatible with composition of stages. -/
@[reassoc]
lemma stageRes_comp {k k' k'' : Over (op i₀)} (m : k' ⟶ k) (m' : k'' ⟶ k') :
    stageRes D U₀ m ≫ stageRes D U₀ m' = stageRes D U₀ (m' ≫ m) := by
  rw [stageRes, stageRes, stageRes, Scheme.Hom.appLE_comp_appLE]
  exact Scheme.Hom.appLE_eq_of_eq (by rw [Over.comp_left, D.map_comp]) _ _

/-- Restriction along the identity is the identity. -/
lemma stageRes_id (k : Over (op i₀)) : stageRes D U₀ (𝟙 k) = 𝟙 _ := by
  have h : D.map (Over.Hom.left (𝟙 k)) = 𝟙 _ := by rw [Over.id_left, D.map_id]
  rw [stageRes,
    Scheme.Hom.appLE_eq_of_eq (U := stageOpen D U₀ k) (V := stageOpen D U₀ k) h _ le_rfl]
  dsimp only [Scheme.Hom.appLE]
  exact (D.obj k.left).presheaf.map_id (op (stageOpen D U₀ k))

/-- Restriction to a later stage followed by pullback to the limit is pullback to the limit. -/
@[reassoc]
lemma stageRes_appLE {k k' : Over (op i₀)} (m : k' ⟶ k) :
    stageRes D U₀ m ≫ (c.π.app k'.left).appLE (stageOpen D U₀ k') (c.π.app (op i₀) ⁻¹ᵁ U₀)
      (le_stageOpen D c U₀ k') =
    (c.π.app k.left).appLE (stageOpen D U₀ k) (c.π.app (op i₀) ⁻¹ᵁ U₀)
      (le_stageOpen D c U₀ k) := by
  simp only [stageRes, Scheme.Hom.appLE_comp_appLE]
  exact Scheme.Hom.appLE_eq_of_eq (c.w m.left) _ _

/-- Evaluation at `y` commutes with restriction to a later stage. -/
@[reassoc]
lemma stageRes_stageEval {k k' : Over (op i₀)} (m : k' ⟶ k) :
    stageRes D U₀ m ≫ stageEval D c U₀ y hy k' = stageEval D c U₀ y hy k := by
  simp only [stageEval, stageRes_appLE_assoc]

/-- The pairs `(k, g)`: a stage over `i₀` and a section of it over the preimage of `U₀` which does
not vanish at `y`. -/
structure Index where
  /-- The stage. -/
  k : Over (op i₀)
  /-- The section. -/
  g : Γ(D.obj k.left, stageOpen D U₀ k)
  /-- It does not vanish at `y`. -/
  hg : stageEval D c U₀ y hy k g ≠ 0

variable {D c U₀ y hy}

/-- `(k, g) ≤ (k', g')` when `k'` lies over `k` and the restriction of `g` to `k'` divides `g'`. -/
instance : Preorder (Index D c U₀ y hy) where
  le a b := ∃ m : b.k ⟶ a.k, stageRes D U₀ m a.g ∣ b.g
  le_refl a := ⟨𝟙 _, by rw [stageRes_id]; exact dvd_rfl⟩
  le_trans a b c := by
    rintro ⟨m, hm⟩ ⟨m', hm'⟩
    refine ⟨m' ≫ m, ?_⟩
    rw [← stageRes_comp, CommRingCat.comp_apply]
    exact (map_dvd (stageRes D U₀ m').hom hm).trans hm'

variable (D c U₀ y hy)

/-- The kernel of evaluation at `y`, the prime of the image of `y`. -/
abbrev stagePrime (k : Over (op i₀)) : Ideal Γ(D.obj k.left, stageOpen D U₀ k) :=
  RingHom.ker (stageEval D c U₀ y hy k).hom

/-- The ring `(A_k / 𝔭_k)[1/g]`. -/
abbrev ring (a : Index D c U₀ y hy) : Type u :=
  Localization.Away (Ideal.Quotient.mk (stagePrime D c U₀ y hy a.k) a.g)

/-- The canonical map `A_k → (A_k / 𝔭_k)[1/g]`. -/
def toRing (a : Index D c U₀ y hy) : Γ(D.obj a.k.left, stageOpen D U₀ a.k) →+* ring D c U₀ y hy a :=
  (algebraMap (Γ(D.obj a.k.left, stageOpen D U₀ a.k) ⧸ stagePrime D c U₀ y hy a.k)
    (ring D c U₀ y hy a)).comp (Ideal.Quotient.mk _)

/-- Restriction to a later stage maps the prime of the image of `y` into the prime of the image of
`y`. -/
lemma stagePrime_le_comap {k k' : Over (op i₀)} (m : k' ⟶ k) :
    stagePrime D c U₀ y hy k ≤ (stagePrime D c U₀ y hy k').comap (stageRes D U₀ m).hom := by
  intro x hx
  simp only [Ideal.mem_comap, RingHom.mem_ker] at hx ⊢
  rw [← CommRingCat.comp_apply, stageRes_stageEval]
  exact hx

/-- The transition map `(A_k / 𝔭_k)[1/g] → (A_{k'} / 𝔭_{k'})[1/g']` for `(k, g) ≤ (k', g')`. -/
def transition {a b : Index D c U₀ y hy} (h : a ≤ b) : ring D c U₀ y hy a →+* ring D c U₀ y hy b :=
  IsLocalization.Away.lift (Ideal.Quotient.mk (stagePrime D c U₀ y hy a.k) a.g)
    (g := (algebraMap (Γ(D.obj b.k.left, stageOpen D U₀ b.k) ⧸ stagePrime D c U₀ y hy b.k)
      (ring D c U₀ y hy b)).comp (Ideal.quotientMap (stagePrime D c U₀ y hy b.k)
        (stageRes D U₀ h.choose).hom (stagePrime_le_comap D c U₀ y hy h.choose))) (by
    have hu : IsUnit (toRing D c U₀ y hy b b.g) :=
      IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk (stagePrime D c U₀ y hy b.k) b.g)
    have hd := isUnit_of_dvd_unit (map_dvd (toRing D c U₀ y hy b) h.choose_spec) hu
    simpa [toRing] using hd)

/-- The transition maps are compatible with the canonical maps from the rings of sections. -/
@[simp]
lemma transition_toRing {a b : Index D c U₀ y hy} (h : a ≤ b) (x) :
    transition D c U₀ y hy h (toRing D c U₀ y hy a x) =
      toRing D c U₀ y hy b (stageRes D U₀ h.choose x) := by
  rw [transition, toRing, RingHom.comp_apply, IsLocalization.Away.lift_eq, RingHom.comp_apply,
    Ideal.quotientMap_mk]
  rfl

/-- Two ring maps out of `(A_k / 𝔭_k)[1/g]` agreeing on the image of `A_k` are equal. -/
lemma ringHom_ext {a : Index D c U₀ y hy} {R : Type*} [CommRing R]
    {φ ψ : ring D c U₀ y hy a →+* R}
    (h : ∀ x, φ (toRing D c U₀ y hy a x) = ψ (toRing D c U₀ y hy a x)) : φ = ψ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (Ideal.Quotient.mk (stagePrime D c U₀ y hy a.k) a.g))
  apply Ideal.Quotient.ringHom_ext
  ext x
  exact h x

/-- The rings `(A_k / 𝔭_k)[1/g]`, as a functor on the directed set of pairs. -/
def ringFunctor : Index D c U₀ y hy ⥤ CommRingCat.{u} where
  obj a := CommRingCat.of (ring D c U₀ y hy a)
  map h := CommRingCat.ofHom (transition D c U₀ y hy (leOfHom h))
  map_id a := by
    ext1
    refine ringHom_ext D c U₀ y hy fun x => ?_
    simp only [CommRingCat.hom_ofHom, transition_toRing, CommRingCat.hom_id, RingHom.id_apply]
    congr 1
    rw [Subsingleton.elim (leOfHom (𝟙 a)).choose (𝟙 _), stageRes_id]
    rfl
  map_comp {a b d} h h' := by
    ext1
    refine ringHom_ext D c U₀ y hy fun x => ?_
    simp only [CommRingCat.hom_ofHom, transition_toRing, CommRingCat.hom_comp, RingHom.comp_apply]
    congr 1
    rw [← CommRingCat.comp_apply, stageRes_comp]
    congr 2

/-- The value of `g` at `y` is a unit of `κ(y)`. -/
lemma isUnit_stageEval (a : Index D c U₀ y hy) :
    IsUnit ((Ideal.Quotient.lift (stagePrime D c U₀ y hy a.k) (stageEval D c U₀ y hy a.k).hom
      fun _ hx => RingHom.mem_ker.mp hx) (Ideal.Quotient.mk (stagePrime D c U₀ y hy a.k) a.g)) := by
  rw [Ideal.Quotient.lift_mk]
  exact isUnit_iff_ne_zero.mpr a.hg

/-- The ring map `(A_k / 𝔭_k)[1/g] → κ(y)` induced by evaluation at `y`. -/
def toResidueFieldHom (a : Index D c U₀ y hy) : ring D c U₀ y hy a →+* c.pt.residueField y :=
  IsLocalization.Away.lift (Ideal.Quotient.mk (stagePrime D c U₀ y hy a.k) a.g)
    (isUnit_stageEval D c U₀ y hy a)

/-- The map `(A_k / 𝔭_k)[1/g] → κ(y)` restricts to evaluation at `y` on `A_k`. -/
@[simp]
lemma toResidueFieldHom_toRing (a : Index D c U₀ y hy) (x) :
    toResidueFieldHom D c U₀ y hy a (toRing D c U₀ y hy a x) = stageEval D c U₀ y hy a.k x := by
  rw [toResidueFieldHom, toRing, RingHom.comp_apply, IsLocalization.Away.lift_eq,
    Ideal.Quotient.lift_mk]

/-- The map `(A_k / 𝔭_k)[1/g] → κ(y)` induced by evaluation at `y`. -/
def toResidueField (a : Index D c U₀ y hy) :
    (ringFunctor D c U₀ y hy).obj a ⟶ c.pt.residueField y :=
  CommRingCat.ofHom (toResidueFieldHom D c U₀ y hy a)

/-- The map `(A_k / 𝔭_k)[1/g] → κ(y)` restricts to evaluation at `y` on `A_k`. -/
@[simp]
lemma toResidueField_toRing (a : Index D c U₀ y hy) (x) :
    toResidueField D c U₀ y hy a (toRing D c U₀ y hy a x) = stageEval D c U₀ y hy a.k x :=
  toResidueFieldHom_toRing D c U₀ y hy a x

/-- The cocone of the rings `(A_k / 𝔭_k)[1/g]` with vertex `κ(y)`. -/
def cocone : Cocone (ringFunctor D c U₀ y hy) where
  pt := c.pt.residueField y
  ι :=
    { app a := toResidueField D c U₀ y hy a
      naturality {a b} h := by
        ext1
        refine ringHom_ext D c U₀ y hy fun x => ?_
        change toResidueField D c U₀ y hy b (transition D c U₀ y hy (leOfHom h)
          (toRing D c U₀ y hy a x)) = toResidueField D c U₀ y hy a (toRing D c U₀ y hy a x)
        rw [transition_toRing, toResidueField_toRing, toResidueField_toRing,
          ← CommRingCat.comp_apply, stageRes_stageEval] }

/-- The map `(A_k / 𝔭_k)[1/g] → κ(y)` is injective. -/
lemma toResidueFieldHom_injective (a : Index D c U₀ y hy) :
    Function.Injective (toResidueFieldHom D c U₀ y hy a) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (Ideal.Quotient.mk (stagePrime D c U₀ y hy a.k) a.g)) x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hspec := IsLocalization.mk'_spec (ring D c U₀ y hy a) (Ideal.Quotient.mk _ r) m
  have h2 := congrArg (toResidueFieldHom D c U₀ y hy a) hspec
  rw [map_mul, hx, zero_mul] at h2
  have h3 : stageEval D c U₀ y hy a.k r = 0 := by
    rw [← toResidueFieldHom_toRing D c U₀ y hy a r]
    exact h2.symm
  have h4 : Ideal.Quotient.mk (stagePrime D c U₀ y hy a.k) r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr h3
  rw [h4]
  exact IsLocalization.mk'_zero m

variable [IsDirected I (· ≤ ·)]

/-- The pairs `(k, g)` form a nonempty set. -/
instance : Nonempty (Index D c U₀ y hy) :=
  ⟨⟨Over.mk (𝟙 _), 1, by simp⟩⟩

/-- The pairs `(k, g)` form a directed set. -/
instance : IsDirected (Index D c U₀ y hy) (· ≤ ·) where
  directed a b := by
    have : Nonempty I := ⟨i₀⟩
    let k := IsCofiltered.min a.k b.k
    let m₁ := IsCofiltered.minToLeft a.k b.k
    let m₂ := IsCofiltered.minToRight a.k b.k
    refine ⟨⟨k, stageRes D U₀ m₁ a.g * stageRes D U₀ m₂ b.g, ?_⟩, ⟨m₁, dvd_mul_right _ _⟩,
      ⟨m₂, dvd_mul_left _ _⟩⟩
    rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stageRes_stageEval,
      stageRes_stageEval]
    exact mul_ne_zero a.hg b.hg

variable [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- Sections of the limit over the preimage of `U₀` come from sections of the stages. -/
lemma exists_appLE_eq (hc : IsLimit c) (hU₀ : IsAffineOpen U₀)
    (s : Γ(c.pt, c.π.app (op i₀) ⁻¹ᵁ U₀)) :
    ∃ (k : Over (op i₀)) (t : Γ(D.obj k.left, stageOpen D U₀ k)),
      (c.π.app k.left).appLE (stageOpen D U₀ k) _ (le_stageOpen D c U₀ k) t = s := by
  have : Nonempty I := ⟨i₀⟩
  have (k : Over (op i₀)) : IsAffine ((opensDiagram D (op i₀) U₀).obj k) :=
    hU₀.preimage (D.map _)
  obtain ⟨k, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit _ _
    (isLimitOpensCone D c hc (op i₀) U₀) ((c.π.app (op i₀) ⁻¹ᵁ U₀).topIso.inv s)
  refine ⟨k, (stageOpen D U₀ k).topIso.hom t, ?_⟩
  have h := congrArg (c.π.app (op i₀) ⁻¹ᵁ U₀).topIso.hom ht
  rw [Iso.inv_hom_id_apply] at h
  rw [← h]
  have e := congrArg (fun φ => ((c.π.app (op i₀) ⁻¹ᵁ U₀).topIso.hom) (φ t))
    (Scheme.Hom.resLE_app_top (f := c.π.app k.left) (e := le_stageOpen D c U₀ k))
  refine Eq.trans ?_ e.symm
  exact (Iso.inv_hom_id_apply (c.π.app (op i₀) ⁻¹ᵁ U₀).topIso _).symm

/-- If `U₀` is affine, so is its preimage in the limit. -/
private lemma isAffineOpen_preimage_π (hc : IsLimit c) (hU₀ : IsAffineOpen U₀) :
    IsAffineOpen (X := c.pt) (c.π.app (op i₀) ⁻¹ᵁ U₀) := by
  have : Nonempty I := ⟨i₀⟩
  have := isAffineHom_π_app D c hc (op i₀)
  exact hU₀.preimage _

/-- Every element of `κ(y)` comes from some `(A_k / 𝔭_k)[1/g]`. -/
lemma exists_toResidueFieldHom_eq (hc : IsLimit c) (hU₀ : IsAffineOpen U₀)
    (z : c.pt.residueField y) :
    ∃ (a : Index D c U₀ y hy) (x : ring D c U₀ y hy a), toResidueFieldHom D c U₀ y hy a x = z := by
  have hUy := isAffineOpen_preimage_π D c U₀ hc hU₀
  obtain ⟨s, rfl⟩ := c.pt.residue_surjective y z
  let := c.pt.presheaf.algebra_section_stalk (U := c.π.app (op i₀) ⁻¹ᵁ U₀) ⟨y, hy⟩
  have hloc := hUy.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective
    (hUy.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl s
  have hspec := IsLocalization.mk'_spec (c.pt.presheaf.stalk y) a b
  have hb : IsUnit (algebraMap _ (c.pt.presheaf.stalk y) (b : Γ(c.pt, c.π.app (op i₀) ⁻¹ᵁ U₀))) :=
    IsLocalization.map_units _ b
  obtain ⟨k₁, t₁, ht₁⟩ := exists_appLE_eq D c U₀ hc hU₀ a
  obtain ⟨k₂, t₂, ht₂⟩ := exists_appLE_eq D c U₀ hc hU₀ b
  let k := IsCofiltered.min k₁ k₂
  let m₁ := IsCofiltered.minToLeft k₁ k₂
  let m₂ := IsCofiltered.minToRight k₁ k₂
  let ev := c.pt.evaluation _ y (mem_basePreimage D c U₀ y hy)
  have ev_res {k' : Over (op i₀)} (m : k ⟶ k') (t : Γ(D.obj k'.left, stageOpen D U₀ k'))
      (s : Γ(c.pt, c.π.app (op i₀) ⁻¹ᵁ U₀))
      (ht : (c.π.app k'.left).appLE (stageOpen D U₀ k') _ (le_stageOpen D c U₀ k') t = s) :
      stageEval D c U₀ y hy k (stageRes D U₀ m t) = ev s := by
    rw [← CommRingCat.comp_apply, stageRes_stageEval, stageEval, CommRingCat.comp_apply, ht]
  have ev₁ := ev_res m₁ t₁ _ ht₁
  have ev₂ := ev_res m₂ t₂ _ ht₂
  have hne : ev (b : Γ(c.pt, c.π.app (op i₀) ⁻¹ᵁ U₀)) ≠ 0 :=
    (hb.map (c.pt.residue y).hom).ne_zero
  let μ : Index D c U₀ y hy := ⟨k, stageRes D U₀ m₂ t₂, ev₂ ▸ hne⟩
  refine ⟨μ, IsLocalization.mk' (ring D c U₀ y hy μ)
    (Ideal.Quotient.mk (stagePrime D c U₀ y hy k) (stageRes D U₀ m₁ t₁))
    ⟨_, Submonoid.mem_powers (Ideal.Quotient.mk (stagePrime D c U₀ y hy k)
      (stageRes D U₀ m₂ t₂))⟩, ?_⟩
  have h₁ := congrArg (toResidueFieldHom D c U₀ y hy μ) (IsLocalization.mk'_spec
    (ring D c U₀ y hy μ) (Ideal.Quotient.mk (stagePrime D c U₀ y hy k) (stageRes D U₀ m₁ t₁))
    ⟨_, Submonoid.mem_powers (Ideal.Quotient.mk (stagePrime D c U₀ y hy k)
      (stageRes D U₀ m₂ t₂))⟩)
  have h₂ := congrArg (c.pt.residue y) hspec
  rw [map_mul] at h₁ h₂
  change _ * toResidueFieldHom D c U₀ y hy μ (toRing D c U₀ y hy μ _) =
    toResidueFieldHom D c U₀ y hy μ (toRing D c U₀ y hy μ _) at h₁
  rw [toResidueFieldHom_toRing, toResidueFieldHom_toRing, ev₁, ev₂] at h₁
  change _ * ev (b : Γ(c.pt, c.π.app (op i₀) ⁻¹ᵁ U₀)) = ev a at h₂
  exact mul_right_cancel₀ hne (h₁.trans h₂.symm)

/-- **`κ(y)` is the filtered colimit of the rings `(A_k / 𝔭_k)[1/g]`.** -/
def isColimit (hc : IsLimit c) (hU₀ : IsAffineOpen U₀) : IsColimit (cocone D c U₀ y hy) := by
  have : ReflectsFilteredColimits (forget CommRingCat.{u}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  refine isColimitOfReflects (forget CommRingCat.{u}) (Types.FilteredColimit.isColimitOf'
    (ringFunctor D c U₀ y hy ⋙ forget CommRingCat.{u})
    ((forget CommRingCat.{u}).mapCocone (cocone D c U₀ y hy)) ?_ ?_)
  · intro z
    obtain ⟨a, x, hx⟩ := exists_toResidueFieldHom_eq D c U₀ y hy hc hU₀ z
    exact ⟨a, x, hx.symm⟩
  · intro a x x' h
    exact ⟨a, 𝟙 a, by rw [toResidueFieldHom_injective D c U₀ y hy a h]⟩

/-! ### The geometric side: `Spec κ(y)` as a limit of locally closed pieces of the stages -/

section Geometric

variable (hU₀ : IsAffineOpen U₀)

omit [IsDirected I (· ≤ ·)] in
include hU₀ in
/-- If `U₀` is affine, so is its preimage in every stage over `i₀`. -/
lemma isAffineOpen_stageOpen (k : Over (op i₀)) : IsAffineOpen (stageOpen D U₀ k) :=
  hU₀.preimage (D.map k.hom)

/-- The canonical map `A_k → (A_k / 𝔭_k)[1/g]`, as a morphism of rings. -/
def toRingHom (a : Index D c U₀ y hy) :
    Γ(D.obj a.k.left, stageOpen D U₀ a.k) ⟶ (ringFunctor D c U₀ y hy).obj a :=
  CommRingCat.ofHom (toRing D c U₀ y hy a)

omit [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- The canonical maps `A_k → (A_k / 𝔭_k)[1/g]` commute with the transition maps. -/
@[reassoc]
lemma toRingHom_comp_map {a b : Index D c U₀ y hy} (h : a ⟶ b) :
    toRingHom D c U₀ y hy a ≫ (ringFunctor D c U₀ y hy).map h =
      stageRes D U₀ (leOfHom h).choose ≫ toRingHom D c U₀ y hy b := by
  ext x
  exact transition_toRing D c U₀ y hy (leOfHom h) x

omit [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- The composite `A_k → (A_k / 𝔭_k)[1/g] → κ(y)` is evaluation at `y`. -/
@[reassoc]
lemma toRingHom_comp_toResidueField (a : Index D c U₀ y hy) :
    toRingHom D c U₀ y hy a ≫ toResidueField D c U₀ y hy a = stageEval D c U₀ y hy a.k := by
  ext x
  exact toResidueField_toRing D c U₀ y hy a x

/-- The locally closed piece `Spec (A_k / 𝔭_k)[1/g] → S_k`. -/
def stageSpecMap (a : Index D c U₀ y hy) :
    Spec ((ringFunctor D c U₀ y hy).obj a) ⟶ D.obj a.k.left :=
  Spec.map (toRingHom D c U₀ y hy a) ≫ (isAffineOpen_stageOpen D U₀ hU₀ a.k).fromSpec

/-- The locally closed piece, as a scheme over the base stage `S_{i₀}`. -/
def baseMap (a : Index D c U₀ y hy) : Spec ((ringFunctor D c U₀ y hy).obj a) ⟶ D.obj (op i₀) :=
  stageSpecMap D c U₀ y hy hU₀ a ≫ D.map a.k.hom

/-- The inverse system of the schemes `Spec (A_k / 𝔭_k)[1/g]`. -/
abbrev specDiagram : (Index D c U₀ y hy)ᵒᵖ ⥤ Scheme.{u} :=
  (ringFunctor D c U₀ y hy).op ⋙ Scheme.Spec

/-- The structure morphisms of the pieces to the base stage, as a natural transformation. -/
def toBase : specDiagram D c U₀ y hy ⟶ (Functor.const _).obj (D.obj (op i₀)) where
  app a := baseMap D c U₀ y hy hU₀ a.unop
  naturality {a b} h := by
    simp only [specDiagram, Functor.comp_map, Functor.op_map, Scheme.Spec_map, Quiver.Hom.unop_op,
      Functor.const_obj_map, Category.comp_id, Functor.const_obj_obj]
    rw [baseMap, baseMap, stageSpecMap, stageSpecMap, Category.assoc, Category.assoc,
      ← Spec.map_comp_assoc, toRingHom_comp_map, Spec.map_comp_assoc, stageRes,
      IsAffineOpen.SpecMap_appLE_fromSpec_assoc, ← D.map_comp, Over.w]

/-- The cone of the pieces with vertex `Spec κ(y)`. -/
abbrev specCone : Cone (specDiagram D c U₀ y hy) :=
  Scheme.Spec.mapCone (cocone D c U₀ y hy).op

/-- The projection of `Spec κ(y)` to a piece, followed by the piece's map to the base stage, is the
canonical map `Spec κ(y) → S_{i₀}`. -/
lemma specCone_π_baseMap (hc : IsLimit c) (a : Index D c U₀ y hy) :
    (specCone D c U₀ y hy).π.app (op a) ≫ baseMap D c U₀ y hy hU₀ a =
      c.pt.fromSpecResidueField y ≫ c.π.app (op i₀) := by
  have hUy := isAffineOpen_preimage_π D c U₀ hc hU₀
  change Spec.map (toResidueField D c U₀ y hy a) ≫ baseMap D c U₀ y hy hU₀ a = _
  rw [baseMap, stageSpecMap, Category.assoc, ← Spec.map_comp_assoc, toRingHom_comp_toResidueField,
    stageEval,
    Spec.map_comp_assoc, IsAffineOpen.SpecMap_appLE_fromSpec_assoc (hV := hUy),
    IsAffineOpen.SpecMap_evaluation_fromSpec_assoc, ← Cone.w c a.k.hom]

/-- **`Spec κ(y)` is the limit of the pieces `Spec (A_k / 𝔭_k)[1/g]`.** -/
def isLimitSpecCone (hc : IsLimit c) : IsLimit (specCone D c U₀ y hy) :=
  isLimitOfPreserves Scheme.Spec (isColimit D c U₀ y hy hc hU₀).op

/-- The pieces, as schemes over the base stage. -/
abbrev overDiagram : (Index D c U₀ y hy)ᵒᵖ ⥤ Over (D.obj (op i₀)) :=
  Over.lift (specDiagram D c U₀ y hy) (toBase D c U₀ y hy hU₀)

/-- `Spec κ(y)` as a cone of schemes over the base stage. -/
abbrev overCone (hc : IsLimit c) : Cone (overDiagram D c U₀ y hy hU₀) :=
  Over.liftCone (specDiagram D c U₀ y hy) (toBase D c U₀ y hy hU₀) (specCone D c U₀ y hy)
    (c.pt.fromSpecResidueField y ≫ c.π.app (op i₀))
    (fun a => specCone_π_baseMap D c U₀ y hy hU₀ hc a.unop)

/-- `Spec κ(y)` is the limit of the pieces, over the base stage. -/
def isLimitOverCone (hc : IsLimit c) : IsLimit (overCone D c U₀ y hy hU₀ hc) :=
  Over.isLimitLiftCone _ _ _ _ _ (isLimitSpecCone D c U₀ y hy hU₀ hc)

variable {X₀ : Scheme.{u}} (g₀ : X₀ ⟶ D.obj (op i₀))

/-- The base changes `X₀ ×_{S_{i₀}} Spec (A_k / 𝔭_k)[1/g]`. -/
abbrev fibreDiagram : (Index D c U₀ y hy)ᵒᵖ ⥤ Scheme.{u} :=
  overDiagram D c U₀ y hy hU₀ ⋙ Over.pullback g₀ ⋙ Over.forget X₀

/-- The fibre `X₀ ×_{S_{i₀}} Spec κ(y)` as a cone over the base changes of the pieces. -/
abbrev fibreCone (hc : IsLimit c) : Cone (fibreDiagram D c U₀ y hy hU₀ g₀) :=
  (Over.pullback g₀ ⋙ Over.forget X₀).mapCone (overCone D c U₀ y hy hU₀ hc)

attribute [local instance] IsCofiltered.isConnected in
/-- **The fibre over `y` is the limit of the base changes of the pieces.** -/
def isLimitFibreCone (hc : IsLimit c) : IsLimit (fibreCone D c U₀ y hy hU₀ g₀ hc) :=
  isLimitOfPreserves _ (isLimitOverCone D c U₀ y hy hU₀ hc)

end Geometric

/-! ### Spreading out an isomorphism of modules on the fibre -/

/-- Two modules on `X₀` have isomorphic pullbacks to the base change of `g₀ : X₀ ⟶ S` along
`q : T ⟶ S`. -/
def IsoAlong {X₀ S T : Scheme.{u}} (g₀ : X₀ ⟶ S) (M N : X₀.Modules) (q : T ⟶ S) : Prop :=
  Nonempty ((Scheme.Modules.pullback (pullback.snd q g₀)).obj M ≅
    (Scheme.Modules.pullback (pullback.snd q g₀)).obj N)

/-- Isomorphic pullbacks along `t'` are the same as isomorphic pullbacks along `t` after pulling
back along `φ`, when `φ ≫ t = t'`. -/
private lemma nonempty_iso_pullback_comp_iff {A B X₀ : Scheme.{u}} (φ : A ⟶ B) {t : B ⟶ X₀}
    {t' : A ⟶ X₀} (h : φ ≫ t = t') {M N : X₀.Modules} :
    Nonempty ((Scheme.Modules.pullback t').obj M ≅ (Scheme.Modules.pullback t').obj N) ↔
      Nonempty ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback t).obj M) ≅
        (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback t).obj N)) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨((Scheme.Modules.pullbackComp φ t).app M) ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫
      e ≪≫ (Scheme.Modules.pullbackCongr h).symm.app N ≪≫
        ((Scheme.Modules.pullbackComp φ t).app N).symm⟩
  · rintro ⟨e⟩
    exact ⟨(Scheme.Modules.pullbackCongr h).symm.app M ≪≫
      ((Scheme.Modules.pullbackComp φ t).app M).symm ≪≫ e ≪≫
        (Scheme.Modules.pullbackComp φ t).app N ≪≫ (Scheme.Modules.pullbackCongr h).app N⟩

/-- Isomorphic pullbacks along `t` give isomorphic pullbacks along any `φ ≫ t`. -/
lemma nonempty_iso_pullback_of_comp {A B X₀ : Scheme.{u}} (φ : A ⟶ B) {t : B ⟶ X₀}
    {t' : A ⟶ X₀} (h : φ ≫ t = t') {M N : X₀.Modules}
    (e : Nonempty ((Scheme.Modules.pullback t).obj M ≅ (Scheme.Modules.pullback t).obj N)) :
    Nonempty ((Scheme.Modules.pullback t').obj M ≅ (Scheme.Modules.pullback t').obj N) :=
  (nonempty_iso_pullback_comp_iff φ h).mpr ⟨(Scheme.Modules.pullback φ).mapIso e.some⟩

/-- Isomorphic pullbacks along `q` give isomorphic pullbacks along any `w ≫ q`. -/
lemma IsoAlong.comp {X₀ S T T' : Scheme.{u}} {g₀ : X₀ ⟶ S} {M N : X₀.Modules} {q : T ⟶ S}
    (h : IsoAlong g₀ M N q) (w : T' ⟶ T) : IsoAlong g₀ M N (w ≫ q) :=
  nonempty_iso_pullback_of_comp (pullback.map (w ≫ q) g₀ q g₀ w (𝟙 _) (𝟙 _)
    (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp]))
    (by rw [pullback.lift_snd, Category.comp_id]) h

/-- `IsoAlong` transports along an equality of morphisms. -/
lemma IsoAlong.of_eq {X₀ S T : Scheme.{u}} {g₀ : X₀ ⟶ S} {M N : X₀.Modules} {q q' : T ⟶ S}
    (h : IsoAlong g₀ M N q) (e : q = q') : IsoAlong g₀ M N q' := e ▸ h

section Spreading

variable (hU₀ : IsAffineOpen U₀) {X₀ : Scheme.{u}}
  (g₀ : X₀ ⟶ D.obj (op i₀)) [QuasiCompact g₀] [QuasiSeparated g₀]

/-- **An isomorphism on the fibre over `y` spreads out to one of the pieces.** -/
theorem exists_isoAlong_baseMap (hc : IsLimit c) (M N : X₀.Modules)
    (hM : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hN : SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    (h : IsoAlong g₀ M N (c.pt.fromSpecResidueField y ≫ c.π.app (op i₀))) :
    ∃ a : Index D c U₀ y hy, IsoAlong g₀ M N (baseMap D c U₀ y hy hU₀ a) := by
  classical
  have : Nonempty I := ⟨i₀⟩
  have hfl : ∀ {a b} (f : a ⟶ b), IsAffineHom ((fibreDiagram D c U₀ y hy hU₀ g₀).map f) := by
    intro a b f
    refine MorphismProperty.overPullbackMap (P := @IsAffineHom) g₀ _ ?_
    change IsAffineHom (Spec.map _)
    infer_instance
  have hcs : ∀ a, CompactSpace ((fibreDiagram D c U₀ y hy hU₀ g₀).obj a) := fun a => by
    change CompactSpace ↥(pullback (baseMap D c U₀ y hy hU₀ a.unop) g₀)
    infer_instance
  have hqs : ∀ a, QuasiSeparatedSpace ((fibreDiagram D c U₀ y hy hU₀ g₀).obj a) := fun a => by
    change QuasiSeparatedSpace ↥(pullback (baseMap D c U₀ y hy hU₀ a.unop) g₀)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (baseMap D c U₀ y hy hU₀ a.unop) g₀)
  let a₀ : Index D c U₀ y hy := Classical.arbitrary _
  let t₀ := pullback.snd (baseMap D c U₀ y hy hU₀ a₀) g₀
  have hleg : ∀ (a : (Index D c U₀ y hy)ᵒᵖ) (b : Index D c U₀ y hy) (f : a ⟶ op b),
      (fibreDiagram D c U₀ y hy hU₀ g₀).map f ≫ pullback.snd (baseMap D c U₀ y hy hU₀ b) g₀ =
        pullback.snd (baseMap D c U₀ y hy hU₀ a.unop) g₀ := fun a b f =>
    Over.w ((Over.pullback g₀).map ((overDiagram D c U₀ y hy hU₀).map f))
  have hcone : (fibreCone D c U₀ y hy hU₀ g₀ hc).π.app (op a₀) ≫ t₀ =
      pullback.snd (c.pt.fromSpecResidueField y ≫ c.π.app (op i₀)) g₀ :=
    Over.w ((Over.pullback g₀).map ((overCone D c U₀ y hy hU₀ hc).π.app (op a₀)))
  have hA := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation _
    (SheafOfModules.IsFiniteLocallyFree.pullback_scheme t₀ M hM)
  have hB := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation _
    (SheafOfModules.IsFiniteLocallyFree.pullback_scheme t₀ N hN)
  obtain ⟨j, e, hj⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_iso_of_hasCanonicalDescent _ _
      (isLimitFibreCone D c U₀ y hy hU₀ g₀ hc)
    (Stacks.AlgebraicGeometry.ModuleLimits.hasCanonicalDescent_of_isLimit' _ _
      (isLimitFibreCone D c U₀ y hy hU₀ g₀ hc)) (op a₀) _ _ hA hB
    ((nonempty_iso_pullback_comp_iff _ hcone).mp h)
  exact ⟨j.unop, (nonempty_iso_pullback_comp_iff _ (hleg j a₀ e)).mpr hj⟩

end Spreading

/-! ### The locally closed pieces as sets of points of the stages -/

section Points

omit [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- Evaluation at `y` is evaluation at the image of `y` in the stage, followed by the map of
residue fields. -/
lemma stageEval_eq (k : Over (op i₀)) :
    stageEval D c U₀ y hy k = (D.obj k.left).evaluation (stageOpen D U₀ k) (c.π.app k.left y)
      (mem_stageOpen D c U₀ y hy k) ≫ (c.π.app k.left).residueFieldMap y := by
  rw [Scheme.evaluation_naturality, stageEval, Scheme.Hom.appLE, Category.assoc]
  congr 1
  exact c.pt.presheaf.germ_res'_assoc _ _ _ _

omit [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- A section vanishes at `y` if and only if it vanishes at the image of `y` in the stage. -/
lemma stageEval_eq_zero_iff (k : Over (op i₀)) (x : Γ(D.obj k.left, stageOpen D U₀ k)) :
    stageEval D c U₀ y hy k x = 0 ↔
      (D.obj k.left).evaluation (stageOpen D U₀ k) (c.π.app k.left y)
        (mem_stageOpen D c U₀ y hy k) x = 0 := by
  rw [stageEval_eq, CommRingCat.comp_apply]
  exact map_eq_zero_iff _ ((c.π.app k.left).residueFieldMap y).hom.injective

/-- The points of the locally closed piece of index `(k, g)`: the specialisations of the image of
`y` in `S_k` at which `g` does not vanish. -/
def pieceSet (a : Index D c U₀ y hy) : Set (D.obj a.k.left) :=
  ((D.obj a.k.left).basicOpen a.g : Set (D.obj a.k.left)) ∩ closure {c.π.app a.k.left y}

omit [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- The image of `y` in `S_k` lies in the piece of index `(k, g)`. -/
lemma mem_pieceSet (a : Index D c U₀ y hy) : c.π.app a.k.left y ∈ pieceSet D c U₀ y hy a := by
  refine ⟨?_, subset_closure rfl⟩
  rw [SetLike.mem_coe, ← Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _
    (mem_stageOpen D c U₀ y hy a.k), ne_eq, ← stageEval_eq_zero_iff]
  exact a.hg

omit [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- In a Noetherian stage, the piece of index `(k, g)` is locally constructible. -/
lemma isLocallyConstructible_pieceSet (a : Index D c U₀ y hy) [NoetherianSpace (D.obj a.k.left)] :
    Topology.IsLocallyConstructible (pieceSet D c U₀ y hy a) := by
  refine (Topology.IsConstructible.inter ?_ ?_).isLocallyConstructible
  · exact (NoetherianSpace.isCompact _).isConstructible ((D.obj a.k.left).basicOpen a.g).isOpen
  · rw [← Topology.isConstructible_compl]
    exact (NoetherianSpace.isCompact _).isConstructible isClosed_closure.isOpen_compl

variable {a : Index D c U₀ y hy} {t : D.obj a.k.left}

omit [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- A point of the piece lies in the preimage of `U₀`. -/
lemma mem_stageOpen_of_mem_pieceSet (ht : t ∈ pieceSet D c U₀ y hy a) : t ∈ stageOpen D U₀ a.k :=
  (D.obj a.k.left).basicOpen_le a.g ht.1

omit [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- A section vanishing at `y` vanishes at every point of the piece. -/
lemma evaluation_eq_zero_of_mem_pieceSet (ht : t ∈ pieceSet D c U₀ y hy a)
    (x : Γ(D.obj a.k.left, stageOpen D U₀ a.k)) (hx : stageEval D c U₀ y hy a.k x = 0) :
    (D.obj a.k.left).evaluation _ t (mem_stageOpen_of_mem_pieceSet D c U₀ y hy ht) x = 0 := by
  by_contra hne
  have hne' := (Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ _ _).mp hne
  obtain ⟨z, hz, rfl⟩ := mem_closure_iff.mp ht.2 _ ((D.obj a.k.left).basicOpen x).isOpen hne'
  rw [stageEval_eq_zero_iff, Scheme.evaluation_eq_zero_iff_notMem_basicOpen] at hx
  exact hx hz

omit [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- At a point of the piece, the value of `g` is a unit of the residue field. -/
lemma isUnit_evaluation_of_mem_pieceSet (ht : t ∈ pieceSet D c U₀ y hy a) :
    IsUnit ((Ideal.Quotient.lift (stagePrime D c U₀ y hy a.k)
      ((D.obj a.k.left).evaluation _ t (mem_stageOpen_of_mem_pieceSet D c U₀ y hy ht)).hom
        fun x hx => evaluation_eq_zero_of_mem_pieceSet D c U₀ y hy ht x (RingHom.mem_ker.mp hx))
      (Ideal.Quotient.mk (stagePrime D c U₀ y hy a.k) a.g)) := by
  rw [Ideal.Quotient.lift_mk]
  exact isUnit_iff_ne_zero.mpr ((Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ _ _).mpr ht.1)

/-- The residue field of a point of the piece receives the ring of the piece. -/
def liftResidueFieldHom (ht : t ∈ pieceSet D c U₀ y hy a) :
    ring D c U₀ y hy a →+* (D.obj a.k.left).residueField t :=
  IsLocalization.Away.lift (Ideal.Quotient.mk (stagePrime D c U₀ y hy a.k) a.g)
    (isUnit_evaluation_of_mem_pieceSet D c U₀ y hy ht)

/-- The residue field of a point of the piece receives the ring of the piece. -/
def liftResidueField (ht : t ∈ pieceSet D c U₀ y hy a) :
    (ringFunctor D c U₀ y hy).obj a ⟶ (D.obj a.k.left).residueField t :=
  CommRingCat.ofHom (liftResidueFieldHom D c U₀ y hy ht)

omit [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- The composite `A_k → (A_k / 𝔭_k)[1/g] → κ(t)` is evaluation at `t`. -/
lemma toRingHom_comp_liftResidueField (ht : t ∈ pieceSet D c U₀ y hy a) :
    toRingHom D c U₀ y hy a ≫ liftResidueField D c U₀ y hy ht =
      (D.obj a.k.left).evaluation _ t (mem_stageOpen_of_mem_pieceSet D c U₀ y hy ht) := by
  ext x
  change liftResidueFieldHom D c U₀ y hy ht (toRing D c U₀ y hy a x) = _
  rw [liftResidueFieldHom, toRing, RingHom.comp_apply, IsLocalization.Away.lift_eq,
    Ideal.Quotient.lift_mk]

omit [IsDirected I (· ≤ ·)] in
/-- **Every point of the piece factors through the piece.** -/
lemma SpecMap_liftResidueField_stageSpecMap (hU₀ : IsAffineOpen U₀)
    (ht : t ∈ pieceSet D c U₀ y hy a) :
    Spec.map (liftResidueField D c U₀ y hy ht) ≫ stageSpecMap D c U₀ y hy hU₀ a =
      (D.obj a.k.left).fromSpecResidueField t := by
  rw [stageSpecMap, ← Spec.map_comp_assoc, toRingHom_comp_liftResidueField,
    IsAffineOpen.SpecMap_evaluation_fromSpec]

end Points

end ResidueFieldSpreading

open ResidueFieldSpreading in
/-- **Spreading out an isomorphism of modules from the fibre over a point of a limit to a locally
constructible neighbourhood of its image in a stage.**

Let `S = lim Sᵢ` be a directed inverse limit of Noetherian schemes with affine transition
morphisms, `g₀ : X₀ ⟶ S_{i₀}` quasi-compact and quasi-separated, and `M, N` finite locally free
`𝒪_{X₀}`-modules. If `M` and `N` have isomorphic pullbacks to the fibre `X₀ ×_{S_{i₀}} Spec κ(y)`
over a point `y ∈ S`, then there are a later stage `S_k` and a locally constructible set `C ⊆ S_k`
containing the image of `y` such that `M` and `N` have isomorphic pullbacks to the fibre over
every point of `C`.

The set `C` is `V(𝔭) ∩ D(g)` inside an affine open of `S_k`, where `𝔭` is the prime of the image
of `y`. -/
theorem exists_isLocallyConstructible_isoAlong {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, NoetherianSpace (D.obj i)] (c : Cone D) (hc : IsLimit c) (i₀ : I)
    {X₀ : Scheme.{u}} (g₀ : X₀ ⟶ D.obj (op i₀)) [QuasiCompact g₀] [QuasiSeparated g₀]
    (M N : X₀.Modules) (hM : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hN : SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) (y : c.pt)
    (h : IsoAlong g₀ M N (c.pt.fromSpecResidueField y ≫ c.π.app (op i₀))) :
    ∃ (k : Over (op i₀)) (C : Set (D.obj k.left)), Topology.IsLocallyConstructible C ∧
      c.π.app k.left y ∈ C ∧
      ∀ t ∈ C, IsoAlong g₀ M N ((D.obj k.left).fromSpecResidueField t ≫ D.map k.hom) := by
  obtain ⟨_, ⟨U₀, hU₀ : IsAffineOpen U₀, rfl⟩, hyU, -⟩ :=
    (D.obj (op i₀)).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (c.π.app (op i₀) y)) isOpen_univ
  obtain ⟨a, ha⟩ := exists_isoAlong_baseMap D c U₀ y hyU hU₀ g₀ hc M N hM hN h
  refine ⟨a.k, pieceSet D c U₀ y hyU a, isLocallyConstructible_pieceSet D c U₀ y hyU a,
    mem_pieceSet D c U₀ y hyU a, fun t ht => ?_⟩
  refine (ha.comp (Spec.map (liftResidueField D c U₀ y hyU ht))).of_eq ?_
  rw [baseMap, ← Category.assoc, SpecMap_liftResidueField_stageSpecMap]

/-- The fibre condition is inherited by the points over a point: if `M` and `N` are isomorphic on
the fibre over `ψ t`, they are isomorphic on the fibre over `t`. -/
lemma ResidueFieldSpreading.IsoAlong.of_residueField {X₀ S A B : Scheme.{u}} {g₀ : X₀ ⟶ S}
    {M N : X₀.Modules} (ψ : A ⟶ B) (qB : B ⟶ S) (t : A)
    (h : ResidueFieldSpreading.IsoAlong g₀ M N (B.fromSpecResidueField (ψ t) ≫ qB)) :
    ResidueFieldSpreading.IsoAlong g₀ M N (A.fromSpecResidueField t ≫ ψ ≫ qB) :=
  (h.comp (Spec.map (ψ.residueFieldMap t))).of_eq
    (by rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc])

open ResidueFieldSpreading in
/-- **A pointwise fibre condition on the limit holds at every point of some stage.**

Let `S = lim Sᵢ` be a directed inverse limit of Noetherian quasi-compact quasi-separated schemes
with affine transition morphisms and quasi-compact quasi-separated limit, `g₀ : X₀ ⟶ S_{i₀}`
quasi-compact and quasi-separated, and `(M i, N i)` a family of pairs of finite locally free
`𝒪_{X₀}`-modules. If over every point `y` of `S` some pair has isomorphic pullbacks to the
fibre, then there is a stage `S_j` over every point of which some pair has isomorphic pullbacks
to the fibre. -/
theorem exists_stage_forall_isoAlong {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, NoetherianSpace (D.obj i)] [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (op i))] (c : Cone D) (hc : IsLimit c)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt] (i₀ : I)
    {X₀ : Scheme.{u}} (g₀ : X₀ ⟶ D.obj (op i₀)) [QuasiCompact g₀] [QuasiSeparated g₀]
    {ι : Type*} (M N : ι → X₀.Modules)
    (hM : ∀ i, SheafOfModules.IsFiniteLocallyFree.{u, u, u} (M i))
    (hN : ∀ i, SheafOfModules.IsFiniteLocallyFree.{u, u, u} (N i))
    (h : ∀ y : c.pt, ∃ i, IsoAlong g₀ (M i) (N i) (c.pt.fromSpecResidueField y ≫ c.π.app (op i₀))) :
    ∃ (j : I) (hj : i₀ ≤ j), ∀ t : D.obj (op j), ∃ i,
      IsoAlong g₀ (M i) (N i) ((D.obj (op j)).fromSpecResidueField t ≫ D.map (homOfLE hj).op) := by
  classical
  have : Nonempty I := ⟨i₀⟩
  choose ι' hι' using h
  choose k C hCl hyC hgood using fun y =>
    exists_isLocallyConstructible_isoAlong D c hc i₀ g₀ (M (ι' y)) (N (ι' y)) (hM _) (hN _) y
      (hι' y)
  let P : c.pt → Set c.pt := fun y => c.π.app (k y).left ⁻¹' C y
  have hP : ∀ y, Topology.IsConstructible (X := c.pt) (P y) := fun y =>
    (isLocallyConstructible_preimage (X := c.pt) (c.π.app (k y).left) (hCl y)).isConstructible
  let V : c.pt → Set (WithConstructibleTopology c.pt) := fun y =>
    WithTopology.ofTopology ⁻¹' P y
  have hV : ∀ y, IsOpen (V y) := fun y => by
    rw [WithConstructibleTopology.isOpen_iff]
    have := TopologicalSpace.isOpen_generateFrom_of_mem
      (g := {s : Set c.pt | Topology.IsConstructible s}) (hP y)
    rw [← constructibleTopology_eq_generateFrom_isConstructible] at this
    exact this
  obtain ⟨σ, hσ⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun z _ => Set.mem_iUnion.mpr ⟨z.ofTopology, hyC z.ofTopology⟩)
  obtain ⟨k₀, hk₀⟩ := IsCofiltered.inf_objs_exists (σ.image k)
  let m : ∀ y ∈ σ, k₀ ⟶ k y := fun y hy => (hk₀ (Finset.mem_image_of_mem k hy)).some
  let E : Set (D.obj k₀.left) := ⋃ y ∈ σ.attach, D.map (m y.1 y.2).left ⁻¹' C y.1
  have hE : IsLocallyConstructible E :=
    IsLocallyConstructible.biUnion σ.attach.finite_toSet fun y _ =>
      isLocallyConstructible_preimage _ (hCl y.1)
  have hlim : Set.range (c.π.app k₀.left) ⊆ E := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hσ (Set.mem_univ (WithTopology.toTopology _ x)))
    refine Set.mem_iUnion₂.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, ?_⟩
    change (c.π.app k₀.left ≫ D.map (m y hy).left) x ∈ C y
    rw [c.w]
    exact hxy
  let DS : DescentSituation.{u, u} I :=
    { system := D
      transition_affine := fun f => inferInstance
      quasiCompact := inferInstance
      quasiSeparated := inferInstance
      limitCone := c
      isLimit := hc
      base := k₀.left.unop }
  obtain ⟨j, hbj, hj⟩ := (eventually_range_transition_subset_of_isLocallyConstructible DS E hE
    hlim).exists
  have hij : i₀ ≤ j := (leOfHom k₀.hom.unop).trans hbj
  refine ⟨j, hij, fun t => ?_⟩
  obtain ⟨⟨y, hy⟩, -, hty⟩ := Set.mem_iUnion₂.mp (hj ⟨t, rfl⟩)
  refine ⟨ι' y, ?_⟩
  have := ResidueFieldSpreading.IsoAlong.of_residueField
    (D.map (homOfLE hbj).op ≫ D.map (m y hy).left) (D.map (k y).hom) t (hgood y _ hty)
  refine this.of_eq ?_
  rw [← D.map_comp, ← D.map_comp]
  congr 2

end AlgebraicGeometry

end
