module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.SetTheoreticEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# Testing universal injectivity on the base changes to schemes

Universal injectivity of a morphism of algebraic spaces over a scheme `S` is a condition on
the maps of point sets of all of its base changes along algebraic spaces. This module shows
that it is already detected by the base changes along schemes, and indeed by the base changes
along affine schemes, by a single surjective scheme chart of the target, or by a Zariski
covering of the target.

## Main results

* `AlgebraicGeometry.Space.universallyInjective_tfae`: **Stacks 03MX**, the five equivalent
  criteria.

## Implementation notes

Schemes over `S` are the objects of the chosen big fppf site over `S`, and a scheme-valued
test object enters through its representable presheaf; the base change `Z ×_Y X ⟶ Z` is the
second projection of the presheaf fibre product. A Zariski covering of the target is a family
of open subfunctors as in Stacks 02YY, and the base change along a member is the second
projection along its inclusion.

Each of the three criteria that imply universal injectivity does so through the same two
steps. First, universal injectivity of the base change `Z ×_Y X ⟶ Z` makes that projection
*injective on the sections* over the spectrum of a field in the site: the relative diagonal is
surjective on points by Stacks 040X, so the section of `(Z ×_Y X) ×_Z (Z ×_Y X)` assembled
from two sections with the same image becomes a restriction of the diagonal over a common
field-valued extension, where the two components agree. Second, the two sections of the source
therefore agree after restriction along one morphism of field spectra, and such a morphism is
flat, surjective and quasi-compact, hence a one-member fpqc covering; an algebraic space is an
fpqc sheaf by Stacks 0APL, so the two sections were already equal.

The criterion for affine test schemes needs no covering argument, because the spectrum of a
field is itself affine. The criterion for a surjective scheme chart uses surjectivity to move
the image point of the two sections to a point of the chart, and the criterion for a Zariski
covering uses Stacks 03BZ to find a member containing that image point and Stacks 03IE to
factor the map through it.

## References

* [Stacks Project, Tag 03MX](https://stacks.math.columbia.edu/tag/03MX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms of field spectra are fpqc coverings -/

/-- A morphism between the spectra of two fields is flat, surjective and quasi-compact. -/
private theorem flat_surjective_quasiCompact_of_fieldSpec (K L : Type u) [Field K] [Field L]
    (f : Spec (.of L) ⟶ Spec (.of K)) : Flat f ∧ Surjective f ∧ QuasiCompact f := by
  let _ : Field (↑(CommRingCat.of K)) := inferInstanceAs (Field K)
  let _ : Field (↑(CommRingCat.of L)) := inferInstanceAs (Field L)
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ⟨?_, ?_, ?_⟩
  · rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField (↑(CommRingCat.of K))) φ.hom
  · rw [surjective_iff]
    exact fun _ ↦ ⟨(⊥ : PrimeSpectrum (CommRingCat.of L)), Subsingleton.elim _ _⟩
  · infer_instance

/-- **Separatedness along a field extension.** Two sections of an algebraic space over `S`
over the spectrum of a field in the site which agree after restriction along a morphism from
the spectrum of another field in the site are equal: that morphism is a one-member fpqc
covering and an algebraic space is an fpqc sheaf by Stacks 0APL. -/
private theorem eq_of_map_eq_fieldSpec {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (K L : Type u) [Field K] [Field L]
    (hK : B.Contains (Spec (.of K))) (hL : B.Contains (Spec (.of L)))
    (sK : Spec (.of K) ⟶ S) (sL : Spec (.of L) ⟶ S)
    (c : fieldObject (hS := hS) L hL sL ⟶ fieldObject (hS := hS) K hK sK)
    (x y : X.obj (Opposite.op (fieldObject (hS := hS) K hK sK)))
    (h : X.map c.op x = X.map c.op y) : x = y := by
  obtain ⟨_, _, _⟩ := flat_surjective_quasiCompact_of_fieldSpec K L
    ((BigFppfOver.toScheme B S hS).map c)
  have hcover : Sieve.generate (Presieve.singleton c) ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
        (fieldObject (hS := hS) K hK sK) := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [Precoverage.mem_comap_iff, Presieve.map_singleton]
    exact Scheme.Hom.singleton_mem_fpqcPrecoverage _
  refine hX.isSheaf_fpqc.isSeparated _ (Sieve.generate (Presieve.singleton c)) hcover x y ?_
  rintro A' b ⟨W, e, g, hg, rfl⟩
  cases hg
  simpa using congrArg (fun z ↦ X.map e.op z) h

/-! ### Injectivity on sections from universal injectivity -/

/-- Sections with the same image under `f` give morphisms from the representable presheaf
with the same composition with `f`. -/
private theorem yonedaEquiv_symm_comp_eq_of_app_eq {C : Type (u + 1)} [Category.{u} C]
    {X Y : Cᵒᵖ ⥤ Type u} (f : X ⟶ Y) {A : C} {x y : X.obj (Opposite.op A)}
    (h : f.app (Opposite.op A) x = f.app (Opposite.op A) y) :
    yonedaEquiv.symm x ≫ f = yonedaEquiv.symm y ≫ f := by
  rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h]

/-- Sections of a presheaf have equal restrictions along `c` as soon as the corresponding
morphisms from the representable presheaf agree after precomposition with `yoneda.map c`. -/
private theorem map_eq_of_yoneda_map_comp_eq {C : Type (u + 1)} [Category.{u} C]
    {X : Cᵒᵖ ⥤ Type u} {A B : C} (c : B ⟶ A) {x y : X.obj (Opposite.op A)}
    (h : yoneda.map c ≫ yonedaEquiv.symm x = yoneda.map c ≫ yonedaEquiv.symm y) :
    X.map c.op x = X.map c.op y := by
  refine yonedaEquiv.symm.injective ?_
  rw [← yonedaEquiv_symm_naturality_left, ← yonedaEquiv_symm_naturality_left]
  exact h

/-- Restricting a section along `d` and then applying `g` corresponds to precomposing the
morphism from the representable presheaf with `yoneda.map d`. -/
private theorem yoneda_map_comp_yonedaEquiv_symm_comp {C : Type (u + 1)} [Category.{u} C]
    {X Y : Cᵒᵖ ⥤ Type u} (g : X ⟶ Y) {A B : C} (d : B ⟶ A) {a : X.obj (Opposite.op A)}
    {b : Y.obj (Opposite.op B)} (h : Y.map d.op (g.app (Opposite.op A) a) = b) :
    yoneda.map d ≫ yonedaEquiv.symm a ≫ g = yonedaEquiv.symm b := by
  rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_left]
  exact congrArg yonedaEquiv.symm h

/-- Two morphisms from a representable presheaf to the source of `f` which have the same
composition with `f` and lift the same morphism to `Z` are equal, as soon as the second
projection of the fibre product `X ×_Y Z` is injective on the sections over the representing
object. -/
private theorem eq_of_injective_pullback_snd_app {C : Type (u + 1)} [Category.{u} C]
    {X Y Z : Cᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y) (A : C)
    (hinj : Function.Injective ((pullback.snd f g).app (Opposite.op A)))
    (v₁ v₂ : yoneda.obj A ⟶ X) (w : yoneda.obj A ⟶ Z)
    (h₁ : v₁ ≫ f = w ≫ g) (h₂ : v₂ ≫ f = w ≫ g) : v₁ = v₂ := by
  have hlift : pullback.lift v₁ w h₁ = pullback.lift v₂ w h₂ :=
    yonedaEquiv.injective (hinj (by
      rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, pullback.lift_snd, pullback.lift_snd]))
  rw [← pullback.lift_fst v₁ w h₁, hlift, pullback.lift_fst]

/-- A universally injective morphism out of an algebraic space over `S` is injective on the
sections over the spectrum of a field in the site.

The relative diagonal is surjective on points by Stacks 040X, so the section of `P ×_Z P`
assembled from two sections of `P` with the same image in `Z` is, over a common field-valued
extension, the image under the diagonal of a section of `P`; there its two components are
equal, so the two sections agree after one restriction, and an algebraic space is separated
for the fpqc topology. -/
private theorem injective_app_fieldSpec_of_universallyInjective
    {P Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P) (k : P ⟶ Z)
    (hk : UniversallyInjective B S hS k) (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (s : Spec (.of K) ⟶ S) :
    Function.Injective (k.app (Opposite.op (fieldObject (hS := hS) K hK s))) := by
  intro x y hxy
  have hcomp := yonedaEquiv_symm_comp_eq_of_app_eq k hxy
  obtain ⟨ξ, hξ⟩ := isSurjective_diagonal_of_universallyInjective B S hS hP k hk
    (FieldValuedPoint.class B S hS (pullback k k)
      { carrier := K, contained := hK, toBase := s
        value := yonedaEquiv (pullback.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) hcomp) })
  obtain ⟨ξ₀, rfl⟩ := Quot.exists_rep ξ
  have hξ' : FieldValuedPoint.class B S hS (pullback k k)
      (FieldValuedPoint.map B S hS P (pullback.diagonal k) ξ₀) =
        FieldValuedPoint.class B S hS (pullback k k)
          { carrier := K, contained := hK, toBase := s
            value := yonedaEquiv
              (pullback.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) hcomp) } := hξ
  obtain ⟨r, ⟨d, hd⟩, ⟨c, hc⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS (pullback k k) _ _).mp hξ'
  let d' : FieldValuedPoint.siteObject B S hS (pullback k k) r ⟶
    FieldValuedPoint.siteObject B S hS P ξ₀ := d
  have hd' : (pullback k k).map d'.op ((pullback.diagonal k).app
      (Opposite.op (FieldValuedPoint.siteObject B S hS P ξ₀)) ξ₀.value) = r.value := hd
  have hdm := yoneda_map_comp_yonedaEquiv_symm_comp (pullback.diagonal k) d' hd'
  have hcm : yoneda.map c ≫
      pullback.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) hcomp =
      yonedaEquiv.symm r.value := by
    have h0 := yonedaEquiv_symm_naturality_left c (pullback k k)
      (yonedaEquiv (pullback.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) hcomp))
    rw [Equiv.symm_apply_apply] at h0
    rw [h0]
    exact congrArg yonedaEquiv.symm hc
  have hkey := hcm.trans hdm.symm
  have hfst : yoneda.map c ≫ yonedaEquiv.symm x =
      yoneda.map d' ≫ yonedaEquiv.symm ξ₀.value := by
    simpa only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id] using
      congrArg (· ≫ pullback.fst k k) hkey
  have hsnd : yoneda.map c ≫ yonedaEquiv.symm y =
      yoneda.map d' ≫ yonedaEquiv.symm ξ₀.value := by
    simpa only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id] using
      congrArg (· ≫ pullback.snd k k) hkey
  exact eq_of_map_eq_fieldSpec B S hS hP K r.carrier hK r.contained s r.toBase c x y
    (map_eq_of_yoneda_map_comp_eq c (hfst.trans hsnd.symm))

/-- A morphism of presheaves on the big fppf site of `S` is universally injective as soon as
it is injective on the sections over the spectrum of every field in the site. -/
private theorem universallyInjective_of_injective_fieldSections
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
      (s : Spec (.of K) ⟶ S),
      Function.Injective (f.app (Opposite.op (fieldObject (hS := hS) K hK s)))) :
    UniversallyInjective B S hS f := by
  refine universallyInjective_of_fieldPoints B S hS f fun p y hy ↦ ?_
  have hpy : p.value = y := h p.carrier p.contained p.toBase hy
  refine ⟨p, 𝟙 p.siteObject, by simp, ?_⟩
  rw [← hpy]
  simp

/-- The combination of the two previous lemmas used by each of the three criteria: two
morphisms from the spectrum of a field in the site to the source of `f` which lift the same
morphism to `Z` and have the same composition with `f` agree, as soon as the base change of
`f` along `Z ⟶ Y` is universally injective. -/
private theorem eq_of_universallyInjective_pullback_snd
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y)
    (g : Z ⟶ Y) (hsnd : UniversallyInjective B S hS (pullback.snd f g))
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (s : Spec (.of K) ⟶ S)
    (v₁ v₂ : yoneda.obj (fieldObject (hS := hS) K hK s) ⟶ X)
    (w : yoneda.obj (fieldObject (hS := hS) K hK s) ⟶ Z)
    (h₁ : v₁ ≫ f = w ≫ g) (h₂ : v₂ ≫ f = w ≫ g) : v₁ = v₂ :=
  eq_of_injective_pullback_snd_app f g _
    (injective_app_fieldSpec_of_universallyInjective B S hS
      (isAlgebraicSpace_pullback B S hS f g hX hZ hY) (pullback.snd f g) hsnd K hK s)
    v₁ v₂ w h₁ h₂

/-- The presheaf represented by the spectrum of a field in the site has a single point, so a
morphism out of it sends every point to the class of its own section. -/
private theorem pointsMap_yoneda_fieldObject_eq
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (s : Spec (.of K) ⟶ S)
    (g : yoneda.obj (fieldObject (hS := hS) K hK s) ⟶ Y)
    (p : FieldValuedPoint B S hS (yoneda.obj (fieldObject (hS := hS) K hK s))) :
    pointsMap B S hS (yoneda.obj (fieldObject (hS := hS) K hK s)) g
        (FieldValuedPoint.class B S hS
          (yoneda.obj (fieldObject (hS := hS) K hK s)) p) =
      FieldValuedPoint.class B S hS Y
        { carrier := K, contained := hK, toBase := s, value := yonedaEquiv g } :=
  FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS Y
    ⟨FieldValuedPoint.map B S hS _ g p, FieldValuedPoint.dominates_refl B S hS Y _,
      ⟨p.value, map_yonedaEquiv g p.value⟩⟩

/-! ### The three criteria -/

/-- Stability of universal injectivity under base change, in the form of the second
projection of the fibre product. -/
private theorem universallyInjective_pullback_snd
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y)
    (g : Z ⟶ Y) (hf : UniversallyInjective B S hS f) :
    UniversallyInjective B S hS (pullback.snd f g) :=
  universallyInjective_of_isPullback B S hS hX hZ hY f g hf
    (IsPullback.of_hasPullback f g).flip

/-- A morphism of algebraic spaces over `S` all of whose base changes along affine schemes
are universally injective is universally injective. -/
private theorem universallyInjective_of_affine_scheme_tests
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
        UniversallyInjective B S hS (pullback.snd f g)) :
    UniversallyInjective B S hS f := by
  refine universallyInjective_of_injective_fieldSections B S hS f ?_
  intro K _ hK s x y hxy
  have hcomp := yonedaEquiv_symm_comp_eq_of_app_eq f hxy
  have hA : IsAffine ((BigFppfOver.toScheme B S hS).obj (fieldObject (hS := hS) K hK s)) := by
    change IsAffine (Spec (.of K))
    infer_instance
  refine yonedaEquiv.symm.injective (eq_of_universallyInjective_pullback_snd B S hS hX hY
    (isAlgebraicSpace_yoneda B S hS (fieldObject (hS := hS) K hK s)) f
    (yonedaEquiv.symm x ≫ f)
    (h (fieldObject (hS := hS) K hK s) (yonedaEquiv.symm x ≫ f) hA) K hK s
    (yonedaEquiv.symm x) (yonedaEquiv.symm y) (𝟙 _) (by rw [Category.id_comp])
    (by rw [Category.id_comp, hcomp]))

/-- A morphism of algebraic spaces over `S` whose base change along one surjective scheme
chart of the target is universally injective is universally injective. -/
private theorem universallyInjective_of_surjective_scheme_test
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (Z : BigFppfOver B S hS)
    (g : yoneda.obj Z ⟶ Y) (hg : IsSurjective B S hS g)
    (hsnd : UniversallyInjective B S hS (pullback.snd f g)) :
    UniversallyInjective B S hS f := by
  refine universallyInjective_of_injective_fieldSections B S hS f ?_
  intro K _ hK s x y hxy
  have hcomp := yonedaEquiv_symm_comp_eq_of_app_eq f hxy
  obtain ⟨w, hw⟩ := hg (FieldValuedPoint.class B S hS Y
    { carrier := K, contained := hK, toBase := s, value := f.app (Opposite.op _) x })
  obtain ⟨pz, rfl⟩ := Quot.exists_rep w
  have hw' : FieldValuedPoint.class B S hS Y
      (FieldValuedPoint.map B S hS (yoneda.obj Z) g pz) =
        FieldValuedPoint.class B S hS Y
          { carrier := K, contained := hK, toBase := s
            value := f.app (Opposite.op _) x } := hw
  obtain ⟨r, ⟨br, hbr⟩, ⟨ar, har⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS Y _ _).mp hw'
  have he₁ := yoneda_map_comp_yonedaEquiv_symm_comp f ar har
  let br' : FieldValuedPoint.siteObject B S hS Y r ⟶
    FieldValuedPoint.siteObject B S hS (yoneda.obj Z) pz := br
  have hbr' : Y.map br'.op (g.app (Opposite.op
      (FieldValuedPoint.siteObject B S hS (yoneda.obj Z) pz)) pz.value) = r.value := hbr
  have heZ := yoneda_map_comp_yonedaEquiv_symm_comp g br' hbr'
  have hv := eq_of_universallyInjective_pullback_snd B S hS hX hY
    (isAlgebraicSpace_yoneda B S hS Z) f g hsnd r.carrier r.contained r.toBase
    (yoneda.map ar ≫ yonedaEquiv.symm x) (yoneda.map ar ≫ yonedaEquiv.symm y)
    (yoneda.map br' ≫ yonedaEquiv.symm pz.value)
    (by rw [Category.assoc, Category.assoc, he₁, heZ])
    (by rw [Category.assoc, Category.assoc, ← hcomp, he₁, heZ])
  exact eq_of_map_eq_fieldSpec B S hS hX K r.carrier hK r.contained s r.toBase ar x y
    (map_eq_of_yoneda_map_comp_eq ar hv)

/-- A morphism of algebraic spaces over `S` whose base changes along the members of a Zariski
covering of the target are universally injective is universally injective. -/
private theorem universallyInjective_of_zariskiCover
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (I : Type u) (U : I → Subfunctor Y)
    (hcover : IsZariskiCover B S hS I U)
    (hU : ∀ i, UniversallyInjective B S hS (pullback.snd f (U i).ι)) :
    UniversallyInjective B S hS f := by
  refine universallyInjective_of_injective_fieldSections B S hS f ?_
  intro K _ hK s x y hxy
  have hcomp := yonedaEquiv_symm_comp_eq_of_app_eq f hxy
  have hpoints := (isZariskiCover_iff_iUnion_points B S hS Y hY I U hcover.1).mp hcover
  have hmem : FieldValuedPoint.class B S hS Y
      { carrier := K, contained := hK, toBase := s
        value := yonedaEquiv (yonedaEquiv.symm x ≫ f) } ∈
      ⋃ i, Set.range (pointsMap B S hS (U i).toFunctor (U i).ι) := by
    rw [hpoints]
    exact Set.mem_univ _
  obtain ⟨i, v, hv⟩ := Set.mem_iUnion.mp hmem
  have hrange : Set.range (pointsMap B S hS
      (yoneda.obj (fieldObject (hS := hS) K hK s)) (yonedaEquiv.symm x ≫ f)) ⊆
      Set.range (pointsMap B S hS (U i).toFunctor (U i).ι) := by
    rintro z ⟨z₀, rfl⟩
    obtain ⟨p, rfl⟩ := Quot.exists_rep z₀
    exact ⟨v, hv.trans
      (pointsMap_yoneda_fieldObject_eq B S hS K hK s (yonedaEquiv.symm x ≫ f) p).symm⟩
  obtain ⟨gU, hgU⟩ := (factorsThrough_openSubspace_iff_points B S hS hY
    (isAlgebraicSpace_yoneda B S hS (fieldObject (hS := hS) K hK s)) (U i) (hcover.1 i)
    (yonedaEquiv.symm x ≫ f)).2 hrange
  exact yonedaEquiv.symm.injective (eq_of_universallyInjective_pullback_snd B S hS hX hY
    (hcover.1 i).1 f (U i).ι (hU i) K hK s (yonedaEquiv.symm x) (yonedaEquiv.symm y) gU
    hgU.symm (hcomp.symm.trans hgU.symm))

/-! ### The statement of Stacks 03MX -/

/-- **Stacks 03MX.** For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the
following are equivalent: `f` is universally injective; the base change `Z ×_Y X ⟶ Z` of `f`
along every morphism from a scheme over `S` is universally injective; the same for every
morphism from an affine scheme over `S`; the same for one morphism from a scheme over `S`
which is surjective; and the base change of `f` along each member of some Zariski covering of
`Y` is universally injective. -/
@[stacks 03MX]
theorem universallyInjective_tfae {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [UniversallyInjective B S hS f,
        ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
          UniversallyInjective B S hS (pullback.snd f g),
        ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
            UniversallyInjective B S hS (pullback.snd f g),
        ∃ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
          IsSurjective B S hS g ∧ UniversallyInjective B S hS (pullback.snd f g),
        ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
          ∀ i, UniversallyInjective B S hS (pullback.snd f (U i).ι)] := by
  tfae_have 1 → 2 := fun h Z g ↦ universallyInjective_pullback_snd B S hS hX hY
    (isAlgebraicSpace_yoneda B S hS Z) f g h
  tfae_have 2 → 3 := fun h Z g _ ↦ h Z g
  tfae_have 3 → 1 := universallyInjective_of_affine_scheme_tests B S hS hX hY f
  tfae_have 1 → 4 := by
    intro h
    obtain ⟨Z, g, hgs, -⟩ := hY.exists_atlas
    exact ⟨Z, g, (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY Z g).mp hgs,
      universallyInjective_pullback_snd B S hS hX hY
        (isAlgebraicSpace_yoneda B S hS Z) f g h⟩
  tfae_have 4 → 1 := fun ⟨Z, g, hgs, hsnd⟩ ↦
    universallyInjective_of_surjective_scheme_test B S hS hX hY f Z g hgs hsnd
  tfae_have 1 → 5 := fun h ↦ ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hY,
    fun _ ↦ universallyInjective_pullback_snd B S hS hX hY (isOpenSubspace_top hY).1 f _ h⟩
  tfae_have 5 → 1 := fun ⟨I, U, hcover, hU⟩ ↦
    universallyInjective_of_zariskiCover B S hS hX hY f I U hcover hU
  tfae_finish

end AlgebraicGeometry.Space

end
