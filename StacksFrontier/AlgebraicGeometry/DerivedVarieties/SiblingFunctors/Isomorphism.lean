module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.NegativeObjects
public import StacksCore.Tactic.StacksAttribute

/-!
# Isomorphism of sibling functors

Fully faithful sibling exact functors out of the bounded derived category of an abelian category
are naturally isomorphic, provided the abelian category has enough negative objects. The
comparison is built one cohomological band at a time: on objects concentrated in a single degree
it is the shift of the comparison on the heart, and the band is widened by one degree using a
negative object in the top degree, whose vanishing Hom groups make the extension unique.

## Main definitions

* `AlgebraicGeometry.HasEnoughNegativeObjects`: every object admits an epimorphism from an object
  to which it has no nonzero morphisms.

## Main results

* `AlgebraicGeometry.iso_of_areSiblings_of_fullyFaithful`: a natural isomorphism between sibling
  functors when the first is fully faithful.

## Implementation notes

The source defines enough negative objects immediately before the proposition; it is recorded
here as a predicate because no separate tag states that definition. Vanishing of a Hom group is
expressed by its being a subsingleton, and the conclusion is propositional existence of a natural
isomorphism.

## References

* [Stacks Project, Tag 0FZW](https://stacks.math.columbia.edu/tag/0FZW)
* [Orlov-K3, Proposition 2.16]
* [Canonaco-Stellari]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe w v v' u u'

namespace AlgebraicGeometry

/-- Extending an objectwise comparison from a class `P` to a larger class `Q`: if every pair of
`Q`-objects is separated by a map to a `P`-object, and every map from a `Q`-object to a
`P`-object lifts the comparison, then the comparison extends to `Q`, naturally. -/
private lemma exists_comparison_of_separating_maps
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasBinaryBiproducts C]
    (F G : C ⥤ D) (P Q : C → Prop)
    (c : ∀ X, P X → (F.obj X ≅ G.obj X))
    (hc : ∀ X Y (hX : P X) (hY : P Y) (f : X ⟶ Y),
      F.map f ≫ (c Y hY).hom = (c X hX).hom ≫ G.map f)
    (hP : ∀ X Y, P X → P Y → P (X ⊞ Y))
    (hsep : ∀ X Z, Q X → Q Z → ∃ (Y : C) (_ : P Y) (p : Z ⟶ Y),
      Function.Injective (fun f : F.obj X ⟶ G.obj Z => f ≫ G.map p))
    (hlift : ∀ X Y, Q X → ∀ hY : P Y, ∀ f : X ⟶ Y,
      ∃ e : F.obj X ≅ G.obj X, F.map f ≫ (c Y hY).hom = e.hom ≫ G.map f) :
    ∃ d : ∀ X, Q X → (F.obj X ≅ G.obj X),
      (∀ X Y (hX : Q X) (hY : P Y) (f : X ⟶ Y),
        F.map f ≫ (c Y hY).hom = (d X hX).hom ≫ G.map f) ∧
      (∀ X Y (hX : Q X) (hY : Q Y) (f : X ⟶ Y),
        F.map f ≫ (d Y hY).hom = (d X hX).hom ≫ G.map f) := by
  classical
  have hext (X : C) (hX : Q X) : ∃ e : F.obj X ≅ G.obj X,
      ∀ Y (hY : P Y) (f : X ⟶ Y),
        F.map f ≫ (c Y hY).hom = e.hom ≫ G.map f := by
    obtain ⟨Y₀, hY₀, p, hp⟩ := hsep X X hX hX
    obtain ⟨e, he⟩ := hlift X Y₀ hX hY₀ p
    refine ⟨e, ?_⟩
    intro Y hY f
    obtain ⟨e', he'⟩ := hlift X (Y₀ ⊞ Y) hX (hP Y₀ Y hY₀ hY)
      (biprod.lift p f)
    have hproj {Z : C} (hZ : P Z) (q : Y₀ ⊞ Y ⟶ Z) :
        F.map (biprod.lift p f ≫ q) ≫ (c Z hZ).hom =
          e'.hom ≫ G.map (biprod.lift p f ≫ q) := by
      rw [F.map_comp, G.map_comp, Category.assoc, hc _ _ (hP Y₀ Y hY₀ hY) hZ q,
        ← Category.assoc, he', Category.assoc]
    have hp' := hproj hY₀ biprod.fst
    simp only [biprod.lift_fst] at hp'
    have ee : e'.hom = e.hom := hp (hp'.symm.trans he)
    simpa only [biprod.lift_snd, ee] using hproj hY biprod.snd
  choose d hd using hext
  refine ⟨d, fun X Y hX hY f => hd X hX Y hY f, ?_⟩
  intro X Z hX hZ f
  obtain ⟨Y, hY, p, hp⟩ := hsep X Z hX hZ
  apply hp
  dsimp only
  rw [Category.assoc, ← hd Z hZ Y hY p, ← Category.assoc, ← F.map_comp,
    hd X hX Y hY (f ≫ p), G.map_comp, Category.assoc]

/-- A fully faithful functor sends a Hom group that is a subsingleton, up to isomorphisms of the
source and target, to a subsingleton. -/
private lemma fullyFaithful_hom_subsingleton_of_iso
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (G : C ⥤ D) [G.Full] [G.Faithful]
    {X X' Y Y' : C} (eX : X' ≅ X) (eY : Y ≅ Y')
    (h : Subsingleton (X ⟶ Y)) : Subsingleton (G.obj X' ⟶ G.obj Y') := by
  have h' : Subsingleton (X' ⟶ Y') := by
    constructor
    intro f g
    apply (cancel_epi eX.inv).1
    exact (cancel_mono eY.inv).1 (by
      simpa only [Category.assoc] using
        h.elim (eX.inv ≫ f ≫ eY.inv) (eX.inv ≫ g ≫ eY.inv))
  refine ⟨fun f g => ?_⟩
  calc
    f = G.map (G.preimage f) := (G.map_preimage f).symm
    _ = G.map (G.preimage g) := congrArg G.map (h'.elim _ _)
    _ = g := G.map_preimage g

/-- A fully faithful functor sends a subsingleton Hom group to a subsingleton, after transporting
the target along an isomorphism in the target category. -/
private lemma fullyFaithful_hom_subsingleton_of_targetIso
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (G : C ⥤ D) [G.Full] [G.Faithful] {X Y : C} {Z : D}
    (e : G.obj Y ≅ Z) (h : Subsingleton (X ⟶ Y)) :
    Subsingleton (G.obj X ⟶ Z) := by
  have h' := fullyFaithful_hom_subsingleton_of_iso G (Iso.refl X) (Iso.refl Y) h
  exact ⟨fun f g => (cancel_mono e.inv).1 (h'.elim _ _)⟩

/-- For `X` bounded above by `b` and `Y` bounded below by `b`, morphisms `X` to `Y` vanish as soon
as morphisms out of the truncation of `X` in degrees at least `b` do. -/
private lemma hom_subsingleton_of_truncGE_vanish
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {b : ℤ} (X Y : DerivedCategory A)
    [X.IsLE b] [Y.IsGE b]
    (h : Subsingleton (((DerivedCategory.TStructure.t (C := A)).truncGE b).obj X ⟶ Y)) :
    Subsingleton (X ⟶ Y) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := (t.triangleLEGE (b - 1) b (by omega)).obj X
  have hT : T ∈ distTriang (DerivedCategory A) :=
    t.triangleLEGE_distinguished (b - 1) b (by omega) X
  have hLE : t.IsLE ((t.truncLE (b - 1)).obj X) (b - 1) := by
    infer_instance
  constructor
  intro f g
  have hz : T.mor₁ ≫ (f - g) = 0 := by
    rw [t.zero_of_isLE_of_isGE (T.mor₁ ≫ (f - g)) (b - 1) b (by omega) hLE
      (show t.IsGE Y b from inferInstance)]
  obtain ⟨c, hc⟩ := T.yoneda_exact₂ hT (f - g) hz
  have hc0 := h.elim c 0
  have hfg : f - g = 0 := by
    rw [hc, hc0]
    dsimp [T]
    exact comp_zero
  exact sub_eq_zero.mp hfg

/-- Morphisms from an object bounded above by `a` to an object bounded below by `b` vanish when
`a < b`. -/
private lemma hom_subsingleton_of_strict_tstructure_gap
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {X Y : DerivedCategory A} {a b : ℤ} [X.IsLE a] [Y.IsGE b]
    (hab : a < b) : Subsingleton (X ⟶ Y) := by
  refine ⟨fun f g => ?_⟩
  have hf := (DerivedCategory.TStructure.t (C := A)).zero_of_isLE_of_isGE
    f a b hab (by infer_instance) (by infer_instance)
  have hg := (DerivedCategory.TStructure.t (C := A)).zero_of_isLE_of_isGE
    g a b hab (by infer_instance) (by infer_instance)
  rw [hf, hg]

/-- Isomorphisms of the first and third vertices of two distinguished triangles, compatible with
the connecting maps, extend to an isomorphism of the second vertices. -/
private lemma exists_iso_middle_of_triangle_endpoints
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {T T' : Triangle D} (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (e₁ : T.obj₁ ≅ T'.obj₁) (e₃ : T.obj₃ ≅ T'.obj₃)
    (h₃ : T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' = e₃.hom ≫ T'.mor₃) :
    ∃ e₂ : T.obj₂ ≅ T'.obj₂,
      T.mor₁ ≫ e₂.hom = e₁.hom ≫ T'.mor₁ ∧
      T.mor₂ ≫ e₃.hom = e₂.hom ≫ T'.mor₂ := by
  obtain ⟨g₂, hg₁, hg₂⟩ :=
    complete_distinguished_triangle_morphism₂ T T' hT hT' e₁.hom e₃.hom h₃
  let φ : T ⟶ T' :=
    { hom₁ := e₁.hom
      hom₂ := g₂
      hom₃ := e₃.hom
      comm₁ := hg₁
      comm₂ := hg₂
      comm₃ := h₃ }
  have : IsIso g₂ := isIso₂_of_isIso₁₃ φ hT hT' inferInstance inferInstance
  exact ⟨asIso g₂, hg₁, hg₂⟩

/-- The same extension, for the two triangles obtained by applying two exact functors to one
distinguished triangle. -/
private lemma exists_iso_middle_of_functor_triangle_endpoints
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F F' : C ⥤ D} [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ]
    [F'.IsTriangulated] {T : Triangle C} (hT : T ∈ distTriang C)
    (e₁ : F.obj T.obj₁ ≅ F'.obj T.obj₁)
    (e₃ : F.obj T.obj₃ ≅ F'.obj T.obj₃)
    (h₃ : (F.mapTriangle.obj T).mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' =
      e₃.hom ≫ (F'.mapTriangle.obj T).mor₃) :
    ∃ e₂ : F.obj T.obj₂ ≅ F'.obj T.obj₂,
      F.map T.mor₁ ≫ e₂.hom = e₁.hom ≫ F'.map T.mor₁ ∧
      F.map T.mor₂ ≫ e₃.hom = e₂.hom ≫ F'.map T.mor₂ :=
  exists_iso_middle_of_triangle_endpoints
    (F.map_distinguished T hT) (F'.map_distinguished T hT) e₁ e₃ h₃

/-- A map out of the second vertex of a distinguished triangle killed by the first map factors
through the third vertex. -/
private lemma factors_through_triangle_of_zero
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) {X : C}
    (f : T.obj₂ ⟶ X) (hf : T.mor₁ ≫ f = 0) :
    ∃ g : T.obj₃ ⟶ X, T.mor₂ ≫ g = f := by
  obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT f hf
  exact ⟨g, hg.symm⟩

/-- Two maps into the second vertex of a distinguished triangle agreeing after the second map are
equal, provided morphisms into the first vertex vanish. -/
private lemma postcomp_hom_subsingleton_of_coyoneda_vanish
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {T : Triangle D} (hT : T ∈ distTriang D) {X : D}
    (h : Subsingleton (X ⟶ T.obj₁)) {f g : X ⟶ T.obj₂}
    (hfg : f ≫ T.mor₂ = g ≫ T.mor₂) : f = g := by
  have hz : (f - g) ≫ T.mor₂ = 0 := by
    rw [Preadditive.sub_comp, hfg, sub_self]
  obtain ⟨c, hc⟩ := T.coyoneda_exact₂ hT (f - g) hz
  have hc0 := h.elim c 0
  have hfg' : f - g = 0 := by
    rw [hc, hc0]
    exact zero_comp
  exact sub_eq_zero.mp hfg'

/-- Truncation below `b` does not change cohomology in degree `b`. -/
private lemma homology_map_truncGE_isIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : DerivedCategory A) (b : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor A b).map
      (((DerivedCategory.TStructure.t (C := A)).truncGEπ b).app X)) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := (t.triangleLEGE (b - 1) b (by omega)).obj X
  have hT : T ∈ distTriang (DerivedCategory A) :=
    t.triangleLEGE_distinguished (b - 1) b (by omega) X
  have hLE : T.obj₁.IsLE (b - 1) := by
    show t.IsLE ((t.truncLE (b - 1)).obj X) (b - 1)
    infer_instance
  have : T.obj₁.IsLE (b - 1) := hLE
  have hL0 : IsZero ((DerivedCategory.homologyFunctor A b).obj T.obj₁) := by
    apply DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) b (by omega)
  have hL1 : IsZero ((DerivedCategory.homologyFunctor A (b + 1)).obj T.obj₁) := by
    apply DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) (b + 1) (by omega)
  have hmono : Mono ((DerivedCategory.homologyFunctor A b).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT b]
    exact hL0.eq_of_src _ _
  have hepi : Epi ((DerivedCategory.homologyFunctor A b).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT b (b + 1) (by omega)]
    exact hL1.eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor A b).map T.mor₂) := hmono
  have : Epi ((DerivedCategory.homologyFunctor A b).map T.mor₂) := hepi
  have : IsIso ((DerivedCategory.homologyFunctor A b).map T.mor₂) :=
    isIso_of_mono_of_epi _
  show IsIso ((DerivedCategory.homologyFunctor A b).map T.mor₂)
  exact this

/-- For `X` bounded above by `b`, the truncation of `X` in degrees at least `b` is the degree-`b`
cohomology of `X` placed in degree `b`. -/
private noncomputable def truncGEIsoSingleHomology
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : DerivedCategory A) (b : ℤ) [X.IsLE b] :
    ((DerivedCategory.TStructure.t (C := A)).truncGE b).obj X ≅
      (DerivedCategory.singleFunctor A b).obj ((DerivedCategory.homologyFunctor A b).obj X) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let Z := (t.truncGE b).obj X
  have hGE : Z.IsGE b := by infer_instance
  have hLE : Z.IsLE b := by infer_instance
  let hExists := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Z b
  let Y := Classical.choose hExists
  let eZ : Z ≅ (DerivedCategory.singleFunctor A b).obj Y :=
    Classical.choice (Classical.choose_spec hExists)
  let hπ := homology_map_truncGE_isIso X b
  have : IsIso ((DerivedCategory.homologyFunctor A b).map ((t.truncGEπ b).app X)) := hπ
  let eπ : (DerivedCategory.homologyFunctor A b).obj X ≅
      (DerivedCategory.homologyFunctor A b).obj Z :=
    asIso ((DerivedCategory.homologyFunctor A b).map ((t.truncGEπ b).app X))
  let eH : (DerivedCategory.homologyFunctor A b).obj X ≅ Y :=
    eπ ≪≫ (DerivedCategory.homologyFunctor A b).mapIso eZ ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A b).app Y
  exact eZ ≪≫ (DerivedCategory.singleFunctor A b).mapIso eH.symm

/-- For `X` bounded above by `b`, morphisms from `X` to `N` placed in degree `b` vanish as soon as
morphisms from the degree-`b` cohomology of `X` to `N` do. -/
private lemma hom_subsingleton_of_top_homology_vanish
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {X : DerivedCategory A} {b : ℤ} [X.IsLE b] (N : A)
    (h : Subsingleton ((DerivedCategory.homologyFunctor A b).obj X ⟶ N)) :
    Subsingleton (X ⟶ (DerivedCategory.singleFunctor A b).obj N) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let Z := (t.truncGE b).obj X
  have hSingle : Subsingleton
      ((DerivedCategory.singleFunctor A b).obj ((DerivedCategory.homologyFunctor A b).obj X) ⟶
        (DerivedCategory.singleFunctor A b).obj N) :=
    fullyFaithful_hom_subsingleton_of_iso (DerivedCategory.singleFunctor A b)
      (Iso.refl _) (Iso.refl _) h
  have hZ : Subsingleton (Z ⟶ (DerivedCategory.singleFunctor A b).obj N) :=
    fullyFaithful_hom_subsingleton_of_iso (𝟭 (DerivedCategory A))
      (truncGEIsoSingleHomology X b) (Iso.refl _) hSingle
  exact hom_subsingleton_of_truncGE_vanish X _ hZ

/-- The comparison of two exact functors on a shift of a degree-zero object, obtained by shifting
the natural isomorphism between their restrictions to the heart. -/
private noncomputable def shiftedComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    {F F' : DerivedCategory.Bounded A ⥤ D}
    [F.CommShift ℤ] [F'.CommShift ℤ]
    (α : boundedSingleFunctor A ⋙ F ≅
      boundedSingleFunctor A ⋙ F') (n : ℤ) (X : A) :
    F.obj ((boundedSingleFunctor A).obj X⟦n⟧) ≅
      F'.obj ((boundedSingleFunctor A).obj X⟦n⟧) :=
  (F.commShiftIso n).app ((boundedSingleFunctor A).obj X) ≪≫
    (shiftFunctor D n).mapIso (α.app X) ≪≫
      ((F'.commShiftIso n).app ((boundedSingleFunctor A).obj X)).symm

/-- The shifted comparison commutes with morphisms between shifts of degree-zero objects. -/
private lemma shiftedComparison_naturality
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    {F F' : DerivedCategory.Bounded A ⥤ D}
    [F.CommShift ℤ] [F'.CommShift ℤ]
    (α : boundedSingleFunctor A ⋙ F ≅
      boundedSingleFunctor A ⋙ F') (n : ℤ) (X Y : A)
    (f : ((boundedSingleFunctor A).obj X)⟦n⟧ ⟶
      ((boundedSingleFunctor A).obj Y)⟦n⟧) :
    F.map f ≫ (shiftedComparison α n Y).hom =
      (shiftedComparison α n X).hom ≫ F'.map f := by
  let B := boundedSingleFunctor A
  let hB : B.FullyFaithful := Functor.FullyFaithful.ofCompFaithful
    ((Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor A 0)).ofIso
      (boundedSingleFunctorCompιIso A).symm)
  have : B.Full := hB.full
  obtain ⟨g, rfl⟩ := (shiftFunctor (DerivedCategory.Bounded A) n).map_surjective f
  let g₀ := B.preimage g
  have hmap : B.map g₀ = g := B.map_preimage g
  rw [← hmap]
  dsimp [shiftedComparison]
  rw [F.commShiftIso_hom_naturality_assoc]
  have hα : F.map (B.map g₀) ≫ α.hom.app Y =
      α.hom.app X ≫ F'.map (B.map g₀) := by
    simpa only [Functor.comp_map] using α.hom.naturality g₀
  rw [← Functor.map_comp_assoc, hα, Functor.map_comp_assoc, F'.commShiftIso_inv_naturality]
  simp only [Category.assoc]

/-- An abelian category has enough negative objects if every object `X` admits an epimorphism
from some `N` such that every morphism from `X` to `N` is zero. -/
public def HasEnoughNegativeObjects (A : Type u) [Category.{v} A] : Prop :=
  ∀ X : A, ∃ (N : A) (f : N ⟶ X), Epi f ∧ Subsingleton (X ⟶ N)

/-- From enough negative objects, an epimorphism onto `X` from an object receiving no nonzero map
from either `X` or a prescribed second object `Y`. -/
private lemma exists_negative_epimorphism_pair
    {A : Type u} [Category.{v} A] [Abelian A]
    (hA : HasEnoughNegativeObjects A) (X Y : A) :
    ∃ (N : A) (p : N ⟶ X), Epi p ∧
      Subsingleton (X ⟶ N) ∧ Subsingleton (Y ⟶ N) := by
  obtain ⟨N, p, hp, hN⟩ := hA (X ⊞ Y)
  have : Epi p := hp
  have hpX : Epi (p ≫ (biprod.fst : X ⊞ Y ⟶ X)) := epi_comp _ _
  refine ⟨N, p ≫ biprod.fst, hpX, ?_, ?_⟩
  · constructor
    intro f g
    have heq := hN.elim (biprod.desc f 0) (biprod.desc g 0)
    simpa using congrArg (fun q => (biprod.inl : X ⟶ X ⊞ Y) ≫ q) heq
  · constructor
    intro f g
    have heq := hN.elim (biprod.desc 0 f) (biprod.desc 0 g)
    simpa using congrArg (fun q => (biprod.inr : Y ⟶ X ⊞ Y) ≫ q) heq

/-- A negative object in degree `b` mapping to a bounded object, epimorphically on degree-`b`
cohomology. -/
private lemma exists_negative_epimorphic_map
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (hA : HasEnoughNegativeObjects A) (K : DerivedCategory.Bounded A) (b : ℤ) :
    ∃ (N : A) (g : (DerivedCategory.singleFunctor A b).obj N ⟶ K.obj),
      Epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).inv.app N ≫
        (DerivedCategory.homologyFunctor A b).map g) ∧
      Subsingleton (((DerivedCategory.homologyFunctor A b).obj K.obj) ⟶ N) := by
  let Z : DerivedCategory.Bounded A :=
    ⟨0, ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩⟩
  have hZ : IsZero (Z.obj) := isZero_zero _
  have hHZ : IsZero ((DerivedCategory.homologyFunctor A b).obj Z.obj) :=
    (DerivedCategory.homologyFunctor A b).map_isZero hZ
  obtain ⟨N, g, hg, hN, _⟩ := exists_negative_epimorphic_lift_comp_eq_zero
    (fun X ↦ hA X) K Z 0 b hHZ
  exact ⟨N, g, hg, hN⟩

/-- The same negative object, chosen so that in addition a prescribed object `Y` has no nonzero
map to it. -/
private lemma exists_negative_epimorphic_map_with_second_vanish
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (hA : HasEnoughNegativeObjects A) (K : DerivedCategory.Bounded A)
    (b : ℤ) (Y : A) :
    ∃ (N : A) (g : (DerivedCategory.singleFunctor A b).obj N ⟶ K.obj),
      Epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).inv.app N ≫
        (DerivedCategory.homologyFunctor A b).map g) ∧
      Subsingleton (((DerivedCategory.homologyFunctor A b).obj K.obj) ⟶ N) ∧
      Subsingleton (Y ⟶ N) := by
  obtain ⟨N₀, g₀, hg₀, hN₀⟩ := exists_negative_epimorphic_map hA K b
  obtain ⟨N, p, hp, hN₀N, hYN⟩ := exists_negative_epimorphism_pair hA N₀ Y
  let H := DerivedCategory.homologyFunctor A b
  let η := DerivedCategory.singleFunctorCompHomologyFunctorIso A b
  let q₀ : N₀ ⟶ H.obj K.obj := η.inv.app N₀ ≫ H.map g₀
  let g := (DerivedCategory.singleFunctor A b).map p ≫ g₀
  have hq₀ : Epi q₀ := hg₀
  have hq : Epi (η.inv.app N ≫ H.map g) := by
    have hn : η.inv.app N ≫ H.map ((DerivedCategory.singleFunctor A b).map p) =
        p ≫ η.inv.app N₀ := by
      have hnat := NatIso.naturality_2 η p
      simpa [Functor.comp_map, Category.assoc, Functor.id_map, Iso.inv_hom_id_app] using
        (congrArg (fun z => η.inv.app N ≫ z) hnat).symm
    have hcomp : η.inv.app N ≫ H.map g = p ≫ q₀ := by
      calc
        η.inv.app N ≫ H.map g =
            (η.inv.app N ≫ H.map ((DerivedCategory.singleFunctor A b).map p)) ≫
              H.map g₀ := by
          simp [g, Functor.map_comp, Category.assoc]
        _ = (p ≫ η.inv.app N₀) ≫ H.map g₀ :=
          congrArg (fun q => q ≫ H.map g₀) hn
        _ = p ≫ q₀ := by simp [q₀, Category.assoc]
    rw [hcomp]
    exact epi_comp p q₀
  exact ⟨N, g, hq, ⟨fun f g => (cancel_epi q₀).1 (hN₀N.elim _ _)⟩, hYN⟩

/-- An object of the abelian category placed in degree `b`, as a bounded derived object. -/
private noncomputable abbrev boundedSingleAt
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (N : A) (b : ℤ) : DerivedCategory.Bounded A :=
  ⟨(DerivedCategory.singleFunctor A b).obj N,
    ⟨b, inferInstance⟩, ⟨b, inferInstance⟩⟩

/-- An object placed in degree `b` has cohomology only in degree `b`. -/
private lemma boundedSingleAt_isGE_isLE
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] (N : A) (b : ℤ) :
    (boundedSingleAt N b).obj.IsGE b ∧ (boundedSingleAt N b).obj.IsLE b :=
  ⟨by dsimp [boundedSingleAt]; infer_instance, by dsimp [boundedSingleAt]; infer_instance⟩

/-- The shift by `-b` of a degree-zero object is the same object placed in degree `b`. -/
private noncomputable def boundedSingleShiftIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (N : A) (b : ℤ) :
    ((boundedSingleFunctor A).obj N)⟦-b⟧ ≅ boundedSingleAt N b :=
  ObjectProperty.isoMk _ <|
    ((DerivedCategory.Bounded.ι.commShiftIso (-b)).app
        ((boundedSingleFunctor A).obj N) ≪≫
      (shiftFunctor (DerivedCategory A) (-b)).mapIso
        ((boundedSingleFunctorCompιIso A).app N) ≪≫
      ((DerivedCategory.singleFunctors A).shiftIso (-b) b 0 (by omega)).app N)

/-- The shift by `n` of an objectwise comparison between two functors commuting with the shift. -/
private def comparisonShift
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    {X : C} (e : F.obj X ≅ G.obj X) (n : ℤ) : F.obj (X⟦n⟧) ≅ G.obj (X⟦n⟧) :=
  (F.commShiftIso n).app X ≪≫ (shiftFunctor D n).mapIso e ≪≫
    ((G.commShiftIso n).app X).symm

/-- Transporting an objectwise comparison along an isomorphism commutes with shifting it. -/
private lemma comparisonShift_transport
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    {X Y : C} (e : F.obj Y ≅ G.obj Y) (i : X ≅ Y) (n : ℤ) :
    comparisonShift (F.mapIso i ≪≫ e ≪≫ (G.mapIso i).symm) n =
      F.mapIso ((shiftFunctor C n).mapIso i) ≪≫ comparisonShift e n ≪≫
        (G.mapIso ((shiftFunctor C n).mapIso i)).symm := by
  ext
  simp [comparisonShift, F.commShiftIso_hom_naturality_assoc,
    G.commShiftIso_inv_naturality]

/-- Shifting an objectwise comparison twice is shifting it once by the sum. -/
private lemma comparisonShift_add
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    {X : C} (e : F.obj X ≅ G.obj X) (n m : ℤ) :
    F.mapIso ((shiftFunctorAdd C n m).app X) ≪≫
        comparisonShift (comparisonShift e n) m ≪≫
          (G.mapIso ((shiftFunctorAdd C n m).app X)).symm =
      comparisonShift e (n + m) := by
  ext
  simp [comparisonShift, F.commShiftIso_add, G.commShiftIso_add,
    Functor.CommShift.isoAdd, Functor.CommShift.isoAdd', shiftFunctorAdd'_eq_shiftFunctorAdd,
    ← NatTrans.naturality_assoc]

/-- A bounded object concentrated in degree `b`, presented as the shift by `-b` of a degree-zero
object. -/
private def pureIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : DerivedCategory.Bounded A) (b : ℤ) [X.obj.IsGE b] [X.obj.IsLE b] :
    Σ N : A, X ≅ ((boundedSingleFunctor A).obj N)⟦-b⟧ := by
  let h := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X.obj b
  exact ⟨h.choose, ObjectProperty.isoMk _ h.choose_spec.some ≪≫
    (boundedSingleShiftIso h.choose b).symm⟩

/-- The comparison of two exact functors at a bounded object concentrated in one degree. -/
private def pureComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    {F G : DerivedCategory.Bounded A ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    (X : DerivedCategory.Bounded A) (b : ℤ) [X.obj.IsGE b] [X.obj.IsLE b] :
    F.obj X ≅ G.obj X :=
  F.mapIso (pureIso X b).2 ≪≫ shiftedComparison α (-b) (pureIso X b).1 ≪≫
    (G.mapIso (pureIso X b).2).symm

/-- The comparison at a concentrated object may be computed from any presentation of it as a
shifted degree-zero object. -/
private lemma pureComparison_eq
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    {F G : DerivedCategory.Bounded A ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    (X : DerivedCategory.Bounded A) (b : ℤ) [X.obj.IsGE b] [X.obj.IsLE b]
    (N : A) (i : X ≅ ((boundedSingleFunctor A).obj N)⟦-b⟧) :
    pureComparison α X b = F.mapIso i ≪≫ shiftedComparison α (-b) N ≪≫
      (G.mapIso i).symm := by
  have hn := shiftedComparison_naturality α (-b) (pureIso X b).1 N
    ((pureIso X b).2.inv ≫ i.hom)
  ext
  dsimp [pureComparison]
  simp only [Functor.map_comp] at hn
  have hh := congrArg (fun f => F.map (pureIso X b).2.hom ≫ f ≫ G.map i.inv) hn
  simpa [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc] using hh.symm

/-- The comparison at concentrated objects is natural in those objects. -/
private lemma pureComparison_naturality
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    {F G : DerivedCategory.Bounded A ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    (X Y : DerivedCategory.Bounded A) (b : ℤ)
    [X.obj.IsGE b] [X.obj.IsLE b] [Y.obj.IsGE b] [Y.obj.IsLE b] (f : X ⟶ Y) :
    F.map f ≫ (pureComparison α Y b).hom =
      (pureComparison α X b).hom ≫ G.map f := by
  have hn := shiftedComparison_naturality α (-b) (pureIso X b).1 (pureIso Y b).1
    ((pureIso X b).2.inv ≫ f ≫ (pureIso Y b).2.hom)
  have hh := congrArg (fun z => F.map (pureIso X b).2.hom ≫ z ≫
    G.map (pureIso Y b).2.inv) hn
  simpa [pureComparison, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Category.assoc] using hh

/-- Morphisms of bounded derived objects vanish as soon as the corresponding morphisms in the
ambient derived category do. -/
private lemma bounded_hom_subsingleton_of_ambient
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory.Bounded A) (N : A) (b : ℤ)
    (h : Subsingleton (K.obj ⟶ (DerivedCategory.singleFunctor A b).obj N)) :
    Subsingleton (K ⟶ boundedSingleAt N b) := by
  constructor
  intro f g
  apply (DerivedCategory.Bounded.ι).map_injective
  exact h.elim ((DerivedCategory.Bounded.ι).map f) ((DerivedCategory.Bounded.ι).map g)

/-- A fully faithful functor and a sibling of it send a vanishing Hom group into a degree-`b`
object to a vanishing Hom group, the vanishing being tested in the ambient derived category. -/
private lemma fully_faithful_hom_subsingleton_to_sibling_single
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F F' : DerivedCategory.Bounded A ⥤ D} [F.CommShift ℤ] [F'.CommShift ℤ]
    (hFF : F.FullyFaithful)
    (hObj : ∀ K, Nonempty (F.obj K ≅ F'.obj K))
    (K : DerivedCategory.Bounded A) (N : A) (b : ℤ)
    (h : Subsingleton (K.obj ⟶ (DerivedCategory.singleFunctor A b).obj N)) :
    Subsingleton (F.obj K ⟶ F'.obj (boundedSingleAt N b)) := by
  have : F.Full := hFF.full
  have : F.Faithful := hFF.faithful
  obtain ⟨e⟩ := hObj (boundedSingleAt N b)
  exact fullyFaithful_hom_subsingleton_of_targetIso F e
    (bounded_hom_subsingleton_of_ambient K N b h)

/-- A negative object in the top degree mapping epimorphically on cohomology to `K'`, chosen so
that the two functors see no nonzero map from `K` into it. -/
private lemma exists_negative_map_with_functor_hom_vanish
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F F' : DerivedCategory.Bounded A ⥤ D} [F.CommShift ℤ] [F'.CommShift ℤ]
    (hFF : F.FullyFaithful) (hObj : ∀ K, Nonempty (F.obj K ≅ F'.obj K))
    (hA : HasEnoughNegativeObjects A) (K K' : DerivedCategory.Bounded A)
    {b b' : ℤ} [K.obj.IsLE b] (hbb : b ≤ b') :
    ∃ (N : A) (g : (DerivedCategory.singleFunctor A b').obj N ⟶ K'.obj),
      Epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b').inv.app N ≫
        (DerivedCategory.homologyFunctor A b').map g) ∧
      Subsingleton (F.obj K ⟶ F'.obj (boundedSingleAt N b')) := by
  let H := (DerivedCategory.homologyFunctor A b).obj K.obj
  obtain ⟨N, g, hg, hH', hH⟩ :=
    exists_negative_epimorphic_map_with_second_vanish hA K' b' H
  have hHom : Subsingleton (K.obj ⟶ (DerivedCategory.singleFunctor A b').obj N) := by
    by_cases hEq : b = b'
    · subst b'
      exact hom_subsingleton_of_top_homology_vanish N hH
    · have hlt : b < b' := lt_of_le_of_ne hbb hEq
      have : ((DerivedCategory.singleFunctor A b').obj N).IsGE b' := by infer_instance
      exact hom_subsingleton_of_strict_tstructure_gap hlt
  exact ⟨N, g, hg, fully_faithful_hom_subsingleton_to_sibling_single hFF hObj K N b' hHom⟩

/-- The annihilated negative lift of Tag 0GWG, in the form used below. -/
private lemma exists_negative_epimorphic_map_kills
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (hA : HasEnoughNegativeObjects A) (K K' : DerivedCategory.Bounded A)
    (f : K ⟶ K') (b : ℤ)
    (hK' : IsZero ((DerivedCategory.homologyFunctor A b).obj K'.obj)) :
    ∃ (N : A) (g : (DerivedCategory.singleFunctor A b).obj N ⟶ K.obj),
      Epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).inv.app N ≫
        (DerivedCategory.homologyFunctor A b).map g) ∧
      Subsingleton (((DerivedCategory.homologyFunctor A b).obj K.obj) ⟶ N) ∧
      g ≫ (DerivedCategory.Bounded.ι.map f) = 0 :=
  exists_negative_epimorphic_lift_comp_eq_zero
    (fun X ↦ hA X) K K' f b hK'

/-- Every bounded derived object admits cohomological bounds `a ≤ b`. -/
private lemma bounded_obj_exists_cohomology_bounds
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory.Bounded A) :
    ∃ a b : ℤ, a ≤ b ∧ K.obj.IsGE a ∧ K.obj.IsLE b := by
  obtain ⟨n₀, hn₀⟩ := (DerivedCategory.bounded_iff K.obj).1 K.property
  let n := max n₀ 0
  have hn (i : ℤ) (hi : n ≤ |i|) := hn₀ i (le_trans (le_max_left _ _) hi)
  refine ⟨-(n + 1), n + 1, by omega, ?_, ?_⟩
  · rw [DerivedCategory.isGE_iff]
    intro i hi
    have hi0 : i ≤ 0 := by omega
    have hiabs : n ≤ |i| := by rw [abs_of_nonpos hi0]; omega
    exact hn i hiabs
  · rw [DerivedCategory.isLE_iff]
    intro i hi
    have hi0 : 0 ≤ i := by omega
    have hiabs : n ≤ |i| := by rw [abs_of_nonneg hi0]; omega
    exact hn i hiabs

/-- In a distinguished triangle whose first vertex is concentrated in degree `b` and maps
epimorphically on degree-`b` cohomology, the third vertex loses the top degree. -/
private lemma distinguished_triangle_third_bounds
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (T : Triangle (DerivedCategory.Bounded A))
    (hT : T ∈ distTriang (DerivedCategory.Bounded A)) (a b : ℤ) (hab : a < b)
    (h₁GE : T.obj₁.obj.IsGE b) (h₁LE : T.obj₁.obj.IsLE b)
    (h₂GE : T.obj₂.obj.IsGE a) (h₂LE : T.obj₂.obj.IsLE b)
    (hEpi : Epi ((DerivedCategory.homologyFunctor A b).map
      ((DerivedCategory.Bounded.ι).map T.mor₁))) :
    T.obj₃.obj.IsGE a ∧ T.obj₃.obj.IsLE (b - 1) := by
  let T' := (DerivedCategory.Bounded.ι).mapTriangle.obj T
  have hT' : T' ∈ distTriang (DerivedCategory A) :=
    (DerivedCategory.Bounded.ι).map_distinguished T hT
  have hEpi' : Epi ((DerivedCategory.homologyFunctor A b).map T'.mor₁) := hEpi
  have : T'.obj₁.IsGE b := by simpa [T'] using h₁GE
  have : T'.obj₁.IsLE b := by simpa [T'] using h₁LE
  have : T'.obj₂.IsGE a := by simpa [T'] using h₂GE
  have : T'.obj₂.IsLE b := by simpa [T'] using h₂LE
  constructor
  · rw [DerivedCategory.isGE_iff]
    intro i hi
    exact ((DerivedCategory.homologyFunctor A 0).homologySequence_exact₃ T' hT' i (i + 1)
      rfl).isZero_of_both_isZero (DerivedCategory.isZero_of_isGE T'.obj₂ a i hi)
      (DerivedCategory.isZero_of_isGE T'.obj₁ b (i + 1) (by omega))
  · rw [DerivedCategory.isLE_iff]
    intro i hi
    by_cases hib : i = b
    · subst i
      have hzero : (DerivedCategory.homologyFunctor A b).map T'.mor₂ = 0 :=
        (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T' hT' b).1 hEpi'
      have hEpi₂ : Epi ((DerivedCategory.homologyFunctor A b).map T'.mor₂) :=
        (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T' hT' b (b + 1) rfl).2
          ((DerivedCategory.isZero_of_isLE T'.obj₁ b (b + 1) (by omega)).eq_of_tgt _ _)
      have hY : IsZero ((DerivedCategory.homologyFunctor A b).obj T'.obj₃) := by
        have : Epi ((DerivedCategory.homologyFunctor A b).map T'.mor₂) := hEpi₂
        exact IsZero.of_epi_eq_zero _ hzero
      exact hY
    · exact ((DerivedCategory.homologyFunctor A 0).homologySequence_exact₃ T' hT' i (i + 1)
        rfl).isZero_of_both_isZero (DerivedCategory.isZero_of_isLE T'.obj₂ b i (by omega))
        (DerivedCategory.isZero_of_isLE T'.obj₁ b (i + 1) (by omega))

/-- A map from an object in degree `b` that is epimorphic on degree-`b` cohomology to a bounded
object `X` with cohomology in degrees `a` to `b` completes to a distinguished triangle whose
third vertex has cohomology in degrees `a` to `b - 1`. -/
private lemma exists_triangle_of_epi_homology_map
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {a b : ℤ} (hab : a < b) {X : DerivedCategory.Bounded A}
    (hGE : X.obj.IsGE a) (hLE : X.obj.IsLE b) {N : A}
    (g₀ : (DerivedCategory.singleFunctor A b).obj N ⟶ X.obj)
    (hg₀ : Epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).inv.app N ≫
      (DerivedCategory.homologyFunctor A b).map g₀)) :
    ∃ (g : boundedSingleAt N b ⟶ X) (Y : DerivedCategory.Bounded A) (p : X ⟶ Y)
      (δ : Y ⟶ (boundedSingleAt N b)⟦(1 : ℤ)⟧),
      (DerivedCategory.Bounded.ι).map g = g₀ ∧ Triangle.mk g p δ ∈ distTriang _ ∧
        Y.obj.IsGE a ∧ Y.obj.IsLE (b - 1) := by
  let ι := DerivedCategory.Bounded.ι (C := A)
  let g : boundedSingleAt N b ⟶ X := ι.preimage (X := boundedSingleAt N b) (Y := X) g₀
  have hg : ι.map g = g₀ := ι.map_preimage (X := boundedSingleAt N b) (Y := X) g₀
  obtain ⟨Y, p, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle g
  have hepi : Epi ((DerivedCategory.homologyFunctor A b).map (ι.map g)) := by
    rw [hg]
    exact (epi_comp_iff_of_epi _ _).1 hg₀
  exact ⟨g, Y, p, δ, hg, hT, distinguished_triangle_third_bounds _ hT a b hab
    (boundedSingleAt_isGE_isLE N b).1 (boundedSingleAt_isGE_isLE N b).2 hGE hLE hepi⟩

/-- A distinguished triangle whose first vertex is a negative object in the top degree `b` and
whose cone is bounded above by `b - 1`. -/
private lemma exists_negative_triangle_with_bounded_cone
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (hA : HasEnoughNegativeObjects A) (K : DerivedCategory.Bounded A)
    (a b : ℤ) (hab : a < b) (hGE : K.obj.IsGE a) (hLE : K.obj.IsLE b) :
    ∃ (N : A) (f : boundedSingleAt N b ⟶ K) (Y : DerivedCategory.Bounded A)
      (g : K ⟶ Y) (δ : Y ⟶ (boundedSingleAt N b)⟦(1 : ℤ)⟧),
      Epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).inv.app N ≫
        (DerivedCategory.homologyFunctor A b).map ((DerivedCategory.Bounded.ι).map f)) ∧
      Subsingleton (((DerivedCategory.homologyFunctor A b).obj K.obj) ⟶ N) ∧
      Triangle.mk f g δ ∈ distTriang (DerivedCategory.Bounded A) ∧
      Y.obj.IsGE a ∧ Y.obj.IsLE (b - 1) := by
  have : K.obj.IsLE b := hLE
  obtain ⟨N, f₀, hf₀, hN⟩ := exists_negative_epimorphic_map hA K b
  obtain ⟨f, Y, g, δ, hf, hT, hY⟩ := exists_triangle_of_epi_homology_map hab hGE hLE f₀ hf₀
  exact ⟨N, f, Y, g, δ, by rw [hf]; exact hf₀, hN, hT, hY⟩

section Intervals

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  {F G : DerivedCategory.Bounded A ⥤ D}
  [F.CommShift ℤ] [F.IsTriangulated] [G.CommShift ℤ] [G.IsTriangulated]

/-- Shifting a bounded derived object shifts its lower bound. -/
private lemma bounded_shift_isGE (X : DerivedCategory.Bounded A) (a n b : ℤ)
    [X.obj.IsGE a] (hab : n + b = a) : (X⟦n⟧).obj.IsGE b := by
  have : (DerivedCategory.TStructure.t (C := A)).IsGE (X.obj⟦n⟧) b :=
    (DerivedCategory.TStructure.t (C := A)).isGE_shift X.obj a n b hab
  let e : X.obj⟦n⟧ ≅ (X⟦n⟧).obj :=
    ((DerivedCategory.Bounded.ι.commShiftIso n).app X).symm
  exact (DerivedCategory.TStructure.t (C := A)).isGE_of_iso e b

/-- Shifting a bounded derived object shifts its upper bound. -/
private lemma bounded_shift_isLE (X : DerivedCategory.Bounded A) (a n b : ℤ)
    [X.obj.IsLE a] (hab : n + b = a) : (X⟦n⟧).obj.IsLE b := by
  have : (DerivedCategory.TStructure.t (C := A)).IsLE (X.obj⟦n⟧) b :=
    (DerivedCategory.TStructure.t (C := A)).isLE_shift X.obj a n b hab
  let e : X.obj⟦n⟧ ≅ (X⟦n⟧).obj :=
    ((DerivedCategory.Bounded.ι.commShiftIso n).app X).symm
  exact (DerivedCategory.TStructure.t (C := A)).isLE_of_iso e b

omit [Pretriangulated D] [F.IsTriangulated] [G.IsTriangulated] in
private lemma pureComparison_shift
    (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    (X : DerivedCategory.Bounded A) (b : ℤ) [X.obj.IsGE b] [X.obj.IsLE b]
    [(X⟦(1 : ℤ)⟧).obj.IsGE (b - 1)] [(X⟦(1 : ℤ)⟧).obj.IsLE (b - 1)] :
    pureComparison α (X⟦(1 : ℤ)⟧) (b - 1) = comparisonShift (pureComparison α X b) 1 := by
  let e := (pureIso X b).2
  let N := (pureIso X b).1
  let j := (shiftFunctorAdd (DerivedCategory.Bounded A) (-b) 1).app
    ((boundedSingleFunctor A).obj N)
  have heq : -b + 1 = -(b - 1) := by omega
  let i : X⟦(1 : ℤ)⟧ ≅ ((boundedSingleFunctor A).obj N)⟦-(b - 1)⟧ :=
    (shiftFunctor _ (1 : ℤ)).mapIso e ≪≫ j.symm ≪≫
      eqToIso (congrArg (fun n : ℤ => ((boundedSingleFunctor A).obj N)⟦n⟧) heq)
  rw [pureComparison_eq α _ _ N i]
  unfold pureComparison
  rw [comparisonShift_transport]
  have h := comparisonShift_add (F := F) (G := G) (α.app N) (-b) 1
  have h' : comparisonShift (F := F) (G := G) (α.app N) (-b + 1) =
      F.mapIso j ≪≫ comparisonShift (shiftedComparison α (-b) N) 1 ≪≫
        (G.mapIso j).symm := h.symm
  have hh : shiftedComparison α (-(b - 1)) N =
      F.mapIso (eqToIso (congrArg (fun n : ℤ =>
        ((boundedSingleFunctor A).obj N)⟦n⟧) heq)).symm ≪≫
      comparisonShift (F := F) (G := G) (α.app N) (-b + 1) ≪≫
      G.mapIso (eqToIso (congrArg (fun n : ℤ =>
        ((boundedSingleFunctor A).obj N)⟦n⟧) heq)) := by
    generalize -(b - 1) = k at heq ⊢
    subst k
    ext
    simp [shiftedComparison, comparisonShift]
  rw [hh, h']
  ext
  simp [i, e, j, N]

/-- The property of a bounded derived object of having cohomology only in degrees `a` to `b`. -/
private abbrev InBand (a b : ℤ) (X : DerivedCategory.Bounded A) : Prop :=
  X.obj.IsGE a ∧ X.obj.IsLE b

/-- Widening the band preserves the property of lying in it. -/
private lemma inBand_mono {a b a' b' : ℤ} {X : DerivedCategory.Bounded A}
    (h : InBand a b X) (ha : a' ≤ a) (hb : b ≤ b') : InBand a' b' X := by
  have := h.1
  have := h.2
  exact ⟨(DerivedCategory.TStructure.t (C := A)).isGE_of_ge X.obj a' a ha,
    (DerivedCategory.TStructure.t (C := A)).isLE_of_le X.obj b b' hb⟩

/-- An additive functor killing two objects kills their biproduct. -/
private lemma isZero_map_biprod
    {C E : Type*} [Category* C] [Category* E] [Preadditive C] [Preadditive E]
    [HasBinaryBiproducts C] (H : C ⥤ E) [H.Additive] (X Y : C)
    (hX : IsZero (H.obj X)) (hY : IsZero (H.obj Y)) : IsZero (H.obj (X ⊞ Y)) := by
  rw [IsZero.iff_id_eq_zero]
  rw [← H.map_id, ← biprod.total, H.map_add, H.map_comp, H.map_comp,
    hX.eq_of_tgt (H.map biprod.fst) 0, hY.eq_of_tgt (H.map biprod.snd) 0,
    zero_comp, zero_comp, add_zero]

/-- The biproduct of two objects in a band lies in that band. -/
private lemma inBand_biprod {a b : ℤ} (X Y : DerivedCategory.Bounded A)
    (hX : InBand a b X) (hY : InBand a b Y) : InBand a b (X ⊞ Y) := by
  have := hX.1
  have := hX.2
  have := hY.1
  have := hY.2
  constructor
  · rw [DerivedCategory.isGE_iff]
    intro i hi
    exact isZero_map_biprod (DerivedCategory.Bounded.ι ⋙ DerivedCategory.homologyFunctor A i)
      X Y (DerivedCategory.isZero_of_isGE X.obj a i hi)
      (DerivedCategory.isZero_of_isGE Y.obj a i hi)
  · rw [DerivedCategory.isLE_iff]
    intro i hi
    exact isZero_map_biprod (DerivedCategory.Bounded.ι ⋙ DerivedCategory.homologyFunctor A i)
      X Y (DerivedCategory.isZero_of_isLE X.obj b i hi)
      (DerivedCategory.isZero_of_isLE Y.obj b i hi)

/-- A natural comparison of two exact functors on all objects with cohomology in degrees `a` to
`b`, agreeing with the comparison at concentrated objects. -/
private structure IntervalComparison
    (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    (a b : ℤ) where
  app (X : DerivedCategory.Bounded A) : InBand a b X → (F.obj X ≅ G.obj X)
  naturality (X Y : DerivedCategory.Bounded A) (hX : InBand a b X) (hY : InBand a b Y)
    (f : X ⟶ Y) : F.map f ≫ (app Y hY).hom = (app X hX).hom ≫ G.map f
  pure (X : DerivedCategory.Bounded A) (d : ℤ) (ha : a ≤ d) (hb : d ≤ b)
    (hX : InBand a b X) [X.obj.IsGE d] [X.obj.IsLE d] : app X hX = pureComparison α X d

/-- Given a comparison on the band `a` to `b - 1`, the two endpoints of a triangle whose first
vertex is concentrated in degree `b` determine a comparison at its second vertex. -/
private lemma interval_triangle_iso
    {α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G}
    {a b : ℤ} (hab : a < b) (c : IntervalComparison α a (b - 1))
    (T : Triangle (DerivedCategory.Bounded A)) (hT : T ∈ distTriang _)
    [T.obj₁.obj.IsGE b] [T.obj₁.obj.IsLE b] (hY : InBand a (b - 1) T.obj₃) :
    ∃ e : F.obj T.obj₂ ≅ G.obj T.obj₂,
      F.map T.mor₁ ≫ e.hom = (pureComparison α T.obj₁ b).hom ≫ G.map T.mor₁ ∧
      F.map T.mor₂ ≫ (c.app T.obj₃ hY).hom = e.hom ≫ G.map T.mor₂ := by
  have := bounded_shift_isGE T.obj₁ b 1 (b - 1) (by omega)
  have := bounded_shift_isLE T.obj₁ b 1 (b - 1) (by omega)
  have hS : InBand a (b - 1) (T.obj₁⟦(1 : ℤ)⟧) :=
    inBand_mono ⟨inferInstance, inferInstance⟩ (by omega : a ≤ b - 1) le_rfl
  have hnat := c.naturality T.obj₃ _ hY hS T.mor₃
  rw [c.pure _ (b - 1) (by omega) le_rfl hS, pureComparison_shift] at hnat
  apply exists_iso_middle_of_functor_triangle_endpoints hT (pureComparison α T.obj₁ b)
    (c.app T.obj₃ hY)
  have hh := congrArg (fun z => z ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁) hnat
  convert hh using 1
  all_goals simp [comparisonShift, Category.assoc, Functor.mapTriangle]

/-- In the situation above, when the second vertex is also concentrated in degree `b`, the
comparison obtained is the one at concentrated objects. -/
private lemma interval_triangle_pure
    {α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G}
    (hF : F.FullyFaithful) {a b : ℤ} (hab : a < b) (c : IntervalComparison α a (b - 1))
    (T : Triangle (DerivedCategory.Bounded A)) (hT : T ∈ distTriang _)
    [T.obj₁.obj.IsGE b] [T.obj₁.obj.IsLE b] [T.obj₂.obj.IsGE b] [T.obj₂.obj.IsLE b]
    (hY : InBand a (b - 1) T.obj₃) :
    F.map T.mor₂ ≫ (c.app T.obj₃ hY).hom =
      (pureComparison α T.obj₂ b).hom ≫ G.map T.mor₂ := by
  have := hF.full
  have := hF.faithful
  have := hY.2
  have hz : Subsingleton (F.obj T.obj₃ ⟶ G.obj T.obj₂) := by
    apply fullyFaithful_hom_subsingleton_of_targetIso F (pureComparison α T.obj₂ b)
    constructor
    intro f g
    apply DerivedCategory.Bounded.ι.map_injective
    exact (hom_subsingleton_of_strict_tstructure_gap (X := T.obj₃.obj)
      (Y := T.obj₂.obj) (a := b - 1) (b := b) (by omega)).elim _ _
  obtain ⟨e, he₁, he₂⟩ := interval_triangle_iso hab c T hT hY
  obtain ⟨g, hg⟩ := factors_through_triangle_of_zero (F.map_distinguished T hT)
    (e.hom - (pureComparison α T.obj₂ b).hom) (by
      change F.map T.mor₁ ≫ _ = 0
      rw [Preadditive.comp_sub, he₁, pureComparison_naturality α T.obj₁ T.obj₂ b T.mor₁,
        sub_self])
  have : e.hom = (pureComparison α T.obj₂ b).hom := by
    rw [← sub_eq_zero, ← hg, hz.elim g 0]
    exact comp_zero
  rw [he₂, this]

omit [F.IsTriangulated] in
private lemma interval_separating_maps
    (hF : F.FullyFaithful) (hObj : ∀ X, Nonempty (F.obj X ≅ G.obj X))
    (hA : HasEnoughNegativeObjects A) {a b : ℤ} (hab : a < b)
    (X Z : DerivedCategory.Bounded A) (hX : InBand a b X) (hZ : InBand a b Z) :
    ∃ (Y : DerivedCategory.Bounded A) (_ : InBand a (b - 1) Y) (p : Z ⟶ Y),
      Function.Injective (fun f : F.obj X ⟶ G.obj Z => f ≫ G.map p) := by
  have := hX.2
  obtain ⟨N, g₀, hg₀, hvan⟩ := exists_negative_map_with_functor_hom_vanish
    hF hObj hA X Z (b := b) (b' := b) le_rfl
  obtain ⟨g, Y, p, δ, -, hT, hY⟩ := exists_triangle_of_epi_homology_map hab hZ.1 hZ.2 g₀ hg₀
  refine ⟨Y, hY, p, ?_⟩
  intro f g hfg
  exact postcomp_hom_subsingleton_of_coyoneda_vanish
    (G.map_distinguished _ hT) hvan hfg

/-- Every map from an object of the band to an object one degree lower lifts the comparison. -/
private lemma interval_lift_comparison
    {α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G}
    (hA : HasEnoughNegativeObjects A) {a b : ℤ} (hab : a < b)
    (c : IntervalComparison α a (b - 1)) (X Y : DerivedCategory.Bounded A)
    (hX : InBand a b X) (hY : InBand a (b - 1) Y) (f : X ⟶ Y) :
    ∃ e : F.obj X ≅ G.obj X, F.map f ≫ (c.app Y hY).hom = e.hom ≫ G.map f := by
  have := hY.2
  obtain ⟨N, g₀, hg₀, _, hzero⟩ := exists_negative_epimorphic_map_kills hA X Y f b
    (DerivedCategory.isZero_of_isLE Y.obj (b - 1) b (by omega))
  obtain ⟨g, W, p, δ, hg, hT, hW⟩ :=
    exists_triangle_of_epi_homology_map hab hX.1 hX.2 g₀ hg₀
  have hgzero : g ≫ f = 0 := by
    apply DerivedCategory.Bounded.ι.map_injective
    rw [Functor.map_comp, hg, Functor.map_zero]
    exact hzero
  have : (Triangle.mk g p δ).obj₁.obj.IsGE b := (boundedSingleAt_isGE_isLE N b).1
  have : (Triangle.mk g p δ).obj₁.obj.IsLE b := (boundedSingleAt_isGE_isLE N b).2
  obtain ⟨e, _, he⟩ := interval_triangle_iso hab c (Triangle.mk g p δ) hT hW
  obtain ⟨q, hq⟩ := factors_through_triangle_of_zero hT f hgzero
  refine ⟨e, ?_⟩
  change F.map p ≫ (c.app W hW).hom = e.hom ≫ G.map p at he
  change p ≫ q = f at hq
  rw [← hq, F.map_comp, G.map_comp, Category.assoc, c.naturality W Y hW hY q,
    ← Category.assoc, he, Category.assoc]

/-- A comparison on the band `a` to `b - 1` extends to the band `a` to `b`. -/
private lemma intervalComparison_extend
    {α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G}
    (hF : F.FullyFaithful) (hObj : ∀ X, Nonempty (F.obj X ≅ G.obj X))
    (hA : HasEnoughNegativeObjects A) {a b : ℤ} (hab : a < b)
    (c : IntervalComparison α a (b - 1)) : Nonempty (IntervalComparison α a b) := by
  obtain ⟨d, hd, hn⟩ := exists_comparison_of_separating_maps F G
    (InBand a (b - 1)) (InBand a b) c.app c.naturality
    (fun X Y => inBand_biprod X Y)
    (interval_separating_maps hF hObj hA hab)
    (interval_lift_comparison hA hab c)
  refine ⟨{ app := d, naturality := hn, pure := ?_ }⟩
  intro X k hak hkb hX hGE hLE
  by_cases hlt : k < b
  · have hX' : InBand a (b - 1) X :=
      inBand_mono ⟨hGE, hLE⟩ hak (by omega : k ≤ b - 1)
    have hh := hd X X hX hX' (𝟙 X)
    have he : d X hX = c.app X hX' := by
      ext
      simpa using hh.symm
    exact he.trans (c.pure X k hak (by omega) hX')
  · have hk : k = b := by omega
    subst k
    obtain ⟨N, g, Y, p, δ, _, hN, hT, hYge, hYle⟩ :=
      exists_negative_triangle_with_bounded_cone hA X a b hab hX.1 hX.2
    have hY : InBand a (b - 1) Y := ⟨hYge, hYle⟩
    have hvan : Subsingleton (F.obj X ⟶ G.obj (boundedSingleAt N b)) :=
      fully_faithful_hom_subsingleton_to_sibling_single hF hObj X N b
        (hom_subsingleton_of_top_homology_vanish N hN)
    apply Iso.ext
    apply postcomp_hom_subsingleton_of_coyoneda_vanish (G.map_distinguished _ hT) hvan
    have : (Triangle.mk g p δ).obj₁.obj.IsGE b := (boundedSingleAt_isGE_isLE N b).1
    have : (Triangle.mk g p δ).obj₁.obj.IsLE b := (boundedSingleAt_isGE_isLE N b).2
    have : (Triangle.mk g p δ).obj₂.obj.IsGE b := hGE
    have : (Triangle.mk g p δ).obj₂.obj.IsLE b := hLE
    exact (hd X Y hX hY p).symm.trans
      (interval_triangle_pure hF hab c (Triangle.mk g p δ) hT hY)

/-- A comparison exists on every band of the form `a` to `a + n`. -/
private lemma intervalComparison_exists
    {α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G}
    (hF : F.FullyFaithful) (hObj : ∀ X, Nonempty (F.obj X ≅ G.obj X))
    (hA : HasEnoughNegativeObjects A) (a : ℤ) (n : ℕ) :
    Nonempty (IntervalComparison α a (a + n)) := by
  induction n with
  | zero =>
    refine ⟨{ app := fun X hX => ?_, naturality := ?_, pure := ?_ }⟩
    · have := hX.1
      have : X.obj.IsLE a := by simpa using hX.2
      exact pureComparison α X a
    · intro X Y hX hY f
      have := hX.1
      have : X.obj.IsLE a := by simpa using hX.2
      have := hY.1
      have : Y.obj.IsLE a := by simpa using hY.2
      exact pureComparison_naturality α X Y a f
    · intro X k hak hka hX _ _
      have hk : k = a := by omega
      subst k
      rfl
  | succ n ih =>
    obtain ⟨c⟩ := ih
    have heq : a + (n + 1 : ℕ) - 1 = a + n := by push_cast; omega
    exact intervalComparison_extend hF hObj hA (by push_cast; omega)
      (heq ▸ c)

/-- A comparison restricts to any narrower band. -/
private def intervalComparison_restrict
    {α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G}
    {a b a' b' : ℤ} (c : IntervalComparison α a b) (ha : a ≤ a') (hb : b' ≤ b) :
    IntervalComparison α a' b' where
  app X hX := c.app X (inBand_mono hX ha hb)
  naturality X Y hX hY f :=
    c.naturality X Y (inBand_mono hX ha hb) (inBand_mono hY ha hb) f
  pure X d hd hd' hX :=
    c.pure X d (ha.trans hd) (hd'.trans hb) (inBand_mono hX ha hb)

omit [F.IsTriangulated] in
private lemma intervalComparison_app_eq
    {α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G}
    (hF : F.FullyFaithful) (hObj : ∀ X, Nonempty (F.obj X ≅ G.obj X))
    (hA : HasEnoughNegativeObjects A) (a : ℤ) (n : ℕ)
    (c d : IntervalComparison α a (a + n)) (X : DerivedCategory.Bounded A)
    (hX : InBand a (a + n) X) : c.app X hX = d.app X hX := by
  induction n generalizing X with
  | zero =>
    have := hX.1
    have : X.obj.IsLE a := by simpa using hX.2
    exact (c.pure X a le_rfl (by omega) hX).trans (d.pure X a le_rfl (by omega) hX).symm
  | succ n ih =>
    let b : ℤ := a + (n + 1 : ℕ)
    have hab : a < b := by dsimp [b]; omega
    obtain ⟨N, g, Y, p, δ, _, hN, hT, hYge, hYle⟩ :=
      exists_negative_triangle_with_bounded_cone hA X a b hab hX.1 hX.2
    have hYsmall : InBand a (a + n) Y := by
      have heq : b - 1 = a + n := by dsimp [b]; omega
      exact ⟨hYge, heq ▸ hYle⟩
    have hY : InBand a (a + (n + 1 : ℕ)) Y :=
      inBand_mono hYsmall le_rfl (by omega)
    let c' := intervalComparison_restrict c (a' := a) (b' := a + n) le_rfl (by omega)
    let d' := intervalComparison_restrict d (a' := a) (b' := a + n) le_rfl (by omega)
    have heY : c.app Y hY = d.app Y hY := ih c' d' Y hYsmall
    have : X.obj.IsLE b := hX.2
    have hvan : Subsingleton (F.obj X ⟶ G.obj (boundedSingleAt N b)) :=
      fully_faithful_hom_subsingleton_to_sibling_single hF hObj X N b
        (hom_subsingleton_of_top_homology_vanish N hN)
    apply Iso.ext
    apply postcomp_hom_subsingleton_of_coyoneda_vanish (G.map_distinguished _ hT) hvan
    show (c.app X hX).hom ≫ G.map p = (d.app X hX).hom ≫ G.map p
    rw [← c.naturality X Y hX hY p, heY, d.naturality X Y hX hY p]

/-- A comparison exists on every band `a ≤ b`. -/
private lemma intervalComparison_exists_of_le
    {α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G}
    (hF : F.FullyFaithful) (hObj : ∀ X, Nonempty (F.obj X ≅ G.obj X))
    (hA : HasEnoughNegativeObjects A) (a b : ℤ) (hab : a ≤ b) :
    Nonempty (IntervalComparison α a b) := by
  have heq : a + ((b - a).toNat : ℤ) = b := by rw [Int.toNat_of_nonneg (by omega)]; omega
  exact heq ▸ intervalComparison_exists hF hObj hA a (b - a).toNat

omit [F.IsTriangulated] in
private lemma intervalComparison_unique
    {α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G}
    (hF : F.FullyFaithful) (hObj : ∀ X, Nonempty (F.obj X ≅ G.obj X))
    (hA : HasEnoughNegativeObjects A) (a b : ℤ) (hab : a ≤ b)
    (c d : IntervalComparison α a b) (X : DerivedCategory.Bounded A)
    (hX : InBand a b X) : c.app X hX = d.app X hX := by
  have heq : a + ((b - a).toNat : ℤ) = b := by rw [Int.toNat_of_nonneg (by omega)]; omega
  generalize hn : (b - a).toNat = n at heq
  subst b
  exact intervalComparison_app_eq hF hObj hA a n c d X hX

/-- Every bounded derived object lies in a symmetric band from `-n` to `n`. -/
private lemma exists_symmetric_cohomology_bounds (X : DerivedCategory.Bounded A) :
    ∃ n : ℕ, InBand (-(n : ℤ)) n X := by
  obtain ⟨a, b, _, hge, hle⟩ := bounded_obj_exists_cohomology_bounds X
  let n := (|a| + |b|).toNat
  have hn : (n : ℤ) = |a| + |b| := Int.toNat_of_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b))
  have ha := neg_abs_le a
  have hb := le_abs_self b
  have ha' := abs_nonneg a
  have hb' := abs_nonneg b
  refine ⟨n, inBand_mono ⟨hge, hle⟩ ?_ ?_⟩ <;> rw [hn] <;> omega

/-- Assembling the comparisons on all symmetric bands into a natural isomorphism of the two
functors. -/
private lemma exists_iso_of_intervalComparisons
    (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    (hF : F.FullyFaithful) (hObj : ∀ X, Nonempty (F.obj X ≅ G.obj X))
    (hA : HasEnoughNegativeObjects A) : Nonempty (F ≅ G) := by
  classical
  let c (n : ℕ) : IntervalComparison α (-(n : ℤ)) n :=
    (intervalComparison_exists_of_le hF hObj hA (-(n : ℤ)) n (by omega)).some
  let k (X : DerivedCategory.Bounded A) : ℕ := (exists_symmetric_cohomology_bounds X).choose
  have hk (X : DerivedCategory.Bounded A) : InBand (-(k X : ℤ)) (k X) X :=
    (exists_symmetric_cohomology_bounds X).choose_spec
  let e (X : DerivedCategory.Bounded A) := (c (k X)).app X (hk X)
  have he (X : DerivedCategory.Bounded A) (n : ℕ) (hn : k X ≤ n) :
      e X = (c n).app X (inBand_mono (hk X) (by omega) (by omega)) :=
    intervalComparison_unique hF hObj hA (-(k X : ℤ)) (k X) (by omega)
      (c (k X)) (intervalComparison_restrict (c n) (by omega) (by omega)) X (hk X)
  refine ⟨NatIso.ofComponents e ?_⟩
  intro X Y f
  let n := max (k X) (k Y)
  rw [he X n (le_max_left _ _), he Y n (le_max_right _ _)]
  exact (c n).naturality X Y _ _ f

end Intervals

/-- **Stacks Project, Tag 0FZW.** Sibling exact functors from a bounded derived category
are naturally isomorphic if the first is fully faithful and the source abelian category has
enough negative objects. -/
@[stacks 0FZW]
public theorem iso_of_areSiblings_of_fullyFaithful
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D]
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : AreSiblings F F')
    (hF : Nonempty F.FullyFaithful)
    (hA : HasEnoughNegativeObjects A) : Nonempty (F ≅ F') := by
  obtain ⟨α⟩ := h.restrictionIso
  obtain ⟨hF⟩ := hF
  exact exists_iso_of_intervalComparisons α hF h.objIso hA

end AlgebraicGeometry

end
