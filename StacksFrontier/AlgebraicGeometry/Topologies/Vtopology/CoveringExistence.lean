module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.Defs
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.StandardCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.StandardCovering
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII

/-!
# Descent of standard coverings along affine inverse limits

A finite standard covering of an affine inverse limit of affine schemes descends to a standard
covering at a finite stage. This applies to the Zariski, étale, smooth, syntomic and fppf
topologies.

## Main results

* `AlgebraicGeometry.exists_standardZariskiCovering_of_isLimit` descends a standard Zariski
  covering.
* `AlgebraicGeometry.exists_standardEtaleCovering_of_isLimit` descends a standard étale
  covering.
* `AlgebraicGeometry.exists_standardSmoothCovering_of_isLimit` descends a standard smooth
  covering.
* `AlgebraicGeometry.exists_standardSyntomicCovering_of_isLimit` descends a standard syntomic
  covering.
* `AlgebraicGeometry.exists_standardFppfCovering_of_isLimit` descends a standard fppf covering.

## Implementation notes

The indexing category for descent is essentially small relative to the scheme universe,
expressing the set-sized inverse systems of the source. Each covering is descended member by
member: a model of each member is found over some stage by a filtered-colimit argument on rings
of sections, the finitely many stages are refined to a common one, and the surjectivity of the
descended family is recovered from the fact that the basic opens of the chosen sections already
span at that stage.

## References

* [Stacks Project, Tag 049N](https://stacks.math.columbia.edu/tag/049N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe w v u

namespace AlgebraicGeometry

private lemma exists_common_predecessor_of_finite
    {I : Type v} [Category.{v} I] [IsCofiltered I] {J : Type w} [Finite J]
    (i : J → I) : ∃ (k : I), Nonempty (∀ j : J, k ⟶ i j) := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  exact ⟨k, ⟨fun j => (hk (X := i j) (by simp)).some⟩⟩

private lemma exists_eventual_eq_of_filtered_colimit
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (F : J ⥤ Type u) (c : Cocone F) (hc : IsColimit c)
    (i : J) (x y : F.obj i) (h : c.ι.app i x = c.ι.app i y) :
    ∃ (j : J) (f : i ⟶ j), F.map f x = F.map f y :=
  (Types.FilteredColimit.isColimit_eq_iff' hc x y).mp h

private lemma exists_equal_section_stage
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) (s t : Γ(D.obj i, ⊤))
    (h : (c.π.app i).appTop s = (c.π.app i).appTop t) :
    ∃ (j : I) (g : j ⟶ i), (D.map g).appTop s = (D.map g).appTop t := by
  let X : Over (D.obj i) := Over.mk (𝟙 _)
  let Y : Over (D.obj i) := Over.mk (AffineSpace (PUnit.{u + 1}) (D.obj i) ↘ D.obj i)
  have hfst {q : Scheme.{u}} (p : q ⟶ D.obj i) :
      pullback.fst X.hom p = pullback.snd X.hom p ≫ p := by
    simpa [X] using (pullback.condition (f := X.hom) (g := p))
  let f (s : Γ(D.obj i, ⊤)) : X ⟶ Y :=
    Over.homMk (AffineSpace.homOfVector (𝟙 (D.obj i)) (fun _ : PUnit.{u + 1} => s))
      (AffineSpace.homOfVector_over _ _)
  have hf (q : Scheme.{u}) (p : q ⟶ D.obj i)
      (hp : p.appTop s = p.appTop t) :
      (Over.pullback p).map (f s) = (Over.pullback p).map (f t) := by
    ext1
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst]
      rw [hfst p]
      apply AffineSpace.hom_ext
      · simp [f, Category.assoc]
      · intro k
        change (pullback.snd X.hom p).appTop (p.appTop
          ((AffineSpace.homOfVector (𝟙 (D.obj i)) (fun _ : PUnit.{u + 1} => s)).appTop _)) =
          (pullback.snd X.hom p).appTop (p.appTop
          ((AffineSpace.homOfVector (𝟙 (D.obj i)) (fun _ : PUnit.{u + 1} => t)).appTop _))
        simp only [AffineSpace.homOfVector_appTop_coord, hp]
    · simp only [Over.pullback_map_left, pullback.lift_snd]
  obtain ⟨j, g, hg⟩ := eventually_eq_of_baseChange_eq D c hc i X Y
    (by dsimp [X]; exact ⟨inferInstance, inferInstance, inferInstance⟩)
    (by dsimp [Y]; exact ⟨inferInstance, inferInstance, inferInstance⟩) (f s) (f t)
    (hf _ _ h)
  refine ⟨j, g, ?_⟩
  have he := congrArg (fun k => k.left ≫ pullback.fst Y.hom (D.map g)) hg
  simp only [Over.pullback_map_left, pullback.lift_fst] at he
  rw [hfst, Category.assoc, Category.assoc] at he
  have : IsIso (pullback.snd X.hom (D.map g)) := by dsimp [X]; infer_instance
  have he' := (cancel_epi (pullback.snd X.hom (D.map g))).mp he
  have he'' := congrArg (fun k => k.appTop (AffineSpace.coord (D.obj i) PUnit.unit)) he'
  change (D.map g).appTop ((f s).left.appTop _) =
    (D.map g).appTop ((f t).left.appTop _) at he''
  have hs : (f s).left.appTop (AffineSpace.coord (D.obj i) PUnit.unit) = s :=
    AffineSpace.homOfVector_appTop_coord _ _ _
  have ht : (f t).left.appTop (AffineSpace.coord (D.obj i) PUnit.unit) = t :=
    AffineSpace.homOfVector_appTop_coord _ _ _
  rwa [hs, ht] at he''

private lemma exists_common_cocone_of_finite
    {J : Type v} [Category.{v} J] [IsFiltered J] {α : Type w} [Finite α]
    (i₀ : J) (i : α → J) (f : ∀ a, i₀ ⟶ i a) :
    ∃ (k : J) (g : i₀ ⟶ k) (h : ∀ a, i a ⟶ k), ∀ a, f a ≫ h a = g := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  let S : Finset J := insert i₀ (Finset.univ.image i)
  have hi₀ : i₀ ∈ S := by simp [S]
  have hii (a : α) : i a ∈ S := by simp [S]
  let H : Finset (Σ' (X Y : J) (_ : X ∈ S) (_ : Y ∈ S), X ⟶ Y) :=
    Finset.univ.image fun a : α => ⟨i₀, i a, hi₀, hii a, f a⟩
  obtain ⟨k, q, hq⟩ := IsFiltered.sup_exists S H
  refine ⟨k, q hi₀, fun a => q (hii a), fun a => ?_⟩
  exact hq hi₀ (hii a) (Finset.mem_image_of_mem _ (Finset.mem_univ a))

private lemma exists_common_stage_of_finite_eventual_eq
    {J : Type v} [Category.{v} J] [IsFiltered J]
    {α : Type w} [Finite α] (F : J ⥤ Type u) (c : Cocone F) (hc : IsColimit c)
    (i : J) (x y : α → F.obj i)
    (h : ∀ a, c.ι.app i (x a) = c.ι.app i (y a)) :
    ∃ (j : J) (f : i ⟶ j), ∀ a, F.map f (x a) = F.map f (y a) := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  choose j₀ f₀ hf₀ using fun a => exists_eventual_eq_of_filtered_colimit F c hc i
    (x a) (y a) (h a)
  obtain ⟨j, g, θ, hθ⟩ := exists_common_cocone_of_finite i j₀ f₀
  refine ⟨j, g, fun a => ?_⟩
  have hj : f₀ a ≫ θ a = g := hθ a
  calc
    F.map g (x a) = F.map (f₀ a ≫ θ a) (x a) := by rw [hj]
    _ = F.map (θ a) (F.map (f₀ a) (x a)) := by simp
    _ = F.map (θ a) (F.map (f₀ a) (y a)) := by rw [hf₀ a]
    _ = F.map (f₀ a ≫ θ a) (y a) := by simp
    _ = F.map g (y a) := by rw [hj]

private lemma ring_colimit_surjective
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c) :
    ∀ x : c.pt, ∃ i y, c.ι.app i y = x := by
  classical
  have hcommon {x y : c.pt} (hx : ∃ i a, (c.ι.app i).hom a = x)
      (hy : ∃ i b, (c.ι.app i).hom b = y) :
      ∃ k a b, (c.ι.app k).hom a = x ∧ (c.ι.app k).hom b = y := by
    obtain ⟨i, a, rfl⟩ := hx
    obtain ⟨j, b, rfl⟩ := hy
    obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists {i, j}
    obtain ⟨hik⟩ := hk (X := i) (by simp)
    obtain ⟨hjk⟩ := hk (X := j) (by simp)
    exact ⟨k, F.map hik a, F.map hjk b,
      congrArg (fun h : CommRingCat.Hom (F.obj i) c.pt => h.hom a) (c.w hik),
      congrArg (fun h : CommRingCat.Hom (F.obj j) c.pt => h.hom b) (c.w hjk)⟩
  let S : Subring (↑c.pt) := {
    carrier := {x | ∃ i y, (c.ι.app i).hom y = x}
    zero_mem' := by
      obtain ⟨i⟩ := IsFiltered.nonempty (C := J)
      exact ⟨i, 0, by simp⟩
    one_mem' := by
      obtain ⟨i⟩ := IsFiltered.nonempty (C := J)
      exact ⟨i, 1, by simp⟩
    add_mem' := by
      rintro x y hx hy
      obtain ⟨k, a, b, rfl, rfl⟩ := hcommon hx hy
      exact ⟨k, a + b, by simp⟩
    mul_mem' := by
      rintro x y hx hy
      obtain ⟨k, a, b, rfl, rfl⟩ := hcommon hx hy
      exact ⟨k, a * b, by simp⟩
    neg_mem' := by
      rintro x ⟨i, a, rfl⟩
      exact ⟨i, -a, by simp⟩ }
  let d : Cocone F := {
    pt := CommRingCat.of S
    ι := {
      app i := CommRingCat.ofHom (RingHom.codRestrict (c.ι.app i).hom S
        (fun x => ⟨i, x, rfl⟩))
      naturality i j f := by
        apply CommRingCat.hom_ext
        ext x
        apply Subtype.ext
        exact congrArg (fun h : CommRingCat.Hom (F.obj i) c.pt => h.hom x) (c.w f) }
  }
  let g := hc.desc d
  let inc : CommRingCat.of S ⟶ c.pt := CommRingCat.ofHom S.subtype
  have hg : g ≫ inc = 𝟙 c.pt := by
    apply hc.hom_ext
    intro i
    calc
      c.ι.app i ≫ g ≫ inc = (c.ι.app i ≫ g) ≫ inc := by simp [Category.assoc]
      _ = d.ι.app i ≫ inc := by rw [hc.fac]
      _ = c.ι.app i := by
        apply CommRingCat.hom_ext
        ext x
        rfl
  intro x
  have hx := congrArg (fun h : CommRingCat.Hom c.pt c.pt => h.hom x) hg
  change (g.hom x).val = x at hx
  obtain ⟨i, y, hy⟩ := (g.hom x).property
  exact ⟨i, y, by simpa [hx] using hy⟩

private noncomputable def gamma_mapCocone_isColimit
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i, IsAffine (D.obj i)) :
    IsColimit (Scheme.Γ.mapCocone c.op) := by
  letI : ∀ i, IsAffine (D.obj i) := hD
  letI : ∀ i, IsAffine ((D.op).obj i).unop := fun i => hD i.unop
  exact isColimitOfPreserves Scheme.Γ hc.op

private lemma exists_stage_section
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i, IsAffine (D.obj i)) (s : Γ(c.pt, ⊤)) :
    ∃ (i : I) (sᵢ : Γ(D.obj i, ⊤)), (c.π.app i).appTop sᵢ = s := by
  obtain ⟨i, sᵢ, hsᵢ⟩ := ring_colimit_surjective (D.op ⋙ Scheme.Γ)
    (Scheme.Γ.mapCocone c.op) (gamma_mapCocone_isColimit D c hc hD) s
  exact ⟨i.unop, sᵢ, hsᵢ⟩

private noncomputable def gamma_forget_mapCocone_isColimit
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] :
    IsColimit ((forget CommRingCat).mapCocone (Scheme.Γ.mapCocone c.op)) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := exists_stage_section D c hc (fun _ => inferInstance) x
    exact ⟨Opposite.op i, y, hy.symm⟩
  · intro i x y h
    obtain ⟨j, g, hg⟩ := exists_equal_section_stage D c hc i.unop x y h
    exact ⟨Opposite.op j, g.op, hg⟩

private lemma exists_stage_ringHom
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)]
    (R : CommRingCat.{u}) (hR : Algebra.FinitePresentation ℤ R)
    (f : R ⟶ Γ(c.pt, ⊤)) :
    ∃ (i : I) (g : R ⟶ Γ(D.obj i, ⊤)), g ≫ (c.π.app i).appTop = f := by
  let F := D.op ⋙ Scheme.Γ
  let C := Scheme.Γ.mapCocone c.op
  let hC := gamma_mapCocone_isColimit D c hc (fun _ => inferInstance)
  let : PreservesColimit F (forget CommRingCat) :=
    preservesColimit_of_preserves_colimit_cocone hC
      (gamma_forget_mapCocone_isColimit D c hc)
  let Z := CommRingCat.of (ULift.{u} ℤ)
  let a : (Functor.const Iᵒᵖ).obj Z ⟶ F :=
    { app i := CommRingCat.isInitial.to (F.obj i)
      naturality _ _ _ := CommRingCat.isInitial.hom_ext _ _ }
  have hfp : (CommRingCat.isInitial.to R).hom.FinitePresentation := by
    rw [CommRingCat.isInitial.hom_ext (CommRingCat.isInitial.to R)
      (CommRingCat.ofHom ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom))]
    exact (RingHom.finitePresentation_algebraMap.mpr hR).comp
      (.of_bijective ULift.ringEquiv.bijective)
  obtain ⟨i, g, _, hg⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    Z F a (CommRingCat.isInitial.to R) C hC hfp f
    (fun _ => CommRingCat.isInitial.hom_ext _ _)
  exact ⟨i.unop, g, hg.symm⟩

private lemma appTop_transport
    {I : Type v} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i j : I} (f : i ⟶ j) (s : Γ(D.obj j, ⊤)) :
    (c.π.app i).appTop ((D.map f).appTop s) = (c.π.app j).appTop s := by
  have htransport := congrArg (fun g : CommRingCat.Hom _ _ => g.hom s)
    (congrArg Scheme.Hom.appTop (c.w f))
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    using htransport

private lemma exists_affine_model_of_isPushout
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ c.pt)
    (P : MorphismProperty Scheme.{u})
    (hbase : ∀ {A B S : Scheme.{u}} [IsAffine A] [IsAffine B] [IsAffine S]
      (f : A ⟶ S) (g : B ⟶ S), P f → P (pullback.snd f g))
    {R B : CommRingCat.{u}} (r : R ⟶ Γ(c.pt, ⊤)) (g : R ⟶ B)
    (b : B ⟶ Γ(X, ⊤)) (hR : Algebra.FinitePresentation ℤ R)
    (hp : IsPushout r g f.appTop b) (hg : P (Spec.map g)) :
    ∃ (i : I) (Y : Over (D.obj i)), IsAffine Y.left ∧ P Y.hom ∧
      Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ Over.mk f) := by
  obtain ⟨i, ri, hri⟩ := exists_stage_ringHom D c hc R hR r
  let q := (D.obj i).isoSpec.hom ≫ Spec.map ri
  have hq : c.π.app i ≫ q = c.pt.isoSpec.hom ≫ Spec.map r := by
    dsimp [q]
    rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality,
      Category.assoc, ← Spec.map_comp, hri]
  have hs : IsPullback (X.isoSpec.hom ≫ Spec.map b) f
      (Spec.map g) (c.pt.isoSpec.hom ≫ Spec.map r) := by
    apply (isPullback_SpecMap_of_isPushout r g f.appTop b hp).flip.of_iso
      X.isoSpec.symm (Iso.refl _) c.pt.isoSpec.symm (Iso.refl _)
    · simp
    · simpa using Scheme.isoSpec_inv_naturality f
    · simp
    · simp
  rw [← hq] at hs
  let Y : Over (D.obj i) := Over.mk (pullback.snd (Spec.map g) q)
  have h := hs.of_right' (IsPullback.of_hasPullback (Spec.map g) q)
  refine ⟨i, Y, ?_, hbase _ _ hg, ?_⟩
  · dsimp [Y]
    infer_instance
  exact ⟨(Over.isoMk h.isoPullback h.isoPullback_hom_snd).symm⟩


private lemma exists_affine_etale_model
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ c.pt) [Etale f] :
    ∃ (i : I) (Y : Over (D.obj i)), IsAffine Y.left ∧ Etale Y.hom ∧
      Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ Over.mk f) := by
  have hf : f.appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  let := f.appTop.hom.toAlgebra
  let : Algebra.Etale Γ(c.pt, ⊤) Γ(X, ⊤) := hf
  obtain ⟨R, B, _, _, hR, hB, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg ℤ Γ(c.pt, ⊤) Γ(X, ⊤)
  have hRfp : Algebra.FinitePresentation ℤ R :=
    Algebra.FinitePresentation.of_finiteType.mp ⟨R.fg_top.mpr hR⟩
  exact exists_affine_model_of_isPushout D c hc f (@Etale)
    (by intro A B S _ _ _ f g hf; let := hf; infer_instance)
    (CommRingCat.ofHom (algebraMap R Γ(c.pt, ⊤)))
    (CommRingCat.ofHom (algebraMap R B)) _ hRfp
    (isPushout_of_algEquiv_tensorProduct R Γ(c.pt, ⊤) B Γ(X, ⊤) e)
    (HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hB))

private lemma standardSmooth_pullback_snd
    {A B S : Scheme.{u}} [IsAffine A] [IsAffine B] [IsAffine S]
    (f : A ⟶ S) (g : B ⟶ S) (hf : f.appTop.hom.IsStandardSmooth) :
    (pullback.snd f g).appTop.hom.IsStandardSmooth := by
  let : (RingHom.toMorphismProperty @RingHom.IsStandardSmooth).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
      RingHom.isStandardSmooth_isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty @RingHom.IsStandardSmooth)
    (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f g)).flip hf

private lemma exists_affine_standardSmooth_model
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ c.pt)
    (hf : f.appTop.hom.IsStandardSmooth) :
    ∃ (i : I) (Y : Over (D.obj i)), IsAffine Y.left ∧
      Y.hom.appTop.hom.IsStandardSmooth ∧
      Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ Over.mk f) := by
  let := f.appTop.hom.toAlgebra
  have hstd : Algebra.IsStandardSmooth Γ(c.pt, ⊤) Γ(X, ⊤) := hf
  obtain ⟨ι, σ, hσ, hι, ⟨p⟩⟩ := hstd.out
  let := hσ
  let := hι
  let : Algebra.IsStandardSmoothOfRelativeDimension p.dimension Γ(c.pt, ⊤) Γ(X, ⊤) :=
    p.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨R, B, _, _, hR, hB, ⟨e⟩⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg
      ℤ Γ(c.pt, ⊤) Γ(X, ⊤) p.dimension
  have hRfp : Algebra.FinitePresentation ℤ R :=
    Algebra.FinitePresentation.of_finiteType.mp ⟨R.fg_top.mpr hR⟩
  let := hB
  have hB' : (algebraMap R B).IsStandardSmooth :=
    RingHom.isStandardSmooth_algebraMap.mpr
      (Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth p.dimension)
  exact exists_affine_model_of_isPushout D c hc f
    (fun _ _ f => f.appTop.hom.IsStandardSmooth) standardSmooth_pullback_snd
    (CommRingCat.ofHom (algebraMap R Γ(c.pt, ⊤)))
    (CommRingCat.ofHom (algebraMap R B)) _ hRfp
    (isPushout_of_algEquiv_tensorProduct R Γ(c.pt, ⊤) B Γ(X, ⊤) e)
    ((isStandardSmooth_specMap_iff _).mpr hB')

private lemma universallyOpen_of_standardSmooth
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (hf : f.appTop.hom.IsStandardSmooth) : UniversallyOpen f := by
  let := f.appTop.hom.toAlgebra
  let : Algebra.IsStandardSmooth Γ(S, ⊤) Γ(X, ⊤) := hf
  have hsm : f.appTop.hom.Smooth := inferInstanceAs (Algebra.Smooth Γ(S, ⊤) Γ(X, ⊤))
  let : Smooth f := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mpr hsm
  infer_instance

private lemma flat_finitePresentation_pullback_snd
    {A B S : Scheme.{u}} [IsAffine A] [IsAffine B] [IsAffine S]
    (f : A ⟶ S) (g : B ⟶ S) (hf : Flat f ∧ LocallyOfFinitePresentation f) :
    Flat (pullback.snd f g) ∧ LocallyOfFinitePresentation (pullback.snd f g) := by
  let := hf.1
  let := hf.2
  exact ⟨inferInstance, inferInstance⟩

open Algebra.FiniteTypeSystem in
private lemma exists_affine_flat_finitePresentation_model
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ c.pt)
    [Flat f] [LocallyOfFinitePresentation f] :
    ∃ (i : I) (Y : Over (D.obj i)), IsAffine Y.left ∧
      (Flat Y.hom ∧ LocallyOfFinitePresentation Y.hom) ∧
      Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ Over.mk f) := by
  let A := Γ(c.pt, ⊤)
  let B := Γ(X, ⊤)
  let := f.appTop.hom.toAlgebra
  let : Module.Flat A B := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp inferInstance
  let : Algebra.FinitePresentation A B :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp inferInstance
  obtain ⟨R₀, S₀, _, _, _, _, _, _, _, _, _, _, hZ, hS₀, _, hpush, _⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := A) (S := B) B
  let := hZ
  let := hS₀
  let := hpush
  obtain ⟨i, hi⟩ := exists_flat_stage_self R₀ S₀ (B := B)
  let R := Base R₀ i
  let S := Ring R₀ S₀ i
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hR : Algebra.FinitePresentation ℤ R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hS : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hp : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S)) f.appTop
      (CommRingCat.ofHom (algebraMap S B)) :=
    CommRingCat.isPushout_iff_isPushout.mpr (ringToRing_isPushout R₀ S₀ (S := B) i)
  exact exists_affine_model_of_isPushout D c hc f
    (fun _ _ f => Flat f ∧ LocallyOfFinitePresentation f) flat_finitePresentation_pullback_snd
    _ _ _ hR hp ⟨HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr hi),
      HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr hS)⟩

private abbrev relativeGlobalCompleteIntersection : MorphismProperty CommRingCat.{u} :=
  fun R S f => letI := f.hom.toAlgebra; Algebra.IsRelativeGlobalCompleteIntersection R S

private lemma relativeGlobalCompleteIntersection_isStableUnderCobaseChange :
    relativeGlobalCompleteIntersection.{u}.IsStableUnderCobaseChange := by
  constructor
  intro R S R' S' f g f' g' hsq hf
  algebraize [f.hom, g.hom, f'.hom, g'.hom, f'.hom.comp g.hom]
  have : IsScalarTower R S S' := .of_algebraMap_eq fun x => congr($(hsq.1.1).hom x)
  have : Algebra.IsPushout R S R' S' := (CommRingCat.isPushout_iff_isPushout.mp hsq).symm
  let : Algebra.IsRelativeGlobalCompleteIntersection R S := hf
  exact Algebra.IsRelativeGlobalCompleteIntersection.baseChange R S R' S'

private lemma standardSyntomic_pullback_snd
    {A B S : Scheme.{u}} [IsAffine A] [IsAffine B] [IsAffine S]
    (f : A ⟶ S) (g : B ⟶ S) (hf : relativeGlobalCompleteIntersection f.appTop) :
    relativeGlobalCompleteIntersection (pullback.snd f g).appTop := by
  let := relativeGlobalCompleteIntersection_isStableUnderCobaseChange.{u}
  exact MorphismProperty.of_isPushout (P := relativeGlobalCompleteIntersection)
    (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f g)).flip hf

open Algebra.FiniteTypeSystem in
private lemma exists_relativeGlobalCompleteIntersection_finiteType_model
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsRelativeGlobalCompleteIntersection A B] :
    ∃ (R S : CommRingCat.{u}) (r : R ⟶ CommRingCat.of A) (g : R ⟶ S)
      (b : S ⟶ CommRingCat.of B), Algebra.FinitePresentation ℤ R ∧
      relativeGlobalCompleteIntersection g ∧
      IsPushout r g (CommRingCat.ofHom (algebraMap A B)) b := by
  let := Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection A B
  obtain ⟨R₀, S₀, _, _, _, _, _, _, _, _, _, _, hZ, hS₀, _, hpush, _⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := A) (S := B) B
  let := hZ
  let := hS₀
  let := hpush
  have hfp i : Algebra.FinitePresentation (Base R₀ i) (Ring R₀ S₀ i) := by
    let : IsNoetherianRing (Base R₀ i) := Algebra.FiniteType.isNoetherianRing ℤ _
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hsys : ∀ i j (h : i ≤ j), IsPushout
      (CommRingCat.ofHom (baseMap R₀ h).toRingHom)
      (CommRingCat.ofHom (algebraMap (Base R₀ i) (Ring R₀ S₀ i)))
      (CommRingCat.ofHom (algebraMap (Base R₀ j) (Ring R₀ S₀ j)))
      (CommRingCat.ofHom (ringMap R₀ S₀ h).toRingHom) := by
    intro i j h
    let : Fact (i ≤ j) := ⟨h⟩
    exact CommRingCat.isPushout_iff_isPushout.mpr (ringMap_isPushout R₀ S₀)
  obtain ⟨i, hi⟩ := Algebra.IsRelativeGlobalCompleteIntersection.exists_stage_of_directed
    (A := Base R₀) (B := Ring R₀ S₀)
    (fun _ _ h => (baseMap R₀ h).toRingHom)
    (fun _ _ h => (ringMap R₀ S₀ h).toRingHom)
    (fun i j h => by ext r; exact ringMap_algebraMap R₀ S₀ h r)
    (R := A) (S := B) (fun i => (baseToRing R₀ i).toRingHom)
    (fun i => (ringToRing R₀ S₀ (S := B) i).toRingHom)
    (fun _ _ _ _ => rfl) (fun _ _ h x => ring_cocone R₀ S₀ h x)
    (fun i => algebraMap_base_ring_comp R₀ S₀ i)
    (base_jointly_surjective R₀)
    (fun i x h => ⟨i, le_rfl, by
      change x = 0
      exact (algebraMap_base_injective R₀ i) (by simpa [baseToRing] using h)⟩)
    (ring_colimit R₀ S₀ (S := B)).1
    (fun i x h => by
      obtain ⟨j, hj, he⟩ := (ring_colimit R₀ S₀ (S := B)).2 i x 0 (by simpa using h)
      exact ⟨j, hj, by simpa using he⟩) hsys hfp
  refine ⟨CommRingCat.of (Base R₀ i), CommRingCat.of (Ring R₀ S₀ i),
    CommRingCat.ofHom (algebraMap (Base R₀ i) A),
    CommRingCat.ofHom (algebraMap (Base R₀ i) (Ring R₀ S₀ i)),
    CommRingCat.ofHom (algebraMap (Ring R₀ S₀ i) B),
    Algebra.FinitePresentation.of_finiteType.mp inferInstance, ?_,
    CommRingCat.isPushout_iff_isPushout.mpr (ringToRing_isPushout R₀ S₀ (S := B) i)⟩
  change @Algebra.IsRelativeGlobalCompleteIntersection (Base R₀ i) _ (Ring R₀ S₀ i) _
    (algebraMap (Base R₀ i) (Ring R₀ S₀ i)).toAlgebra
  convert hi using 1
  exact toAlgebra_algebraMap

private lemma exists_affine_standardSyntomic_model
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ c.pt)
    (hf : relativeGlobalCompleteIntersection f.appTop) :
    ∃ (i : I) (Y : Over (D.obj i)), IsAffine Y.left ∧
      relativeGlobalCompleteIntersection Y.hom.appTop ∧
      Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ Over.mk f) := by
  let := f.appTop.hom.toAlgebra
  let : Algebra.IsRelativeGlobalCompleteIntersection Γ(c.pt, ⊤) Γ(X, ⊤) := hf
  obtain ⟨R, S, r, g, b, hR, hg, hp⟩ :=
    exists_relativeGlobalCompleteIntersection_finiteType_model (A := Γ(c.pt, ⊤)) (B := Γ(X, ⊤))
  let := relativeGlobalCompleteIntersection_isStableUnderCobaseChange.{u}
  exact exists_affine_model_of_isPushout D c hc f
    (fun _ _ f => relativeGlobalCompleteIntersection f.appTop) standardSyntomic_pullback_snd
    r g b hR hp
    ((MorphismProperty.arrow_mk_iso_iff relativeGlobalCompleteIntersection
      (arrowIsoΓSpecOfIsAffine g)).mp hg)

private lemma universallyOpen_of_standardSyntomic
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (hf : relativeGlobalCompleteIntersection f.appTop) : UniversallyOpen f := by
  let := f.appTop.hom.toAlgebra
  let : Algebra.IsRelativeGlobalCompleteIntersection Γ(S, ⊤) Γ(X, ⊤) := hf
  let := Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection Γ(S, ⊤) Γ(X, ⊤)
  let : Flat f := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mpr
    (inferInstanceAs (Module.Flat Γ(S, ⊤) Γ(X, ⊤)))
  let : LocallyOfFinitePresentation f :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mpr
      (inferInstanceAs (Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤)))
  infer_instance

private lemma exists_stage_sections
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i, IsAffine (D.obj i)) {J : Type w} [Finite J]
    (s : J → Γ(c.pt, ⊤)) :
    ∃ (i : I) (t : J → Γ(D.obj i, ⊤)),
      ∀ j, (c.π.app i).appTop (t j) = s j := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  choose i₀ t₀ ht₀ using fun j : J => exists_stage_section D c hc hD (s j)
  obtain ⟨i, ⟨e⟩⟩ := exists_common_predecessor_of_finite i₀
  refine ⟨i, fun j => (D.map (e j)).appTop (t₀ j), fun j => ?_⟩
  exact (appTop_transport D c (e j) (t₀ j)).trans (ht₀ j)

private lemma exists_stage_span_eq_top
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I)
    {J : Type w} [Finite J] (t : J → Γ(D.obj i, ⊤))
    (ht : Ideal.span (Set.range (fun j => (c.π.app i).appTop (t j))) = ⊤) :
    ∃ (k : I) (g : k ⟶ i),
      Ideal.span (Set.range (fun j => (D.map g).appTop (t j))) = ⊤ := by
  classical
  let := Fintype.ofFinite J
  have h1 : (1 : Γ(c.pt, ⊤)) ∈
      Ideal.span (Set.range (fun j => (c.π.app i).appTop (t j))) :=
    (Ideal.eq_top_iff_one _).mp ht
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  obtain ⟨l, b, hb⟩ := exists_stage_sections D c hc (fun _ => inferInstance) a
  obtain ⟨k, g, h, _⟩ := IsCofilteredOrEmpty.cone_objs i l
  let t' j := (D.map g).appTop (t j)
  let b' j := (D.map h).appTop (b j)
  have he : (c.π.app k).appTop (∑ j, b' j * t' j) = (c.π.app k).appTop 1 := by
    simpa only [map_sum, map_mul, map_one, t', b', appTop_transport, hb] using ha
  obtain ⟨k', e, he'⟩ := exists_equal_section_stage D c hc k _ _ he
  refine ⟨k', e ≫ g, (Ideal.eq_top_iff_one _).mpr ?_⟩
  have hs : ∑ j, (D.map e).appTop (b' j) * (D.map (e ≫ g)).appTop (t j) = 1 := by
    simpa only [map_sum, map_mul, map_one, t', D.map_comp, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply] using he'
  rw [← hs]
  exact Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩))

private lemma iSup_basicOpen_eq_top_iff_span
    {X : Scheme.{u}} [IsAffine X] {J : Type w} (t : J → Γ(X, ⊤)) :
    (⨆ j, X.basicOpen (t j)) = ⊤ ↔ Ideal.span (Set.range t) = ⊤ := by
  have heq : (⨆ j, X.basicOpen (t j)) =
      ⨆ j : Set.range t, X.basicOpen j.1 := by
    apply le_antisymm
    · apply iSup_le
      intro j
      exact le_iSup_of_le ⟨t j, ⟨j, rfl⟩⟩ le_rfl
    · apply iSup_le
      rintro ⟨x, ⟨j, rfl⟩⟩
      exact le_iSup_of_le j le_rfl
  rw [heq]
  exact (isAffineOpen_top X).iSup_basicOpen_eq_self_iff

private lemma exists_stage_preimage_eq_top
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] [∀ i, IsAffine (D.obj i)]
    (i : I) (W : (D.obj i).Opens) (hW : IsCompact (W : Set (D.obj i)))
    (h : (c.π.app i) ⁻¹ᵁ W = ⊤) :
    ∃ (k : I) (g : k ⟶ i), (D.map g) ⁻¹ᵁ W = ⊤ := by
  classical
  obtain ⟨s, hs, hsW⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen.mp ⟨hW, W.isOpen⟩
  let : Finite s := hs
  have heq : W = ⨆ j : s, (D.obj i).basicOpen j.1 := by
    apply TopologicalSpace.Opens.ext
    simpa only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_subtype] using hsW
  have key {Y : Scheme.{u}} [IsAffine Y] (p : Y ⟶ D.obj i) :
      p ⁻¹ᵁ W = ⊤ ↔ Ideal.span (Set.range fun j : s => p.appTop j.1) = ⊤ := by
    rw [heq, Scheme.Hom.preimage_iSup]
    simp only [Scheme.preimage_basicOpen_top]
    exact iSup_basicOpen_eq_top_iff_span _
  obtain ⟨k, g, hg⟩ := exists_stage_span_eq_top D c hc i (fun j : s => j.1)
    ((key (Y := c.pt) (c.π.app i)).mp h)
  exact ⟨k, g, (key (D.map g)).mpr hg⟩

private lemma range_eq_of_over_iso {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) :
    Set.range X.hom = Set.range Y.hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.hom.left y, congrArg (fun f : X.left ⟶ S => f y) e.hom.w⟩
  · rintro ⟨y, rfl⟩
    exact ⟨e.inv.left y, congrArg (fun f : Y.left ⟶ S => f y) e.inv.w⟩

/-- Pulling back along `p` then `q` is pulling back along `p ≫ q`, up to iso. -/
private lemma nonempty_pullback_comp_iso {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C)
    {r : A ⟶ C} (h : p ≫ q = r) (Y : Over C) {Z : Over A}
    (e : (Over.pullback r).obj Y ≅ Z) :
    Nonempty ((Over.pullback p).obj ((Over.pullback q).obj Y) ≅ Z) := by
  subst h
  exact ⟨((Over.pullbackComp p q).app Y).symm ≪≫ e⟩

private lemma exists_covering_of_models
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] [∀ i, IsAffine (D.obj i)]
    {J : Type w} [Finite J] (X : J → Over c.pt)
    (P : MorphismProperty Scheme.{u})
    (hbase : ∀ {A B S : Scheme.{u}} [IsAffine A] [IsAffine B] [IsAffine S]
      (f : A ⟶ S) (g : B ⟶ S), P f → P (pullback.snd f g))
    (hmodels : ∀ j, ∃ (i : I) (Y : Over (D.obj i)),
      IsAffine Y.left ∧ P Y.hom ∧ UniversallyOpen Y.hom ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ X j))
    (hcover : (⋃ j, Set.range (X j).hom) = Set.univ) :
    ∃ (i : I) (Y : J → Over (D.obj i)),
      (∀ j, IsAffine (Y j).left) ∧ (∀ j, P (Y j).hom) ∧
      (⋃ j, Set.range (Y j).hom) = Set.univ ∧
      ∀ j, Nonempty ((Over.pullback (c.π.app i)).obj (Y j) ≅ X j) := by
  classical
  choose i Y hY hP hO e using hmodels
  obtain ⟨k, ⟨g⟩⟩ := exists_common_predecessor_of_finite i
  let Z j := (Over.pullback (D.map (g j))).obj (Y j)
  have hZ j : IsAffine (Z j).left := by
    let := hY j
    dsimp [Z]
    infer_instance
  have hZP j : P (Z j).hom := by
    let := hY j
    exact hbase _ _ (hP j)
  have hZO j : UniversallyOpen (Z j).hom := by
    let := hO j
    dsimp [Z]
    infer_instance
  have eZ j : Nonempty ((Over.pullback (c.π.app k)).obj (Z j) ≅ X j) := by
    exact nonempty_pullback_comp_iso _ _ (c.w (g j)) (Y j) (e j).some
  let W : (D.obj k).Opens :=
    ⟨⋃ j, Set.range (Z j).hom, isOpen_iUnion (fun j => by
      let := hZO j
      simpa only [Set.image_univ] using (Z j).hom.isOpenMap _ isOpen_univ)⟩
  have hW : IsCompact (W : Set (D.obj k)) := by
    apply isCompact_iUnion
    intro j
    let := hZ j
    exact isCompact_range (Z j).hom.continuous
  have hWlim : (c.π.app k) ⁻¹ᵁ W = ⊤ := by
    apply TopologicalSpace.Opens.ext
    change (c.π.app k) ⁻¹' (⋃ j, Set.range (Z j).hom) = Set.univ
    rw [Set.preimage_iUnion]
    simp_rw [← Scheme.Pullback.range_snd]
    rw [← hcover]
    exact Set.iUnion_congr fun j => range_eq_of_over_iso (eZ j).some
  obtain ⟨l, h, hh⟩ := exists_stage_preimage_eq_top D c hc k W hW hWlim
  let Z' j := (Over.pullback (D.map h)).obj (Z j)
  refine ⟨l, Z', ?_, ?_, ?_, ?_⟩
  · intro j
    let := hZ j
    dsimp [Z']
    infer_instance
  · intro j
    let := hZ j
    exact hbase _ _ (hZP j)
  · change (⋃ j, Set.range (pullback.snd (Z j).hom (D.map h))) = Set.univ
    simp_rw [Scheme.Pullback.range_snd]
    rw [← Set.preimage_iUnion]
    exact congrArg (fun U : (D.obj l).Opens => (U : Set (D.obj l))) hh
  · intro j
    exact nonempty_pullback_comp_iso _ _ (c.w h) (Z j) (eZ j).some

private lemma nonempty_pullback_basicOpen_ι_iso
    {X Y U : Scheme.{u}} (p : X ⟶ Y) (t : Γ(Y, ⊤)) (g : U ⟶ X) [IsOpenImmersion g]
    (hg : g.opensRange = X.basicOpen (p.appTop t)) :
    Nonempty ((Over.pullback p).obj (Over.mk (Y.basicOpen t).ι) ≅ Over.mk g) := by
  let P := (Over.pullback p).obj (Over.mk (Y.basicOpen t).ι)
  let : IsOpenImmersion P.hom := by
    dsimp [P]
    infer_instance
  have hP : P.hom.opensRange = g.opensRange := by
    dsimp [P]
    rw [Scheme.Hom.opensRange_pullbackSnd, Scheme.Opens.opensRange_ι,
      Scheme.preimage_basicOpen_top, hg]
  have hP' : Set.range P.hom = Set.range g := by
    simpa only [Scheme.Hom.coe_opensRange] using congrArg (fun V : X.Opens => (V : Set X)) hP
  exact ⟨Over.isoMk (IsOpenImmersion.isoOfRangeEq P.hom g hP')
    (IsOpenImmersion.isoOfRangeEq_hom_fac P.hom g hP')⟩

/-- A finite standard Zariski covering of an affine inverse limit descends to a
standard Zariski covering at some stage. -/
@[stacks 049N "covering_existence"]
theorem exists_standardZariskiCovering_of_isLimit
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] [∀ i, IsAffine (D.obj i)]
    (𝒰 : c.pt.Cover.{w} Scheme.zariskiPrecoverage)
    (h𝒰 : AlgebraicGeometry.IsStandardZariskiCovering 𝒰) :
    ∃ (i : I) (𝒰ᵢ : (D.obj i).Cover.{w} Scheme.zariskiPrecoverage)
      (_h𝒰ᵢ : AlgebraicGeometry.IsStandardZariskiCovering 𝒰ᵢ)
      (e : 𝒰.I₀ ≃ 𝒰ᵢ.I₀),
      ∀ j : 𝒰.I₀,
        Nonempty ((Over.pullback (c.π.app i)).obj (Over.mk (𝒰ᵢ.f (e j))) ≅
          Over.mk (𝒰.f j)) := by
  classical
  let : ∀ j, IsOpenImmersion (𝒰.f j) := fun j => 𝒰.map_prop j
  let : Finite 𝒰.I₀ := h𝒰.1
  have hsource : ∀ j, IsAffine (𝒰.X j) := by
    intro j
    obtain ⟨r, e, _⟩ := h𝒰.2 j
    exact (IsAffine.iff_of_isIso e.hom).2 inferInstance
  let : ∀ j, IsAffine (𝒰.X j) := hsource
  let s : 𝒰.I₀ → Γ(c.pt, ⊤) := fun j => Classical.choose (h𝒰.2 j)
  let e₀ (j : 𝒰.I₀) : 𝒰.X j ≅ (c.pt.basicOpen (s j)).toScheme :=
    Classical.choose (Classical.choose_spec (h𝒰.2 j))
  have hfactor (j : 𝒰.I₀) :
      𝒰.f j = (e₀ j).hom ≫ (c.pt.basicOpen (s j)).ι :=
    Classical.choose_spec (Classical.choose_spec (h𝒰.2 j))
  have hrange (j : 𝒰.I₀) : (𝒰.f j).opensRange = c.pt.basicOpen (s j) := by
    calc
      (𝒰.f j).opensRange = ((e₀ j).hom ≫ (c.pt.basicOpen (s j)).ι).opensRange := by
        congr 1
        exact hfactor j
      _ = (c.pt.basicOpen (s j)).ι.opensRange := Scheme.Hom.opensRange_comp_of_isIso _ _
      _ = c.pt.basicOpen (s j) := Scheme.Opens.opensRange_ι _
  have hUrange : (⨆ j : 𝒰.I₀, (𝒰.f j).opensRange) = ⊤ := by
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    exact 𝒰.iUnion_range
  have hbasic : (⨆ j : 𝒰.I₀, c.pt.basicOpen (s j)) = ⊤ :=
    (iSup_congr fun j => (hrange j).symm).trans hUrange
  obtain ⟨iS, t, ht⟩ := exists_stage_sections D c hc (fun _ => inferInstance) s
  obtain ⟨iFinal, fFinal, hspanFinal⟩ := exists_stage_span_eq_top D c hc iS t
    (by simp only [ht]; exact (iSup_basicOpen_eq_top_iff_span s).mp hbasic)
  let tFinal (j : 𝒰.I₀) : Γ(D.obj iFinal, ⊤) := (D.map fFinal).appTop (t j)
  have hbasicFinal : (⨆ j : 𝒰.I₀, (D.obj iFinal).basicOpen (tFinal j)) = ⊤ :=
    (iSup_basicOpen_eq_top_iff_span tFinal).mpr hspanFinal
  let 𝒰ᵢ : (D.obj iFinal).Cover Scheme.zariskiPrecoverage :=
    Scheme.Cover.mkOfCovers (J := 𝒰.I₀)
      (obj := fun j => ((D.obj iFinal).basicOpen (tFinal j)).toScheme)
      (map := fun j => ((D.obj iFinal).basicOpen (tFinal j)).ι)
      (fun x => by
        obtain ⟨j, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp
          (hbasicFinal.ge (Set.mem_univ x))
        exact ⟨j, ⟨x, hx⟩, rfl⟩)
  have hsectionFinal (j : 𝒰.I₀) : (c.π.app iFinal).appTop (tFinal j) = s j :=
    (appTop_transport D c fFinal (t j)).trans (ht j)
  refine ⟨iFinal, 𝒰ᵢ, ⟨h𝒰.1, fun j => ⟨tFinal j, Iso.refl _, rfl⟩⟩, Equiv.refl _, fun j => ?_⟩
  change Nonempty ((Over.pullback (c.π.app iFinal)).obj
    (Over.mk (((D.obj iFinal).basicOpen (tFinal j)).ι)) ≅ Over.mk (𝒰.f j))
  exact nonempty_pullback_basicOpen_ι_iso (c.π.app iFinal) (tFinal j) (𝒰.f j)
    ((hrange j).trans (congrArg c.pt.basicOpen (hsectionFinal j).symm))

/-- A finite standard étale covering of an affine inverse limit descends to a
standard étale covering at some stage. -/
@[stacks 049N "covering_existence"]
theorem exists_standardEtaleCovering_of_isLimit
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] [∀ i, IsAffine (D.obj i)]
    (𝒰 : c.pt.AffineCover.{w} @Etale) [Finite 𝒰.I₀] :
    ∃ (i : I) (𝒰ᵢ : (D.obj i).AffineCover.{w} @Etale)
      (_ : Finite 𝒰ᵢ.I₀) (e : 𝒰.I₀ ≃ 𝒰ᵢ.I₀),
      ∀ j : 𝒰.I₀,
        Nonempty ((Over.pullback (c.π.app i)).obj (Over.mk (𝒰ᵢ.f (e j))) ≅
          Over.mk (𝒰.f j)) := by
  classical
  have hm (j : 𝒰.I₀) : ∃ (i : I) (Y : Over (D.obj i)),
      IsAffine Y.left ∧ Etale Y.hom ∧ UniversallyOpen Y.hom ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ Over.mk (𝒰.f j)) := by
    let := 𝒰.map_prop j
    obtain ⟨i, Y, hY, hE, he⟩ := exists_affine_etale_model D c hc (𝒰.f j)
    let := hE
    exact ⟨i, Y, hY, hE, inferInstance, he⟩
  obtain ⟨i, Y, hY, hE, hsurj, he⟩ := exists_covering_of_models D c hc
    (fun j => Over.mk (𝒰.f j)) (@Etale)
    (by intro A B S _ _ _ f g hf; let := hf; infer_instance) hm
    (Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨𝒰.idx x, 𝒰.covers x⟩)
  let : ∀ j, IsAffine (Y j).left := hY
  let fi j := (Y j).left.isoSpec.inv ≫ (Y j).hom
  have hfi (x : D.obj i) : ∃ j y, fi j y = x := by
    obtain ⟨j, y, rfl⟩ := Set.mem_iUnion.mp (hsurj.ge (Set.mem_univ x))
    exact ⟨j, (Y j).left.isoSpec.hom y, by simp [fi, ← Scheme.Hom.comp_apply]⟩
  let V : (D.obj i).AffineCover.{w} (@Etale) :=
    { I₀ := 𝒰.I₀
      X j := Γ((Y j).left, ⊤)
      f := fi
      idx x := (hfi x).choose
      covers x := (hfi x).choose_spec
      map_prop j := by let := hE j; dsimp [fi]; infer_instance }
  refine ⟨i, V, inferInstanceAs (Finite 𝒰.I₀), Equiv.refl _, fun j => ?_⟩
  let ej : Over.mk (fi j) ≅ Y j := Over.isoMk (Y j).left.isoSpec.symm rfl
  exact ⟨(Over.pullback (c.π.app i)).mapIso ej ≪≫ (he j).some⟩

-- Keep the accepted statement's interpretation of `⟶`: the proof imports also
-- provide a competing instance through `ReflQuiver`.
/-- A finite standard smooth covering of an affine inverse limit descends to a
standard smooth covering at some stage. -/
@[stacks 049N "covering_existence"]
theorem exists_standardSmoothCovering_of_isLimit
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] [∀ i, IsAffine (D.obj i)]
    {J : Type w} [Finite J]
    (U : J → Scheme.{u}) [∀ j, IsAffine (U j)]
    (f : ∀ j, U j ⟶ c.pt)
    (hf : IsStandardSmoothCovering U f) :
    ∃ (i : I) (Uᵢ : J → Scheme.{u})
      (hUᵢ : ∀ j, IsAffine (Uᵢ j)) (fᵢ : ∀ j, Uᵢ j ⟶ D.obj i),
      (letI : ∀ j, IsAffine (Uᵢ j) := hUᵢ
       IsStandardSmoothCovering Uᵢ fᵢ) ∧
        ∀ j : J,
          Nonempty ((Over.pullback (c.π.app i)).obj (Over.mk (fᵢ j)) ≅
            Over.mk (f j)) := by
  have hm (j : J) : ∃ (i : I) (Y : Over (D.obj i)),
      IsAffine Y.left ∧ Y.hom.appTop.hom.IsStandardSmooth ∧ UniversallyOpen Y.hom ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ Over.mk (f j)) := by
    obtain ⟨i, Y, hY, hS, he⟩ := exists_affine_standardSmooth_model D c hc (f j) (hf.1 j)
    let := hY
    exact ⟨i, Y, hY, hS, universallyOpen_of_standardSmooth Y.hom hS, he⟩
  obtain ⟨i, Y, hY, hS, hsurj, he⟩ := exists_covering_of_models D c hc
    (fun j => Over.mk (f j)) (fun _ _ f => f.appTop.hom.IsStandardSmooth)
    standardSmooth_pullback_snd hm hf.2
  exact ⟨i, fun j => (Y j).left, hY, fun j => (Y j).hom, ⟨hS, hsurj⟩, he⟩


/-- A finite standard syntomic covering of an affine inverse limit descends to a
standard syntomic covering at some stage. -/
@[stacks 049N "covering_existence"]
theorem exists_standardSyntomicCovering_of_isLimit
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)]
    {J : Type w} (U : J → Scheme.{u}) (f : ∀ j, U j ⟶ c.pt)
    (hf : IsStandardSyntomicCovering U f) :
    ∃ (i : I) (Uᵢ : J → Scheme.{u}) (fᵢ : ∀ j, Uᵢ j ⟶ D.obj i),
      IsStandardSyntomicCovering Uᵢ fᵢ ∧
        ∀ j : J,
          Nonempty ((Over.pullback (c.π.app i)).obj (Over.mk (fᵢ j)) ≅
            Over.mk (f j)) := by
  let := hf.affine_target
  let := hf.finite_index
  let := hf.affine_source
  have hm (j : J) : ∃ (i : I) (Y : Over (D.obj i)),
      IsAffine Y.left ∧ relativeGlobalCompleteIntersection Y.hom.appTop ∧
        UniversallyOpen Y.hom ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ Over.mk (f j)) := by
    obtain ⟨i, Y, hY, hS, he⟩ := exists_affine_standardSyntomic_model D c hc
      (f j) (hf.standard_syntomic j)
    let := hY
    exact ⟨i, Y, hY, hS, universallyOpen_of_standardSyntomic Y.hom hS, he⟩
  obtain ⟨i, Y, hY, hS, hsurj, he⟩ := exists_covering_of_models D c hc
    (fun j => Over.mk (f j)) (fun _ _ f => relativeGlobalCompleteIntersection f.appTop)
    standardSyntomic_pullback_snd hm hf.jointly_surjective
  exact ⟨i, fun j => (Y j).left, fun j => (Y j).hom,
    ⟨inferInstance, inferInstance, hY, hS, hsurj⟩, he⟩


/-- A finite standard fppf covering of an affine inverse limit descends to a
standard fppf covering at some stage. -/
@[stacks 049N "covering_existence"]
theorem exists_standardFppfCovering_of_isLimit
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)]
    {J : Type w} (U : J → Scheme.{u}) (f : ∀ j, U j ⟶ c.pt)
    (hf : IsStandardFppfCovering U f) :
    ∃ (i : I) (Uᵢ : J → Scheme.{u}) (fᵢ : ∀ j, Uᵢ j ⟶ D.obj i),
      IsStandardFppfCovering Uᵢ fᵢ ∧
        ∀ j : J,
          Nonempty ((Over.pullback (c.π.app i)).obj (Over.mk (fᵢ j)) ≅
            Over.mk (f j)) := by
  let := hf.affine_target
  let := hf.finite_index
  let := hf.affine_source
  have hm (j : J) : ∃ (i : I) (Y : Over (D.obj i)),
      IsAffine Y.left ∧ (Flat Y.hom ∧ LocallyOfFinitePresentation Y.hom) ∧
        UniversallyOpen Y.hom ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Y ≅ Over.mk (f j)) := by
    let := hf.flat j
    let := (hf.finite_presentation j).1
    obtain ⟨i, Y, hY, hP, he⟩ := exists_affine_flat_finitePresentation_model D c hc (f j)
    let := hP.1
    let := hP.2
    exact ⟨i, Y, hY, hP, inferInstance, he⟩
  obtain ⟨i, Y, hY, hP, hsurj, he⟩ := exists_covering_of_models D c hc
    (fun j => Over.mk (f j)) (fun _ _ f => Flat f ∧ LocallyOfFinitePresentation f)
    flat_finitePresentation_pullback_snd hm hf.jointly_surjective
  let := hY
  refine ⟨i, fun j => (Y j).left, fun j => (Y j).hom, ?_, he⟩
  exact ⟨inferInstance, inferInstance, hY, fun j => (hP j).1,
    fun j => ⟨(hP j).2, inferInstance, inferInstance⟩, hsurj⟩

end AlgebraicGeometry
