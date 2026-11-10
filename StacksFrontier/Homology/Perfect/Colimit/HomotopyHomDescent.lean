module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Perfect.Colimit.ModuleDescent
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Perfect complexes over filtered colimits of rings: morphisms at a finite stage

Morphisms, cochains and homotopies out of a bounded complex of finite projective modules into a
filtered colimit of complexes are realized, and identified, at a finite stage, so that homotopy
classes of such maps commute with the filtered colimit. The file also records that derived
extension of scalars composes compatibly with the scalar tower on complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

open scoped TensorProduct

open scoped Matrix

universe uI uR uM uA

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

/-- Finitely many elements of possibly different filtered colimits can be lifted to one
common stage. -/
private theorem finite_types_lift
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    {α : Type uA} [Finite α] (F : α → I ⥤ Type uM)
    (c : ∀ a, Cocone (F a)) (hc : ∀ a, IsColimit (c a)) (x : ∀ a, (c a).pt) :
    ∃ (j : I) (y : ∀ a, (F a).obj j), ∀ a, (c a).ι.app j (y a) = x a := by
  classical
  let := Fintype.ofFinite α
  choose i z hz using fun a => Types.jointly_surjective_of_isColimit (hc a) (x a)
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let f (a : α) : i a ⟶ j :=
    Classical.choice (hj (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩))
  refine ⟨j, fun a => (F a).map (f a) (z a), ?_⟩
  intro a
  exact (congrArg (fun g : (F a).obj (i a) ⟶ (c a).pt => g (z a)) ((c a).w (f a))).trans (hz a)

/-- Finitely many equalities in filtered colimits hold after a common transition. -/
private theorem finite_types_eventually_eq
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    {α : Type uA} [Finite α] (F : α → I ⥤ Type uM)
    (c : ∀ a, Cocone (F a)) (hc : ∀ a, IsColimit (c a))
    (i : I) (x y : ∀ a, (F a).obj i)
    (h : ∀ a, (c a).ι.app i (x a) = (c a).ι.app i (y a)) :
    ∃ (j : I) (f : i ⟶ j), ∀ a, (F a).map f (x a) = (F a).map f (y a) := by
  classical
  choose j f hf using fun a =>
    (Types.FilteredColimit.isColimit_eq_iff' (hc a) (x a) (y a)).1 (h a)
  obtain ⟨k, g, l, hl⟩ := IsFiltered.wideSpan f
  refine ⟨k, g, ?_⟩
  intro a
  rw [← hl a, Functor.map_comp]
  exact congrArg ((F a).map (l a)) (hf a)

set_option backward.isDefEq.respectTransparency false in
/-- A map from a finite projective module into a filtered colimit lifts to a stage. -/
private theorem finite_projective_hom_lift
    {A : Type uR} [CommRing A]
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (F : I ⥤ ModuleCat.{max uM uR} A) (c : Cocone F)
    (hc : IsColimit ((forget (ModuleCat A)).mapCocone c))
    (P : ModuleCat.{max uM uR} A) [Module.Finite A P] [Module.Projective A P]
    (φ : P ⟶ c.pt) :
    ∃ (j : I) (ψ : P ⟶ F.obj j), ψ ≫ c.ι.app j = φ := by
  classical
  obtain ⟨n, f, g, hfg, _⟩ := finite_projective_retract (A := A) P
  let b := Pi.basisFun A (Fin n)
  obtain ⟨j, y, hy⟩ := finite_types_lift
    (fun _ : Fin n => F ⋙ forget (ModuleCat A)) (fun _ => (forget _).mapCocone c)
    (fun _ => hc) (fun k => φ.hom (f (b k)))
  let v : (Fin n → A) →ₗ[A] F.obj j := b.constr A y
  have hv : (c.ι.app j).hom.comp v = φ.hom.comp f := by
    apply b.ext
    intro k
    change (c.ι.app j).hom (v (b k)) = φ.hom (f (b k))
    rw [show v (b k) = y k from b.constr_basis A y k]
    exact hy k
  refine ⟨j, ModuleCat.ofHom (v.comp g), ?_⟩
  apply ModuleCat.hom_ext
  change (c.ι.app j).hom.comp (v.comp g) = φ.hom
  rw [← LinearMap.comp_assoc, hv, LinearMap.comp_assoc, hfg, LinearMap.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Equality of maps from a finite projective module into a filtered colimit is detected
at a later stage. -/
private theorem finite_projective_hom_eventually_eq
    {A : Type uR} [CommRing A]
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (F : I ⥤ ModuleCat.{max uM uR} A) (c : Cocone F)
    (hc : IsColimit ((forget (ModuleCat A)).mapCocone c))
    (P : ModuleCat.{max uM uR} A) [Module.Finite A P] [Module.Projective A P]
    (i : I) (φ ψ : P ⟶ F.obj i) (h : φ ≫ c.ι.app i = ψ ≫ c.ι.app i) :
    ∃ (j : I) (f : i ⟶ j), φ ≫ F.map f = ψ ≫ F.map f := by
  classical
  obtain ⟨n, p, q, hpq, _⟩ := finite_projective_retract (A := A) P
  let b := Pi.basisFun A (Fin n)
  obtain ⟨j, f, hf⟩ := finite_types_eventually_eq
    (fun _ : Fin n => F ⋙ forget (ModuleCat A)) (fun _ => (forget _).mapCocone c)
    (fun _ => hc) i (fun k => φ.hom (p (b k))) (fun k => ψ.hom (p (b k)))
    (fun k => congrArg (fun u : P ⟶ c.pt => u.hom (p (b k))) h)
  have he : (F.map f).hom.comp (φ.hom.comp p) = (F.map f).hom.comp (ψ.hom.comp p) :=
    b.ext fun k => hf k
  refine ⟨j, f, ?_⟩
  apply ModuleCat.hom_ext
  change (F.map f).hom.comp φ.hom = (F.map f).hom.comp ψ.hom
  simpa only [LinearMap.comp_assoc, hpq, LinearMap.comp_id] using
    congrArg (fun u => u.comp q) he

open CochainComplex.HomComplex

/-- Terms of a bounded complex vanish outside its interval of strict bounds. -/
private theorem bounded_isZero
    {A : Type uR} [CommRing A]
    (P : CochainComplex (ModuleCat.{max uM uR} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (p : ℤ) (hp : p ∉ Finset.Icc a b) :
    IsZero (P.X p) := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hp
  rcases hp with hp | hp
  · exact P.isZero_of_isStrictlyGE a p hp
  · exact P.isZero_of_isStrictlyLE b p hp

/-- A cochain out of a bounded complex of finite projectives lifts through a degreewise
filtered colimit. -/
private theorem bounded_projective_cochain_lift
    {A : Type uR} [CommRing A]
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (F : I ⥤ CochainComplex (ModuleCat.{max uM uR} A) ℤ) (c : Cocone F)
    (hc : ∀ q : ℤ, IsColimit ((forget (ModuleCat A)).mapCocone
      ((HomologicalComplex.eval _ _ q).mapCocone c)))
    (P : CochainComplex (ModuleCat.{max uM uR} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ p, Module.Finite A (P.X p)] [∀ p, Module.Projective A (P.X p)]
    (n : ℤ) (z : Cochain P c.pt n) :
    ∃ (j : I) (y : Cochain P (F.obj j) n),
      y.comp (Cochain.ofHom (c.ι.app j)) (add_zero n) = z := by
  classical
  let s := Finset.Icc a b
  choose i y hy using fun p : s => finite_projective_hom_lift
    (F ⋙ HomologicalComplex.eval _ _ (p.1 + n))
    ((HomologicalComplex.eval _ _ (p.1 + n)).mapCocone c) (hc (p.1 + n))
    (P.X p) (z.v p (p + n) rfl)
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let f (p : s) : i p ⟶ j :=
    Classical.choice (hj (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩))
  let u (p : ℤ) : P.X p ⟶ (F.obj j).X (p + n) :=
    if hp : p ∈ s then y ⟨p, hp⟩ ≫ (F.map (f ⟨p, hp⟩)).f (p + n) else 0
  let w : Cochain P (F.obj j) n := Cochain.mk (fun p q hpq => by
    subst q
    exact u p)
  refine ⟨j, w, ?_⟩
  apply Cochain.ext
  intro p q hpq
  subst q
  change u p ≫ (c.ι.app j).f (p + n) = z.v p (p + n) rfl
  by_cases hp : p ∈ s
  · have hu : u p = y ⟨p, hp⟩ ≫ (F.map (f ⟨p, hp⟩)).f (p + n) := dite_eq_left hp
    rw [hu, Category.assoc]
    have hw := congrArg (fun g => g.f (p + n)) (c.w (f ⟨p, hp⟩))
    rw [HomologicalComplex.comp_f] at hw
    rw [hw]
    exact hy ⟨p, hp⟩
  · exact (bounded_isZero P a b p hp).eq_of_src _ _

/-- Equality of cochains out of a bounded complex of finite projectives is detected at a
finite stage of a degreewise filtered colimit. -/
private theorem bounded_projective_cochain_eventually_eq
    {A : Type uR} [CommRing A]
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (F : I ⥤ CochainComplex (ModuleCat.{max uM uR} A) ℤ) (c : Cocone F)
    (hc : ∀ q : ℤ, IsColimit ((forget (ModuleCat A)).mapCocone
      ((HomologicalComplex.eval _ _ q).mapCocone c)))
    (P : CochainComplex (ModuleCat.{max uM uR} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ p, Module.Finite A (P.X p)] [∀ p, Module.Projective A (P.X p)]
    (i : I) (n : ℤ) (x y : Cochain P (F.obj i) n)
    (h : x.comp (Cochain.ofHom (c.ι.app i)) (add_zero n) =
      y.comp (Cochain.ofHom (c.ι.app i)) (add_zero n)) :
    ∃ (j : I) (f : i ⟶ j),
      x.comp (Cochain.ofHom (F.map f)) (add_zero n) =
        y.comp (Cochain.ofHom (F.map f)) (add_zero n) := by
  classical
  let s := Finset.Icc a b
  have he (p : s) : x.v p (p + n) rfl ≫ (c.ι.app i).f (p + n) =
      y.v p (p + n) rfl ≫ (c.ι.app i).f (p + n) :=
    Cochain.congr_v h p (p + n) rfl
  choose j f hf using fun p : s => finite_projective_hom_eventually_eq
    (F ⋙ HomologicalComplex.eval _ _ (p.1 + n))
    ((HomologicalComplex.eval _ _ (p.1 + n)).mapCocone c) (hc (p.1 + n))
    (P.X p) i (x.v p (p + n) rfl) (y.v p (p + n) rfl) (he p)
  obtain ⟨k, g, l, hl⟩ := IsFiltered.wideSpan f
  refine ⟨k, g, ?_⟩
  apply Cochain.ext
  intro p q hpq
  subst q
  by_cases hp : p ∈ s
  · change x.v p (p + n) rfl ≫ (F.map g).f (p + n) =
      y.v p (p + n) rfl ≫ (F.map g).f (p + n)
    rw [← hl ⟨p, hp⟩, F.map_comp, HomologicalComplex.comp_f, ← Category.assoc,
      ← Category.assoc]
    exact congrArg (fun t => t ≫ (F.map (l ⟨p, hp⟩)).f (p + n)) (hf ⟨p, hp⟩)
  · exact (bounded_isZero P a b p hp).eq_of_src _ _

/-- Pushing a cochain along a transition map of a cocone does not change its image in the
cocone point. -/
private theorem cochain_comp_map_comp_ι
    {A : Type uR} [CommRing A]
    {I : Type uI} [Category.{uI} I]
    (F : I ⥤ CochainComplex (ModuleCat.{max uM uR} A) ℤ) (c : Cocone F)
    {P : CochainComplex (ModuleCat.{max uM uR} A) ℤ} {n : ℤ} {i j : I}
    (y : Cochain P (F.obj i) n) (f : i ⟶ j) :
    (y.comp (Cochain.ofHom (F.map f)) (add_zero n)).comp
        (Cochain.ofHom (c.ι.app j)) (add_zero n) =
      y.comp (Cochain.ofHom (c.ι.app i)) (add_zero n) := by
  rw [Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp, c.w f]

/-- A morphism of complexes from a bounded complex of finite projectives lifts through a
degreewise filtered colimit. -/
theorem bounded_projective_complex_hom_lift
    {A : Type uR} [CommRing A]
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (F : I ⥤ CochainComplex (ModuleCat.{max uM uR} A) ℤ) (c : Cocone F)
    (hc : ∀ q : ℤ, IsColimit ((forget (ModuleCat A)).mapCocone
      ((HomologicalComplex.eval _ _ q).mapCocone c)))
    (P : CochainComplex (ModuleCat.{max uM uR} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ p, Module.Finite A (P.X p)] [∀ p, Module.Projective A (P.X p)]
    (φ : P ⟶ c.pt) :
    ∃ (j : I) (ψ : P ⟶ F.obj j), ψ ≫ c.ι.app j = φ := by
  obtain ⟨i, y, hy⟩ := bounded_projective_cochain_lift F c hc P a b 0 (Cochain.ofHom φ)
  have hδ : (δ 0 1 y).comp (Cochain.ofHom (c.ι.app i)) (add_zero 1) =
      (0 : Cochain P (F.obj i) 1).comp (Cochain.ofHom (c.ι.app i)) (add_zero 1) := by
    rw [← δ_comp_ofHom, hy, δ_ofHom, Cochain.zero_comp]
  obtain ⟨j, f, hf⟩ := bounded_projective_cochain_eventually_eq F c hc P a b i 1
    (δ 0 1 y) 0 hδ
  let w := y.comp (Cochain.ofHom (F.map f)) (add_zero 0)
  have hw : δ 0 1 w = 0 := by simpa only [w, δ_comp_ofHom, Cochain.zero_comp] using hf
  let z : Cocycle P (F.obj j) 0 := Cocycle.mk w 1 rfl hw
  refine ⟨j, z.homOf, ?_⟩
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp, Cocycle.cochain_ofHom_homOf_eq_coe]
  exact (cochain_comp_map_comp_ι F c y f).trans hy

/-- A homotopy between two maps out of a bounded complex of finite projectives descends
through a degreewise filtered colimit. -/
theorem bounded_projective_homotopy_descends
    {A : Type uR} [CommRing A]
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (F : I ⥤ CochainComplex (ModuleCat.{max uM uR} A) ℤ) (c : Cocone F)
    (hc : ∀ q : ℤ, IsColimit ((forget (ModuleCat A)).mapCocone
      ((HomologicalComplex.eval _ _ q).mapCocone c)))
    (P : CochainComplex (ModuleCat.{max uM uR} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ p, Module.Finite A (P.X p)] [∀ p, Module.Projective A (P.X p)]
    (i : I) (φ ψ : P ⟶ F.obj i) (h : Homotopy (φ ≫ c.ι.app i) (ψ ≫ c.ι.app i)) :
    ∃ (j : I) (f : i ⟶ j), Nonempty (Homotopy (φ ≫ F.map f) (ψ ≫ F.map f)) := by
  obtain ⟨t, ht⟩ := Cochain.equivHomotopy _ _ h
  obtain ⟨j, u, hu⟩ := bounded_projective_cochain_lift F c hc P a b (-1) t
  let k := IsFiltered.max i j
  let fi : i ⟶ k := IsFiltered.leftToMax i j
  let fj : j ⟶ k := IsFiltered.rightToMax i j
  let w := u.comp (Cochain.ofHom (F.map fj)) (add_zero (-1))
  have hw : w.comp (Cochain.ofHom (c.ι.app k)) (add_zero (-1)) = t := by
    exact (cochain_comp_map_comp_ι F c u fj).trans hu
  have he : (Cochain.ofHom (φ ≫ F.map fi)).comp (Cochain.ofHom (c.ι.app k)) (add_zero 0) =
      (δ (-1) 0 w + Cochain.ofHom (ψ ≫ F.map fi)).comp
        (Cochain.ofHom (c.ι.app k)) (add_zero 0) := by
    rw [Cochain.add_comp, ← δ_comp_ofHom, hw, ← Cochain.ofHom_comp,
      ← Cochain.ofHom_comp, Category.assoc, Category.assoc, c.w fi]
    exact ht
  obtain ⟨l, f, hf⟩ := bounded_projective_cochain_eventually_eq F c hc P a b k 0
    (Cochain.ofHom (φ ≫ F.map fi)) (δ (-1) 0 w + Cochain.ofHom (ψ ≫ F.map fi)) he
  refine ⟨l, fi ≫ f, ⟨(Cochain.equivHomotopy _ _).symm
    ⟨w.comp (Cochain.ofHom (F.map f)) (add_zero (-1)), ?_⟩⟩⟩
  simpa only [δ_comp_ofHom, Cochain.add_comp, ← Cochain.ofHom_comp,
    Category.assoc, ← F.map_comp] using hf

/-- Homotopy classes of maps from a bounded complex of finite projectives commute with
filtered colimits computed degreewise on underlying sets. -/
noncomputable def bounded_projective_homotopy_isColimit
    {A : Type uR} [CommRing A]
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (F : I ⥤ CochainComplex (ModuleCat.{max uM uR} A) ℤ) (c : Cocone F)
    (hc : ∀ q : ℤ, IsColimit ((forget (ModuleCat A)).mapCocone
      ((HomologicalComplex.eval _ _ q).mapCocone c)))
    (P : CochainComplex (ModuleCat.{max uM uR} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ p, Module.Finite A (P.X p)] [∀ p, Module.Projective A (P.X p)] :
    IsColimit (((HomotopyCategory.quotient _ _) ⋙
      coyoneda.obj (Opposite.op ((HomotopyCategory.quotient _ _).obj P))).mapCocone c) := by
  let Q := HomotopyCategory.quotient (ModuleCat.{max uM uR} A) (ComplexShape.up ℤ)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨φ, rfl⟩ := Q.map_surjective x
    obtain ⟨j, ψ, hψ⟩ := bounded_projective_complex_hom_lift F c hc P a b φ
    exact ⟨j, Q.map ψ, by change Q.map φ = Q.map ψ ≫ Q.map (c.ι.app j); rw [← Q.map_comp, hψ]⟩
  · intro i x y hxy
    obtain ⟨φ, rfl⟩ := Q.map_surjective x
    obtain ⟨ψ, rfl⟩ := Q.map_surjective y
    have he : Q.map (φ ≫ c.ι.app i) = Q.map (ψ ≫ c.ι.app i) := by
      change Q.map φ ≫ Q.map (c.ι.app i) = Q.map ψ ≫ Q.map (c.ι.app i) at hxy
      simpa only [Q.map_comp] using hxy
    obtain ⟨j, f, ⟨hf⟩⟩ := bounded_projective_homotopy_descends F c hc P a b i φ ψ
      (HomotopyCategory.homotopyOfEq _ _ he)
    refine ⟨j, f, ?_⟩
    change Q.map φ ≫ Q.map (F.map f) = Q.map ψ ≫ Q.map (F.map f)
    rw [← Q.map_comp, ← Q.map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _ hf


/-- Extension of scalars carries K-flat complexes to K-flat complexes ([stacks 06Y1]), spelled
with the termwise `ModuleCat.extendScalars` in which derived extension of scalars records its
comparison. -/
private theorem kFlat_extendScalars {A B : Type uR} [CommRing A] [CommRing B] (f : A →+* B)
    (P : CochainComplex (ModuleCat.{uR} A) ℤ) (hP : P.KFlat) :
    CochainComplex.KFlat (((ModuleCat.extendScalars.{uR, uR, uR} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) :=
  kFlat_baseChange f P hP

/-- Derived extension of scalars composes, with the comparison induced by the ordinary
scalar tower on complexes. -/
theorem derivedExtensionScalarsComp_exists (E : DerivedExtendScalars.{uR})
    (hE : ComputesKFlat E)
    {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    let Df := E f
    let Dg := E g
    let Dh := E (g.comp f)
    ∃ (e : Df.functor ⋙ Dg.functor ≅ Dh.functor),
      ∀ (P : CochainComplex (ModuleCat.{uR} A) ℤ),
        Dg.functor.map (Df.comparison.app P) ≫
            Dg.comparison.app (((ModuleCat.extendScalars.{uR, uR, uR} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
            (extensionOfScalarsComplexComp.{uR} f g).inv.app P =
          e.hom.app (DerivedCategory.Q.obj P) ≫ Dh.comparison.app P := by
  let Df := E f
  let Dg := E g
  let Dh := E (g.comp f)
  let F := (ModuleCat.extendScalars.{uR, uR, uR} f).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let β : DerivedCategory.Q ⋙ (Df.functor ⋙ Dg.functor) ⟶
      extensionOfScalarsComplex.{uR, uR, uR} (g.comp f) :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight Df.comparison Dg.functor ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft F Dg.comparison ≫
        (extensionOfScalarsComplexComp.{uR} f g).inv
  let α := Dh.functor.leftDerivedLift Dh.comparison
    (HomologicalComplex.quasiIso (ModuleCat.{uR} A) (ComplexShape.up ℤ))
    (Df.functor ⋙ Dg.functor) β
  have hα (P : CochainComplex (ModuleCat.{uR} A) ℤ) :
      α.app (DerivedCategory.Q.obj P) ≫ Dh.comparison.app P =
        Dg.functor.map (Df.comparison.app P) ≫ Dg.comparison.app (F.obj P) ≫
          (extensionOfScalarsComplexComp.{uR} f g).inv.app P := by
    refine (Dh.functor.leftDerived_fac_app Dh.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{uR} A) (ComplexShape.up ℤ))
      (Df.functor ⋙ Dg.functor) β P).trans ?_
    simp only [β, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp]
    first
    | (erw [NatTrans.comp_app, NatTrans.comp_app, Category.id_comp]; rfl)
  have hIso (P : CochainComplex (ModuleCat.{uR} A) ℤ) (hP : P.KFlat) :
      IsIso (α.app (DerivedCategory.Q.obj P)) := by
    have := hE f P hP
    have := hE g (F.obj P) (kFlat_extendScalars f P hP)
    have := hE (g.comp f) P hP
    have : IsIso (α.app (DerivedCategory.Q.obj P) ≫ Dh.comparison.app P) := by
      rw [hα]
      have h1 : IsIso (Dg.functor.map (Df.comparison.app P)) := Functor.map_isIso _ _
      have h2 : IsIso (Dg.comparison.app (F.obj P)) :=
        hE g (F.obj P) (kFlat_extendScalars f P hP)
      have h3 : IsIso ((extensionOfScalarsComplexComp.{uR} f g).inv.app P) :=
        inferInstance
      exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 h3)
    exact IsIso.of_isIso_comp_right _ (Dh.comparison.app P)
  have : ∀ X, IsIso (α.app X) := fun X => by
    obtain ⟨P, hP, ⟨e⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative X
    exact (NatTrans.isIso_app_iff_of_iso α e).1 (hIso P hP)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨asIso α, fun P => (hα P).symm⟩

end StacksDraft.Perfect

end
