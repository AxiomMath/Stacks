module

public import StacksFrontier.RingTheory.Length.RingEquiv
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.Deformation.Artin.Approximation
public import StacksFrontier.Deformation.Artin.DeformationObjectExt
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.FormalObject.Predeformation
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfCompletedLocalRing
import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-!
# Algebraization of a versal formal object: the completed formal base

The first part of `StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation`:
restriction of objects along isomorphisms of their bases, the completed local ring at a
finite type point as a formal base (`Deformation.Artin.completedFormalBase`), and the
lifting of compatible reductions of formal objects to complete local bases.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber.fiberInclusion
attribute [local implicit_reducible] Deformation.Artin.baseOver
attribute [local implicit_reducible] Deformation.Artin.truncationOver

namespace Deformation.Artin

open Deformation.Artin.Approximation

universe u v w

/-- The underlying map of schemes of a composite of three morphisms of the site, read with
either grouping. -/
theorem left_hom_assoc {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y Z W : AlgebraicGeometry.BigFppfOver B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (f ≫ g).left.hom ≫ h.left.hom = (f ≫ g ≫ h).left.hom := by
  show (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (f ≫ g) ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map h =
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (f ≫ g ≫ h)
  rw [← Functor.map_comp, Category.assoc]

/-- The underlying map of schemes of a morphism of the site conjugated by identifications,
with the trailing pair of identifications cancelling. -/
theorem left_hom_normalize {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y W Z T : AlgebraicGeometry.BigFppfOver B S hS}
    (h₁ : X = Y) (h₂ : Y = W) (f : W ⟶ Z) (h₃ : Z = T) (h₄ : T = Z) :
    (eqToHom h₁ ≫ (eqToHom h₂ ≫ f ≫ eqToHom h₃) ≫ eqToHom h₄).left.hom =
      (eqToHom h₁ ≫ eqToHom h₂).left.hom ≫ f.left.hom := by
  cases h₁
  cases h₂
  cases h₃
  simp

/-- The domain of a morphism lying over a morphism of the base. -/
theorem domain_eq_of_isHomLift {C E : Type*} [Category C] [Category E] (p : E ⥤ C)
    {R T : C} {a b : E} (f : R ⟶ T) (φ : a ⟶ b) (hφ : p.IsHomLift f φ) : p.obj a = R := by
  let := hφ
  exact IsHomLift.domain_eq p f φ


/-- The underlying map of the base of a morphism lying over a morphism of the base. -/
theorem map_eq_of_isHomLift {C E : Type*} [Category C] [Category E] (p : E ⥤ C)
    {R T : C} {a b : E} (f : R ⟶ T) (φ : a ⟶ b) (hφ : p.IsHomLift f φ)
    (ha : p.obj a = R) (hb : p.obj b = T) :
    p.map φ = eqToHom ha ≫ f ≫ eqToHom hb.symm := by
  let := hφ
  rw [IsHomLift.fac' p f φ]

/-- Composing two morphisms lying over morphisms of the base gives a morphism lying over
their composite. -/
theorem isHomLift_comp_of_isHomLift {C E : Type*} [Category C] [Category E]
    (p : E ⥤ C) {R T W : C} (f : R ⟶ T) (g : T ⟶ W) {a b c : E} (φ : a ⟶ b) (ψ : b ⟶ c)
    (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift g ψ) : p.IsHomLift (f ≫ g) (φ ≫ ψ) := by
  let := hφ
  let := hψ
  infer_instance

/-- A composite framed by identifications is unchanged by inserting a cancelling pair of
identifications in the middle. -/
theorem eqToHom_middle_cancel {C : Type*} [Category C] {W X Y M Z Z' : C}
    (h₁ : W = X) (A : X ⟶ Y) (B : Y ⟶ Z) (h₂ : Z = Z') (q : Y = M) (q' : M = Y) :
    eqToHom h₁ ≫ (A ≫ B) ≫ eqToHom h₂ =
      (eqToHom h₁ ≫ A ≫ eqToHom q) ≫ eqToHom q' ≫ B ≫ eqToHom h₂ := by
  cases q
  simp

-- Versality is invariant under an isomorphism of formal objects:
-- `Deformation.isVersal_of_iso`, public beside the lifting criterion it is proved from in
-- `StacksFrontier.Deformation.FormalObject.VersalLifting` (already imported here). A `private`
-- re-declaration stood here.

/-- Successive Artinian lifting problems admit a compatible sequence of solutions. -/
theorem exists_compatible_artinian_lifts
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    (ξ : Deformation.FormalObject p) (hξ : Deformation.IsVersal hp ξ)
    (A : ℕ → Deformation.ArtinianLocalAlgCat Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) (hf : ∀ n, Function.Surjective (f n).hom)
    (η : ℕ → Deformation.FormalObject p)
    (g : ∀ n, η (n + 1) ⟶ η n)
    (hg : ∀ n, Deformation.FormalObject.projection.IsHomLift
      (Deformation.artinianToComplete.map (f n)) (g n))
    (a₀ : ξ ⟶ η 0) :
    ∃ a : ∀ n, ξ ⟶ η n, a 0 = a₀ ∧ ∀ n, a (n + 1) ≫ g n = a n := by
  classical
  have lift (n : ℕ) (a : ξ ⟶ η n) : ∃ b : ξ ⟶ η (n + 1), b ≫ g n = a :=
    (Deformation.isVersal_iff_lifts_artinian hp ξ).1 hξ (f n) (hf n) (g n) (hg n) a
  let a : ∀ n, ξ ⟶ η n := fun n =>
    Nat.rec a₀ (fun n a => Classical.choose (lift n a)) n
  exact ⟨a, rfl, fun n => Classical.choose_spec (lift n (a n))⟩

/-- The canonical quotient map, viewed as a map of complete local algebras. -/
noncomputable def formalBaseQuotient
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : Deformation.CompleteLocalAlgCat Λ k) (n : ℕ) :
    R ⟶ Deformation.artinianToComplete.obj (Deformation.AdicTruncation.obj R n) where
  hom := Ideal.Quotient.mkₐ Λ (Deformation.AdicTruncation.ideal R n)
  isLocal := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  residue_comm := Deformation.AdicTruncation.residueEquiv_residue_mk R n

/-- A formal object can be pushed forward to any of its Artinian quotients. -/
private theorem exists_formal_reduction
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    (η : Deformation.FormalObject p) (n : ℕ) :
    ∃ (ηn : Deformation.FormalObject p) (q : η ⟶ ηn),
      Deformation.FormalObject.projection.IsHomLift (formalBaseQuotient η.base n) q := by
  let hcompletion := Deformation.formalObjectProjection_isCofiberedInGroupoids p hp
  obtain ⟨Y, f, hf⟩ := hcompletion.exists_lift (formalBaseQuotient η.base n).op
    (Opposite.op η) rfl
  refine ⟨Y.unop, f.unop, ?_⟩
  exact CategoryTheory.isHomLift_unop _ _ _ (inst := hf)

private theorem formalBaseQuotient_transition
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : Deformation.CompleteLocalAlgCat Λ k) (n : ℕ) :
    formalBaseQuotient R (n + 1) ≫
        Deformation.artinianToComplete.map (Deformation.AdicTruncation.transition R n) =
      formalBaseQuotient R n := by
  apply Deformation.CompleteLocalAlgCat.Hom.ext
  rfl

-- In a category cofibred in groupoids every hom-lift is strongly cocartesian:
-- `Deformation.isStronglyCocartesian_of_isCofiberedInGroupoids`, public in
-- `StacksFrontier.Deformation.Cofibered` (already imported here), with the identical statement
-- and argument order. A `private` re-declaration stood here.


/-- Every arrow in a category fibred in groupoids is strongly Cartesian. -/
theorem stronglyCartesian_of_fibered
    {C D : Type*} [Category C] [Category D] {p : C ⥤ D}
    (hp : p.IsFiberedInGroupoids) {a b : C} (φ : a ⟶ b) :
    p.IsStronglyCartesian (p.map φ) φ := by
  refine ⟨fun {a'} f ψ hψ => ?_⟩
  have hcomm : f ≫ p.map φ = p.map ψ := IsHomLift.eq_of_isHomLift p _ ψ
  obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ := hp.unique_lift φ ψ f hcomm
  refine ⟨χ, ⟨?_, hfac⟩, ?_⟩
  · rw [← hχ]
    infer_instance
  · intro χ' ⟨hχ', hfac'⟩
    exact huniq χ' ⟨(IsHomLift.eq_of_isHomLift p f χ').symm, hfac'⟩

private theorem formal_restriction_isHomLift
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (Y : Deformation.Artin.FormalObject B S hS p)
    (A : Deformation.Artin.FormalBase S) (hbase : Y.base = A)
    (hA : B.Contains (Spec (.of A.R))) (n : ℕ)
    (hN : B.Contains (A.truncation n))
    (x : F) (hx : p.obj x = Deformation.Artin.baseOver B S hS A hA)
    (t : Y.level n ⟶ x)
    (ht : (eqToHom (Y.level_eq n).symm ≫ p.map t ≫ eqToHom hx).left.hom =
      AlgebraicGeometry.adicThickeningι Y.base.R (maximalIdeal Y.base.R) n ≫
        eqToHom (congrArg (fun A : Deformation.Artin.FormalBase S => Spec (.of A.R)) hbase))
    (i : siteObject B S hS hN (A.truncationToS n) ⟶
      Deformation.Artin.baseOver B S hS A hA)
    (hi : i.left.hom = AlgebraicGeometry.adicThickeningι A.R (maximalIdeal A.R) n) :
    p.IsHomLift i t := by
  subst A
  apply IsHomLift.of_fac p _ _ (Y.level_eq n) hx
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  rw [hi]
  exact ht.symm

/-- Two lifts of morphisms over isomorphic base maps are related by a lift of the isomorphism. -/
private theorem exists_iso_of_isHomLift_of_baseIso
    {C E : Type*} [Category C] [Category E] {p : E ⥤ C}
    (hp : p.IsFiberedInGroupoids) {c c' d : C} (g : c' ≅ c)
    (i : c ⟶ d) (i' : c' ⟶ d) (h : i' = g.hom ≫ i)
    {x y z : E} (r : x ⟶ z) (s : y ⟶ z)
    (hr : p.IsHomLift i r) (hs : p.IsHomLift i' s) :
    ∃ e : y ≅ x, e.hom ≫ r = s ∧ p.IsHomLift g.hom e.hom := by
  have := hr
  have := hs
  let f := eqToHom (IsHomLift.domain_eq p i' s) ≫ g.hom ≫
    eqToHom (IsHomLift.domain_eq p i r).symm
  have hf : f ≫ p.map r = p.map s := by
    rw [IsHomLift.fac' p i r, IsHomLift.fac' p i' s]
    simp [f, h]
  obtain ⟨a, ⟨ha, har⟩, _⟩ := hp.unique_lift r s f hf
  have ha' : p.IsHomLift g.hom a :=
    IsHomLift.of_fac' p _ _ (IsHomLift.domain_eq p i' s)
      (IsHomLift.domain_eq p i r) ha
  have : IsIso (p.map a) := by rw [ha]; dsimp [f]; infer_instance
  have := stronglyCartesian_of_fibered hp a
  have : IsIso a := Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map a) a
  exact ⟨asIso a, har, ha'⟩

/-- A formal level is isomorphic to a restriction along its canonical quotient map. -/
theorem formal_restriction_iso
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (hp : p.IsFiberedInGroupoids) (Y : Deformation.Artin.FormalObject B S hS p)
    (A : Deformation.Artin.FormalBase S) (hbase : Y.base = A)
    (hA : B.Contains (Spec (.of A.R))) (n : ℕ)
    (hN : B.Contains (A.truncation n))
    (x : F) (hx : p.obj x = Deformation.Artin.baseOver B S hS A hA)
    (t : Y.level n ⟶ x)
    (ht : (eqToHom (Y.level_eq n).symm ≫ p.map t ≫ eqToHom hx).left.hom =
      AlgebraicGeometry.adicThickeningι Y.base.R (maximalIdeal Y.base.R) n ≫
        eqToHom (congrArg (fun A : Deformation.Artin.FormalBase S => Spec (.of A.R)) hbase))
    (y : p.Fiber (siteObject B S hS hN (A.truncationToS n)))
    (i : siteObject B S hS hN (A.truncationToS n) ⟶
      Deformation.Artin.baseOver B S hS A hA)
    (hi : i.left.hom = AlgebraicGeometry.adicThickeningι A.R (maximalIdeal A.R) n)
    (r : y.1 ⟶ x) (hr : p.IsHomLift i r) :
    ∃ e : Y.level n ≅ y.1, e.hom ≫ r = t ∧
      p.IsHomLift (𝟙 (siteObject B S hS hN (A.truncationToS n))) e.hom := by
  have htt := formal_restriction_isHomLift Y A hbase hA n hN x hx t ht i hi
  simpa using exists_iso_of_isHomLift_of_baseIso hp (Iso.refl _) i i (by simp) r t hr htt

theorem restriction_iso_of_baseIso
    {C E : Type*} [Category C] [Category E] {p : E ⥤ C}
    (hp : p.IsFiberedInGroupoids) {c c' d : C} (g : c' ≅ c)
    (i : c ⟶ d) (i' : c' ⟶ d) (h : i' = g.hom ≫ i)
    {x y z : E} (r : x ⟶ z) (s : y ⟶ z)
    (hr : p.IsHomLift i r) (hs : p.IsHomLift i' s) :
    ∃ e : y ≅ x, e.hom ≫ r = s ∧ p.IsHomLift g.hom e.hom :=
  exists_iso_of_isHomLift_of_baseIso hp g i i' h r s hr hs

theorem exists_ringEquiv_of_specIso
    {R A : Type u} [CommRing R] [CommRing A]
    (e : Spec (.of R) ≅ Spec (.of A)) :
    ∃ f : A ≃+* R, Spec.map (CommRingCat.ofHom f.toRingHom) = e.hom := by
  let f := (Spec.fullyFaithful.preimageIso e).unop.commRingCatIsoToRingEquiv
  refine ⟨f, ?_⟩
  exact Spec.fullyFaithful.map_preimage e.hom

theorem exists_chosenBase_ringEquiv
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (x : Deformation.Artin.CompleteLocalObjectsFull B S hS p)
    (A : Deformation.Artin.FormalBase S) (hA : B.Contains (Spec (.of A.R)))
    (hx : p.obj x.1 = Deformation.Artin.baseOver B S hS A hA) :
    ∃ e : A.R ≃+* (Deformation.Artin.chosenBase B S hS p x).R,
      Spec.map (CommRingCat.ofHom e.toRingHom) =
        (eqToHom (Deformation.Artin.chosenBase_eq B S hS p x).symm ≫ eqToHom hx).left.hom := by
  let e := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapIso
    ((eqToIso (Deformation.Artin.chosenBase_eq B S hS p x)).symm ≪≫ eqToIso hx)
  exact exists_ringEquiv_of_specIso e

/-- Pullbacks of an object along a compatible sequence of base maps form a tower. -/
private theorem exists_restriction_tower
    {C E : Type*} [Category C] [Category E] {p : E ⥤ C}
    (hp : p.IsFiberedInGroupoids) {c : C} (x : E) (hx : p.obj x = c)
    (b : ℕ → C) (d : ∀ n, b n ⟶ b (n + 1)) (i : ∀ n, b n ⟶ c)
    (hi : ∀ n, d n ≫ i (n + 1) = i n) :
    ∃ (y : ℕ → E) (r : ∀ n, y n ⟶ x) (t : ∀ n, y n ⟶ y (n + 1)),
      (∀ n, p.IsHomLift (i n) (r n)) ∧
      (∀ n, p.IsHomLift (d n) (t n)) ∧
      (∀ n, t n ≫ r (n + 1) = r n) := by
  classical
  choose y r hr using fun n => hp.exists_lift (i n) x hx
  let (n : ℕ) := hr n
  have hy (n : ℕ) := IsHomLift.domain_eq p (i n) (r n)
  have ht (n : ℕ) : ∃ t : y n ⟶ y (n + 1),
      p.IsHomLift (d n) t ∧ t ≫ r (n + 1) = r n := by
    let f := eqToHom (hy n) ≫ d n ≫ eqToHom (hy (n + 1)).symm
    have hf : f ≫ p.map (r (n + 1)) = p.map (r n) := by
      rw [IsHomLift.fac' p (i (n + 1)) (r (n + 1)),
        IsHomLift.fac' p (i n) (r n)]
      simp only [f, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (d n), hi n]
    obtain ⟨t, ⟨ht, htr⟩, _⟩ := hp.unique_lift (r (n + 1)) (r n) f hf
    exact ⟨t, IsHomLift.of_fac' p _ _ (hy n) (hy (n + 1)) ht, htr⟩
  choose t ht htr using ht
  exact ⟨y, r, t, hr, ht, htr⟩

/-- Restriction to infinitesimal neighborhoods can retain any prescribed complete base. -/
private theorem exists_formal_restriction
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (hp : p.IsFiberedInGroupoids) (A : Deformation.Artin.FormalBase S)
    (hA : B.Contains (Spec (.of A.R)))
    (hAn : ∀ n, B.Contains (A.truncation n))
    (x : F) (hx : p.obj x = Deformation.Artin.baseOver B S hS A hA) :
    ∃ (Y : Deformation.Artin.FormalObject B S hS p) (hY : Y.base = A)
      (r : ∀ n, Y.level n ⟶ x),
      (∀ n, Y.transition n ≫ r (n + 1) = r n) ∧
      (∀ n, (eqToHom (Y.level_eq n).symm ≫ p.map (r n) ≫ eqToHom hx).left.hom =
        AlgebraicGeometry.adicThickeningι Y.base.R (maximalIdeal Y.base.R) n ≫
          eqToHom (congrArg (fun A : Deformation.Artin.FormalBase S => Spec (.of A.R)) hY)) := by
  let i (n : ℕ) : Deformation.Artin.truncationOver B S hS A hAn n ⟶
      Deformation.Artin.baseOver B S hS A hA :=
    Over.homMk (ObjectProperty.homMk
      (AlgebraicGeometry.adicThickeningι A.R (maximalIdeal A.R) n)) (by rfl)
  have hi (n : ℕ) : Deformation.Artin.truncationOverSucc B S hS A hAn n ≫
      i (n + 1) = i n := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact AlgebraicGeometry.adicThickeningSucc_ι A.R (maximalIdeal A.R) n
  obtain ⟨y, r, t, hr, ht, htr⟩ := exists_restriction_tower hp x hx
    (Deformation.Artin.truncationOver B S hS A hAn)
    (Deformation.Artin.truncationOverSucc B S hS A hAn) i hi
  let (n : ℕ) := hr n
  let Y : Deformation.Artin.FormalObject B S hS p := {
    base := A
    contains := hAn
    level := y
    level_eq := fun n => IsHomLift.domain_eq p (i n) (r n)
    transition := t
    transition_lift := ht }
  refine ⟨Y, rfl, r, htr, fun n => ?_⟩
  have h := IsHomLift.fac p (i n) (r n)
  have h' := congrArg (fun f => f.left.hom) h.symm
  exact h'

/-- The structure morphism to `S` of the completed local ring at a finite type point is
locally of finite type and quasi-compact on its residue field. -/
public theorem completedFormalBase_residue_props
    {S : Scheme.{u}} (U : Over S) (u₀ : U.left)
    [IsLocallyNoetherian U.left] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) :
    LocallyOfFiniteType (AlgebraicGeometry.adicThickeningι
        (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)
        (maximalIdeal (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)) 0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
        U.left.fromSpecStalk u₀ ≫ U.hom) ∧
    QuasiCompact (AlgebraicGeometry.adicThickeningι
        (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)
        (maximalIdeal (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)) 0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
        U.left.fromSpecStalk u₀ ≫ U.hom) := by
  let L := U.left.presheaf.stalk u₀
  let C := AlgebraicGeometry.Scheme.completedLocalRing U.left u₀
  let f : L →+* C := algebraMap L C
  let e : ResidueField L ≃+* ResidueField C :=
    RingEquiv.ofBijective (ResidueField.map f)
      (AdicCompletion.residueField_map_bijective L)
  let j := Spec.map (CommRingCat.ofHom e.toRingHom)
  have hjiso : IsIso j := by
    show IsIso (Spec.map e.toCommRingCatIso.hom)
    infer_instance
  have hjopen : IsOpenImmersion j := inferInstance
  have hjft : LocallyOfFiniteType j := locallyOfFiniteType_of_isOpenImmersion j
  have hjqc : QuasiCompact j := quasiCompact_of_isIso j
  have := hu₀.1
  have := hu₀.2
  have hcomm : (CommRingCat.ofHom f) ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal C)) =
      CommRingCat.ofHom (IsLocalRing.residue (L : Type u)) ≫
        CommRingCat.ofHom e.toRingHom :=
    CommRingCat.hom_ext (ResidueField.map_comp_residue f).symm
  have hspec : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal C))) ≫
      Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue (L : Type u))) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map hcomm
  have hres : U.left.fromSpecResidueField u₀ =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue (L : Type u))) ≫
        U.left.fromSpecStalk u₀ := rfl
  have heq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal C))) ≫
      Spec.map (CommRingCat.ofHom f) ≫ U.left.fromSpecStalk u₀ ≫ U.hom =
      j ≫ U.left.fromSpecResidueField u₀ ≫ U.hom := by
    rw [hres, ← Category.assoc, hspec]
    exact Category.assoc _ _ _
  have hprops (J : Ideal C) (hJ : J = maximalIdeal C) :
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
        Spec.map (CommRingCat.ofHom f) ≫ U.left.fromSpecStalk u₀ ≫ U.hom) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
        Spec.map (CommRingCat.ofHom f) ≫ U.left.fromSpecStalk u₀ ≫ U.hom) := by
    subst J
    rw [heq]
    have hft : LocallyOfFiniteType (U.left.fromSpecResidueField u₀ ≫ U.hom) :=
      locallyOfFiniteType_comp (U.left.fromSpecResidueField u₀) U.hom
    have hqc : QuasiCompact (U.left.fromSpecResidueField u₀ ≫ U.hom) :=
      quasiCompact_comp (U.left.fromSpecResidueField u₀) U.hom
    exact ⟨@locallyOfFiniteType_comp _ _ _ j
        (U.left.fromSpecResidueField u₀ ≫ U.hom) hjft hft,
      @quasiCompact_comp _ _ _ j
        (U.left.fromSpecResidueField u₀ ≫ U.hom) hjqc hqc⟩
  exact hprops (maximalIdeal C ^ (0 + 1)) (by simp)

/-- The completion at a finite-type point, with its structure morphism to the base. -/
public noncomputable def completedFormalBase
    {S : Scheme.{u}} (U : Over S) (u₀ : U.left)
    [IsLocallyNoetherian U.left] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) :
    Deformation.Artin.FormalBase S where
  R := AlgebraicGeometry.Scheme.completedLocalRing U.left u₀
  commRing := inferInstance
  localRing := AlgebraicGeometry.Scheme.completedLocalRing_isLocal U.left u₀
  noetherian := AlgebraicGeometry.Scheme.completedLocalRing_isNoetherian U.left u₀
  complete := AlgebraicGeometry.Scheme.completedLocalRing_isAdicComplete U.left u₀
  toS := Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
      (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
    U.left.fromSpecStalk u₀ ≫ U.hom
  residueLocallyFiniteType := (completedFormalBase_residue_props U u₀ hu₀).1
  residueQuasiCompact := (completedFormalBase_residue_props U u₀ hu₀).2

/-- The ring of `completedFormalBase U u₀ hu₀` is the completed local ring of `U.left` at `u₀`. -/
public theorem completedFormalBase_R
    {S : Scheme.{u}} (U : Over S) (u₀ : U.left)
    [IsLocallyNoetherian U.left] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) :
    (completedFormalBase U u₀ hu₀).R = AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ :=
  rfl

/-- The structure morphism of `completedFormalBase U u₀ hu₀`: the spectrum of the completion maps
to the stalk at `u₀`, then to `U.left`, then to the base. -/
public theorem completedFormalBase_toS
    {S : Scheme.{u}} (U : Over S) (u₀ : U.left)
    [IsLocallyNoetherian U.left] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) :
    (completedFormalBase U u₀ hu₀).toS =
      Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
        U.left.fromSpecStalk u₀ ≫ U.hom :=
  rfl

/-- The `n`-th truncation of `completedFormalBase U u₀ hu₀` maps to the base through the closed
immersion into the spectrum of the completion, followed by its structure morphism. -/
public theorem completedFormalBase_truncationToS
    {S : Scheme.{u}} (U : Over S) (u₀ : U.left)
    [IsLocallyNoetherian U.left] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) (n : ℕ) :
    (completedFormalBase U u₀ hu₀).truncationToS n =
      AlgebraicGeometry.adicThickeningι
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)
          (maximalIdeal (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)) n ≫
        (Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
          U.left.fromSpecStalk u₀) ≫ U.hom := by
  show AlgebraicGeometry.adicThickeningι _ _ n ≫
      (completedFormalBase U u₀ hu₀).toS = _
  rw [completedFormalBase_toS, Category.assoc]
  rfl

/-- The base point of a scheme over `S` at a point is the image of that point. -/
public theorem basePoint_eq_hom_apply {S : Scheme.{u}} (U : Over S) (u₀ : U.left) :
    Deformation.Artin.basePoint U u₀ = U.hom u₀ :=
  (Scheme.Hom.comp_apply _ _ _).trans
    (congrArg (fun z => U.hom z) (Scheme.fromSpecResidueField_apply u₀ _))

/-- The completion at a point lies over the image of that point. -/
public theorem completedFormalBase_closedPoint
    {S : Scheme.{u}} (U : Over S) (u₀ : U.left)
    [IsLocallyNoetherian U.left] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) :
    (completedFormalBase U u₀ hu₀).toS
        (IsLocalRing.closedPoint (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)) =
      U.hom u₀ := by
  have : IsLocalHom (algebraMap (U.left.presheaf.stalk u₀)
      (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)) := inferInstance
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))))
        (IsLocalRing.closedPoint
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)) =
      IsLocalRing.closedPoint (U.left.presheaf.stalk u₀) :=
    AlgebraicGeometry.Spec_closedPoint
  have h2 : U.left.fromSpecStalk u₀
      (IsLocalRing.closedPoint (U.left.presheaf.stalk u₀)) = u₀ :=
    Scheme.fromSpecStalk_closedPoint
  have hcomp : (completedFormalBase U u₀ hu₀).toS
        (IsLocalRing.closedPoint
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)) =
      U.hom (U.left.fromSpecStalk u₀
        ((Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))))
          (IsLocalRing.closedPoint
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)))) :=
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.Hom.comp_apply _ _ _)
  refine hcomp.trans ?_
  exact congrArg (fun z => U.hom z)
    ((congrArg (fun z => U.left.fromSpecStalk u₀ z) h1).trans h2)

/-- A complete local base whose closed point lies over `s` is canonically an algebra
over the local ring of `S` at `s`, compatibly with the structure morphisms. -/
public theorem exists_stalk_algebra_of_formalBase
    {S : Scheme.{u}} (A : Deformation.Artin.FormalBase S) (s : S)
    (hs : A.toS (IsLocalRing.closedPoint A.R) = s) :
    ∃ f : (S.presheaf.stalk s : Type u) →+* A.R,
      Spec.map (CommRingCat.ofHom f) ≫ S.fromSpecStalk s = A.toS := by
  rw [← hs]
  exact ⟨(Scheme.stalkClosedPointTo A.toS).hom,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk A.toS⟩

/-- The Artinian reductions of a formal object form a compatible tower. -/
theorem exists_formal_reduction_tower
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p) (η : Deformation.FormalObject p) :
    ∃ (ηn : ℕ → Deformation.FormalObject p) (q : ∀ n, η ⟶ ηn n)
      (g : ∀ n, ηn (n + 1) ⟶ ηn n),
      (∀ n, Deformation.FormalObject.projection.IsHomLift
        (formalBaseQuotient η.base n) (q n)) ∧
      (∀ n, Deformation.FormalObject.projection.IsHomLift
        (Deformation.artinianToComplete.map
          (Deformation.AdicTruncation.transition η.base n)) (g n)) ∧
      ∀ n, q (n + 1) ≫ g n = q n := by
  classical
  choose ηn q hq using exists_formal_reduction hp η
  let Q := Deformation.FormalObject.projection (p := p)
  let hQ := Deformation.formalObjectProjection_isCofiberedInGroupoids p hp
  let (n : ℕ) : Q.IsHomLift (formalBaseQuotient η.base n) (q n) := hq n
  let (n : ℕ) : Q.IsStronglyCocartesian (formalBaseQuotient η.base n) (q n) :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hQ _ _ (hq n)
  let g n := Functor.IsStronglyCocartesian.map Q
    (formalBaseQuotient η.base (n + 1)) (q (n + 1))
    (formalBaseQuotient_transition η.base n).symm (q n)
  exact ⟨ηn, q, g, hq, fun n => inferInstance,
    fun n => Functor.IsStronglyCocartesian.fac _ _ _ _ _⟩

/-- Compatible maps to all positive adic quotients induce a map of complete local algebras. -/
private theorem exists_completeLocal_lift
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (R S : Deformation.CompleteLocalAlgCat Λ k)
    (f : ∀ n, R ⟶ Deformation.artinianToComplete.obj (Deformation.AdicTruncation.obj S n))
    (hf : ∀ n, f (n + 1) ≫ Deformation.artinianToComplete.map
      (Deformation.AdicTruncation.transition S n) = f n) :
    ∃ a : R ⟶ S, ∀ n, a ≫ formalBaseQuotient S n = f n := by
  let σ : ℕ → ℕ := fun n => n + 1
  have hσ : StrictMono σ := fun _ _ h => Nat.add_lt_add_right h 1
  let fn (n : ℕ) : R →+* S ⧸ maximalIdeal S ^ (n + 1) := (f n).hom.toRingHom
  have hfn : ∀ {n : ℕ}, (Ideal.Quotient.factorPow (maximalIdeal S)
      (Nat.le_succ (n + 1))).comp (fn (n + 1)) = fn n := by
    intro n
    exact congrArg (fun a => a.hom.toRingHom) (hf n)
  let a := IsAdicComplete.StrictMono.liftRingHom (maximalIdeal S) hσ fn hfn
  have ha (n : ℕ) (x : R) :
      Ideal.Quotient.mk (maximalIdeal S ^ (n + 1)) (a x) = (f n).hom x :=
    IsAdicComplete.StrictMono.mk_liftRingHom
      (I := maximalIdeal S) (ha := hσ) (f := fn) (hf := hfn) x
  let aΛ : R →ₐ[Λ] S := {
    __ := a
    commutes' := by
      intro r
      have H : (fun r : Λ => a (algebraMap Λ R r)) = algebraMap Λ S := by
        apply IsHausdorff.StrictMono.funext' (maximalIdeal S) hσ
        intro n r
        rw [ha]
        exact (f n).hom.commutes r
      exact congrFun H r }
  have ha₀ (x : R) :
      Ideal.Quotient.mk (Deformation.AdicTruncation.ideal S 0) (aΛ x) =
        (f 0).hom x := ha 0 x
  let aC : R ⟶ S := {
    hom := aΛ
    isLocal := ⟨fun x hx => by
      have hq := hx.map (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal S 0))
      change IsUnit (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal S 0) (aΛ x)) at hq
      rw [ha₀] at hq
      exact (f 0).isLocal.map_nonunit x hq⟩
    residue_comm := fun x => by
      rw [← Deformation.AdicTruncation.residueEquiv_residue_mk S 0 (aΛ x)]
      show (Deformation.AdicTruncation.obj S 0).residueEquiv
        (residue (Deformation.AdicTruncation.obj S 0)
          (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal S 0) (aΛ x))) = _
      rw [ha₀]
      exact (f 0).residue_comm x }
  refine ⟨aC, fun n => ?_⟩
  apply Deformation.CompleteLocalAlgCat.Hom.ext
  exact AlgHom.ext (ha n)

/-- A compatible family of maps to reductions determines its map on complete bases. -/
theorem exists_base_map_of_reduction_maps
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type*} [Category F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat Λ k}
    (ξ η : Deformation.FormalObject p)
    (ηn : ℕ → Deformation.FormalObject p)
    (hn : ∀ n, (ηn n).base =
      Deformation.artinianToComplete.obj (Deformation.AdicTruncation.obj η.base n))
    (g : ∀ n, ηn (n + 1) ⟶ ηn n)
    (hg : ∀ n, Deformation.FormalObject.projection.IsHomLift
      (Deformation.artinianToComplete.map
        (Deformation.AdicTruncation.transition η.base n)) (g n))
    (an : ∀ n, ξ ⟶ ηn n) (ha : ∀ n, an (n + 1) ≫ g n = an n) :
    ∃ a : ξ.base ⟶ η.base,
      ∀ n, a ≫ formalBaseQuotient η.base n = (an n).base ≫ eqToHom (hn n) := by
  apply exists_completeLocal_lift ξ.base η.base
    (fun n => (an n).base ≫ eqToHom (hn n))
  intro n
  let Q := Deformation.FormalObject.projection (p := p)
  let := hg n
  have hgn : (g n).base ≫ eqToHom (hn n) =
      eqToHom (hn (n + 1)) ≫ Deformation.artinianToComplete.map
        (Deformation.AdicTruncation.transition η.base n) :=
    (IsHomLift.commSq Q _ (g n)).w
  rw [Category.assoc, ← hgn, ← Category.assoc]
  show (an (n + 1) ≫ g n).base ≫ eqToHom (hn n) = _
  rw [ha]

/-- A bijective morphism of Artinian local algebras is an isomorphism. -/
theorem isIso_of_bijective_artinianLocalHom
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {R S : Deformation.ArtinianLocalAlgCat Λ k} (f : R ⟶ S)
    (hf : Function.Bijective f.hom) : IsIso f := by
  let e := AlgEquiv.ofBijective f.hom hf
  let g : S ⟶ R := {
    hom := e.symm.toAlgHom
    isLocal := IsLocalHom.of_surjective _ e.symm.surjective
    residue_comm := fun s => by
      show R.residueEquiv (residue R (e.symm s)) = S.residueEquiv (residue S s)
      have h := f.residue_comm (e.symm s)
      change S.residueEquiv (residue S (e (e.symm s))) =
        R.residueEquiv (residue R (e.symm s)) at h
      simpa only [AlgEquiv.apply_symm_apply] using h.symm }
  let eC : R ≅ S := {
    hom := f
    inv := g
    hom_inv_id := by
      apply Deformation.ArtinianLocalAlgCat.hom_ext
      exact AlgHom.ext e.symm_apply_apply
    inv_hom_id := by
      apply Deformation.ArtinianLocalAlgCat.hom_ext
      exact AlgHom.ext e.apply_symm_apply }
  exact eC.isIso_hom

end Deformation.Artin

end
