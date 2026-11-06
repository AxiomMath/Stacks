module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedPullbackTensorChain
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatTensorComplexGeneral
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Stacks 07A4 on affine representables, in the derived category

For a morphism of ringed topoi `f : X ⟶ Y` and functors `G : Mod(A) ⥤ Mod(𝒪_Y)`,
`G' : Mod(A') ⥤ Mod(𝒪_X)` with `G ⋙ f^* ≅ (A' ⊗_A -) ⋙ G'`, whose derived functors `Φ`, `Φ'` are
related by an isomorphism `β : Lf^* Φ ≅ Φ'(- ⊗ᴸ_A A')` computed degreewise on complexes, the
derived pullback of `Φ(K)` is computed by the degreewise pullback of `G K` when `G K` is K-flat
with flat terms. This is the input from which Stacks 07A4 is compared with `β` on affine
representables.

## Main results

* `Stacks.Sheaves.DerivedPullback.derivedPullback_compQFactors_flatPullbackIso`
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorCompat_left`,
  `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorCompat_right`: the two composites of the
  compatibility of Stacks 07A4 with `β`, read on total complexes.
* `Stacks.Sheaves.DerivedPullback.exists_derivedPullbackTensorCompat`: the compatibility, up to a
  unit, for an abstract morphism of ringed topoi.
* `AlgebraicGeometry.Space.exists_representedAffineDerivedPullbackTensorCompat`: the case of affine
  representables.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u c c'

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

namespace Stacks.Generic

/-- Inverting a commutative square of isomorphisms around one of its sides. -/
theorem inv_inv_comp_eq_of_comp_eq {C : Type*} {_ : Category C} {X Y Z T S R : C} (a : X ≅ Y)
    (b : Y ≅ Z) (c : Z ⟶ T) (x : X ⟶ S) (y : S ≅ R) (z : R ≅ T)
    (h : x ≫ y.hom ≫ z.hom = a.hom ≫ b.hom ≫ c) :
    b.inv ≫ a.inv ≫ x = c ≫ z.inv ≫ y.inv := by
  calc b.inv ≫ a.inv ≫ x = b.inv ≫ a.inv ≫ (x ≫ y.hom ≫ z.hom) ≫ z.inv ≫ y.inv := by simp
    _ = c ≫ z.inv ≫ y.inv := by
      rw [h]
      simp

/-- The bookkeeping of the left-hand composite of the compatibility of Stacks 07A4 with a base
change isomorphism, for arbitrary morphisms. -/
theorem left_chain_eq {C : Type*} {_ : Category C}
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ p₁ p₂ p₃ p₄ : C}
    (a : o₀ ⟶ o₁) (b : o₁ ⟶ o₂) (c : o₂ ⟶ o₃) (d : o₃ ⟶ o₄) (e : o₄ ⟶ o₅) (fi : o₅ ⟶ o₆)
    (m : o₆ ⟶ o₇) (k : o₇ ⟶ o₈) (x : o₅ ⟶ p₁) (fi' : p₁ ⟶ o₇) (b' : o₁ ⟶ o₃) (qw : o₄ ⟶ p₁)
    (F : o₀ ⟶ p₂) (Qg : p₂ ⟶ p₃) (qinv : p₃ ⟶ p₁) (Qp : p₂ ⟶ p₄) (Qe : p₄ ⟶ p₃) (fQ' : p₃ ⟶ o₇)
    (e1 : fi ≫ m = x ≫ fi') (e3 : b ≫ c = b') (e4 : e ≫ x = qw)
    (lc : a ≫ b' ≫ d ≫ qw = F ≫ Qg ≫ qinv) (hQ : Qg = Qp ≫ Qe) (e2 : fQ' = qinv ≫ fi') :
    a ≫ b ≫ c ≫ d ≫ e ≫ fi ≫ m ≫ k = F ≫ Qp ≫ Qe ≫ fQ' ≫ k := by
  rw [reassoc_of% e1, reassoc_of% e3, reassoc_of% e4,
    show a ≫ b' ≫ d ≫ qw ≫ fi' ≫ k = (a ≫ b' ≫ d ≫ qw) ≫ fi' ≫ k by simp only [Category.assoc],
    lc, e2, hQ]
  simp only [Category.assoc]

/-- The bookkeeping of the right-hand composite of the compatibility of Stacks 07A4 with a base
change isomorphism, for arbitrary morphisms. -/
theorem right_chain_eq {C : Type*} {_ : Category C}
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ q₁ q₂ q₃ q₄ q₅ q₆ q₇ q₈ q₉ q₁₀ q₁₁ : C}
    (A07 : o₀ ⟶ o₁) (bP : o₁ ⟶ o₂) (bN : o₂ ⟶ o₃) (B1DD : o₃ ⟶ o₄) (PhiDc : o₄ ⟶ o₆)
    (pDcP : o₄ ⟶ o₅) (pDcN : o₅ ⟶ o₆) (sP : o₃ ⟶ o₇) (B1QD : o₇ ⟶ o₅) (sN : o₇ ⟶ o₈)
    (B1QQ : o₈ ⟶ o₆) (fqP : o₈ ⟶ q₁) (fqN : q₁ ⟶ q₂) (kX : q₂ ⟶ q₃) (Qt' : q₃ ⟶ q₄)
    (fQi : q₄ ⟶ q₅) (Φκ : q₅ ⟶ o₆) (lfP : o₁ ⟶ q₆) (lfN : q₆ ⟶ q₇) (flP : q₇ ⟶ q₈)
    (flN : q₈ ⟶ q₉) (qπP : q₉ ⟶ q₁₀) (qπN : q₁₀ ⟶ q₂) (LfTY : o₀ ⟶ q₁₁) (A07G : q₁₁ ⟶ q₇)
    {r₁ r₂ r₃ : C} (kXpb : q₉ ⟶ r₁) (Qmbm : r₁ ⟶ q₃) (LfκY : q₁₁ ⟶ r₂) (flat : r₂ ⟶ r₃)
    (QΘ : r₃ ⟶ r₁) (Qch : r₃ ⟶ q₄)
    (hsplit : PhiDc = pDcP ≫ pDcN) (h1a : sP ≫ B1QD = B1DD ≫ pDcP)
    (h1b : sN ≫ B1QQ = B1QD ≫ pDcN) (h2 : B1QQ = fqP ≫ fqN ≫ kX ≫ Qt' ≫ fQi ≫ Φκ)
    (h3 : bP ≫ bN ≫ sP ≫ sN ≫ fqP ≫ fqN = lfP ≫ lfN ≫ flP ≫ flN ≫ qπP ≫ qπN)
    (h4 : A07 ≫ lfP ≫ lfN = LfTY ≫ A07G) (h5 : qπP ≫ qπN ≫ kX = kXpb ≫ Qmbm)
    (h6 : A07G ≫ flP ≫ flN ≫ kXpb = LfκY ≫ flat ≫ QΘ) (h7 : Qch = QΘ ≫ Qmbm ≫ Qt') :
    A07 ≫ bP ≫ bN ≫ B1DD ≫ PhiDc = LfTY ≫ LfκY ≫ flat ≫ Qch ≫ fQi ≫ Φκ := by
  have e1 : B1DD ≫ PhiDc = sP ≫ sN ≫ fqP ≫ fqN ≫ kX ≫ Qt' ≫ fQi ≫ Φκ := by
    rw [hsplit, ← reassoc_of% h1a, ← h1b, h2]
  rw [e1]
  have e2 : bP ≫ bN ≫ sP ≫ sN ≫ fqP ≫ fqN ≫ kX ≫ Qt' ≫ fQi ≫ Φκ =
      lfP ≫ lfN ≫ flP ≫ flN ≫ kXpb ≫ Qmbm ≫ Qt' ≫ fQi ≫ Φκ := by
    simp only [← Category.assoc] at h3 ⊢
    rw [h3]
    simp only [Category.assoc]
    rw [reassoc_of% h5]
  rw [e2, reassoc_of% h4, h7, reassoc_of% h6]
  simp only [Category.assoc]

/-- Interleaved images of two triple composites under a bifunctor agree as soon as the triple
composites agree. -/
theorem bifunctor_interleave_eq {C D E : Type*} {_ : Category C} {_ : Category D} {_ : Category E}
    (F : C ⥤ D ⥤ E) {X₀ X₁ X₂ X₃ X₁' X₂' : C} {Y₀ Y₁ Y₂ Y₃ Y₁' Y₂' : D}
    (a₁ : X₀ ⟶ X₁) (a₂ : X₁ ⟶ X₂) (a₃ : X₂ ⟶ X₃) (a₁' : X₀ ⟶ X₁') (a₂' : X₁' ⟶ X₂')
    (a₃' : X₂' ⟶ X₃) (b₁ : Y₀ ⟶ Y₁) (b₂ : Y₁ ⟶ Y₂) (b₃ : Y₂ ⟶ Y₃) (b₁' : Y₀ ⟶ Y₁')
    (b₂' : Y₁' ⟶ Y₂') (b₃' : Y₂' ⟶ Y₃)
    (ha : a₁ ≫ a₂ ≫ a₃ = a₁' ≫ a₂' ≫ a₃') (hb : b₁ ≫ b₂ ≫ b₃ = b₁' ≫ b₂' ≫ b₃') :
    (F.map a₁).app Y₀ ≫ (F.obj X₁).map b₁ ≫ (F.map a₂).app Y₁ ≫ (F.obj X₂).map b₂ ≫
        (F.map a₃).app Y₂ ≫ (F.obj X₃).map b₃ =
      (F.map a₁').app Y₀ ≫ (F.obj X₁').map b₁' ≫ (F.map a₂').app Y₁' ≫ (F.obj X₂').map b₂' ≫
        (F.map a₃').app Y₂' ≫ (F.obj X₃).map b₃' := by
  have key : ∀ {X₁ X₂ : C} {Y₁ Y₂ : D} (a₁ : X₀ ⟶ X₁) (a₂ : X₁ ⟶ X₂) (a₃ : X₂ ⟶ X₃)
      (b₁ : Y₀ ⟶ Y₁) (b₂ : Y₁ ⟶ Y₂) (b₃ : Y₂ ⟶ Y₃),
      (F.map a₁).app Y₀ ≫ (F.obj X₁).map b₁ ≫ (F.map a₂).app Y₁ ≫ (F.obj X₂).map b₂ ≫
        (F.map a₃).app Y₂ ≫ (F.obj X₃).map b₃ =
      (F.map (a₁ ≫ a₂ ≫ a₃)).app Y₀ ≫ (F.obj X₃).map (b₁ ≫ b₂ ≫ b₃) := by
    intro X₁ X₂ Y₁ Y₂ a₁ a₂ a₃ b₁ b₂ b₃
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc, NatTrans.naturality_assoc]
  rw [key, key, ha, hb]

/-- Cancelling an isomorphism at the end of a composite. -/
theorem comp_inv_hom_cancel {C : Type*} {_ : Category C} {X₀ X₁ X₂ X₃ X₄ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (i : X₄ ≅ X₃) : (a ≫ b) ≫ (c ≫ i.inv) ≫ i.hom = a ≫ b ≫ c := by
  simp

/-- Cancelling the second half of a composite of isomorphisms. -/
theorem comp_trans_inv_cancel {C : Type*} {_ : Category C} {W V Z P P' P'' M : C} (L₁ : W ≅ V)
    (L₂ : V ≅ Z) (A : P ≅ P') (B : P' ≅ P'') (C' : Z ≅ P'') (x : P ⟶ M) (y : M ⟶ P')
    (hxy : x ≫ y = A.hom) :
    ((L₁ ≪≫ L₂) ≪≫ (A ≪≫ B ≪≫ C'.symm).symm).hom ≫ x ≫ y ≫ B.hom = L₁.hom ≫ L₂.hom ≫ C'.hom := by
  rw [reassoc_of% hxy]
  simp

/-- Cancelling the image of an isomorphism followed by the image of its inverse. -/
theorem map_inv_hom_assoc {C D : Type*} {_ : Category C} {_ : Category D} (F : C ⥤ D)
    {X₁ X₂ : C} (e : X₁ ≅ X₂) {W : D} (x : F.obj X₁ ⟶ W) : F.map e.hom ≫ F.map e.inv ≫ x = x := by
  rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]

/-- The bookkeeping of the compatibility of Stacks 07A4 with a base change isomorphism: the two
composites, after an isomorphism `Dd`, agree up to a central endomorphism. -/
theorem final_chain_eq {C : Type*} {_ : Category C}
    {o₀ o₁ o₂ o₃ o₄ s₁ s₂ s₃ p₁ p₂ p₃ p₄ p₅ : C}
    (l₁ : o₀ ⟶ o₁) (l₂ : o₁ ⟶ o₂) (l₃ : o₂ ⟶ o₃) (r₁ : o₀ ⟶ s₁) (r₂ : s₁ ⟶ s₂) (r₃ : s₂ ⟶ s₃)
    (r₄ : s₃ ⟶ o₃) (Φc : o₃ ⟶ o₃) (Dd : o₃ ⟶ o₄) (hDd : IsIso Dd) (Φc' : o₄ ⟶ o₄)
    (n₁ : o₀ ⟶ p₁) (n₂ : p₁ ⟶ p₂) (n₃ : p₂ ⟶ p₃) (q₁ : p₃ ⟶ p₄) (q₂ : p₃ ⟶ p₄) (qc : p₄ ⟶ p₄)
    (fi : p₄ ⟶ p₅) (k : p₅ ⟶ o₄)
    (H1 : l₁ ≫ l₂ ≫ l₃ ≫ Dd = n₁ ≫ n₂ ≫ n₃ ≫ q₁ ≫ fi ≫ k)
    (H2 : r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ Dd = n₁ ≫ n₂ ≫ n₃ ≫ q₂ ≫ fi ≫ k) (hC : q₂ = q₁ ≫ qc)
    (hc1 : Φc ≫ Dd = Dd ≫ Φc') (hc2 : fi ≫ k ≫ Φc' = qc ≫ fi ≫ k) :
    l₁ ≫ l₂ ≫ l₃ ≫ Φc = r₁ ≫ r₂ ≫ r₃ ≫ r₄ := by
  have := hDd
  rw [← cancel_mono Dd]
  simp only [Category.assoc]
  rw [hc1, reassoc_of% H1, hc2, H2, hC]
  simp only [Category.assoc]

/-- A scalar multiple of the identity is central, after any functor. -/
theorem map_smul_id_comp {R : Type*} [Semiring R] {C D : Type*} {_ : Category C}
    {_ : Category D} {_ : Preadditive C} {_ : Linear R C} (F : C ⥤ D) {X Y : C} (d : X ⟶ Y)
    (c : R) : F.map (c • 𝟙 X) ≫ F.map d = F.map d ≫ F.map (c • 𝟙 Y) := by
  rw [← F.map_comp, ← F.map_comp, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    Category.comp_id]

/-- Reassociating a composite of two and four morphisms. -/
theorem assoc_two_four {C : Type*} {_ : Category C} {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (f : X₅ ⟶ X₆) :
    (a ≫ b) ≫ c ≫ d ≫ e ≫ f = a ≫ b ≫ c ≫ d ≫ e ≫ f := by
  simp only [Category.assoc]

/-- Reassociating a composite of three and two morphisms. -/
theorem assoc_three_two {C : Type*} {_ : Category C} {X₀ X₁ X₂ X₃ X₄ X₅ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) :
    (a ≫ b ≫ c) ≫ d ≫ e = a ≫ b ≫ c ≫ d ≫ e := by
  simp only [Category.assoc]

/-- Reassociating a composite of four and two morphisms. -/
theorem assoc_four_two {C : Type*} {_ : Category C} {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (f : X₅ ⟶ X₆) :
    (a ≫ b ≫ c ≫ d) ≫ e ≫ f = a ≫ b ≫ c ≫ d ≫ e ≫ f := by
  simp only [Category.assoc]

end Stacks.Generic

namespace RingTheory.TorIndependence

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 068I on K-flat complexes, inverted**: the inverse of the derived tensor base-change
isomorphism, read through the comparisons of derived extension of scalars, is the inverse of the
monoidality of degreewise extension of scalars. -/
theorem extensionTensorIso_inv_app_comparison {A A' : Type u} [CommRing A] [CommRing A']
    (φ : A →+* A') (P N : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) (hN : N.KFlat)
    [IsIso ((extensionComparison φ).app P)] [IsIso ((extensionComparison φ).app N)]
    [IsIso ((extensionComparison φ).app (P ⊗ N))] :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ).functor.map
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).comparison P N hP hN).inv ≫
      (extensionTensorIso φ).iso.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) ≫
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.map
          ((extensionComparison φ).app P)).app
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).functor.obj
            (DerivedCategory.Q.obj N)) ≫
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.obj
          (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P))).map ((extensionComparison φ).app N)) =
      (extensionComparison φ).app (P ⊗ N) ≫
        DerivedCategory.Q.map (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).inv ≫
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').comparison _ _
          (kFlat_mapCochainComplex φ P hP) (kFlat_mapCochainComplex φ N hN)).inv := by
  obtain ⟨hFK, hFL, e, he, heq⟩ := (extensionTensorIso φ).comparison P N hP hN
  have heμ := CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom
    φ P N he
  have t1 : ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').toGeneral.comparison
      _ _ hFK hFL).hom =
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').comparison _ _
        (kFlat_mapCochainComplex φ P hP) (kFlat_mapCochainComplex φ N hN)).hom := rfl
  have t3 : DerivedCategory.Q.map e.hom =
      (DerivedCategory.Q.mapIso (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P
          N)).hom := by
    rw [heμ]
    rfl
  rw [t1, t3] at heq
  exact Stacks.Generic.inv_inv_comp_eq_of_comp_eq
    ((extensionTensorIso φ).iso.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N))
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        φ).functor.mapIso
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).comparison P N hP hN))
    ((extensionComparison φ).app (P ⊗ N)) _
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').comparison _ _
      (kFlat_mapCochainComplex φ P hP) (kFlat_mapCochainComplex φ N hN))
    (DerivedCategory.Q.mapIso (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N))
    ((Category.assoc _ _ _).trans heq)

end RingTheory.TorIndependence

namespace Stacks.Sheaves.DerivedPullback

open AlgebraicGeometry Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
    Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

section Derived

variable {X : AlgebraicGeometry.RingedTopos.{u, c, u}}
    {Y : AlgebraicGeometry.RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- `Φ(QK) ≅ Q(G K)`, from `Φ(QK) ≅ Qh(quotient(G K))`. -/
abbrev compQFactors {A : Type u} [CommRing A] {W : Type*} [Category W] [Abelian W]
    [HasDerivedCategory W] {G : ModuleCat.{u} A ⥤ W} [G.Additive]
    {Φ : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory W}
    (fac : DerivedCategory.Q ⋙ Φ ≅ (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomotopyCategory.quotient _ _) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ Φ ≅ G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  fac ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _)

/-- **The derived pullback of `Φ(QK)` is computed by the degreewise pullback of `G K`**, through
the base change isomorphism `β`, for `G K` K-flat with flat terms. -/
theorem derivedPullback_compQFactors_flatPullbackIso {A A' : Type u} [CommRing A] [CommRing A']
    (φ : A →+* A')
    {G : ModuleCat.{u} A ⥤ SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))}
            {G' : ModuleCat.{u} A' ⥤ SheafOfModules.{u}
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))}
    [G.Additive] [G'.Additive] [(ModuleCat.extendScalars.{u, u, u} φ).Additive]
        [((ModuleCat.extendScalars.{u, u, u} φ) ⋙ G').Additive]
    {Φ : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))}
    {Φ' : DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))}
    (fac : DerivedCategory.Q ⋙ Φ ≅ (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomotopyCategory.quotient _ _) ⋙ DerivedCategory.Qh)
    (fac' : DerivedCategory.Q ⋙ Φ' ≅ (G'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomotopyCategory.quotient _ _) ⋙ DerivedCategory.Qh)
    (r : G ⋙ f.toModulesHom.pullbackModules ≅ (ModuleCat.extendScalars.{u, u, u} φ) ⋙ G')
    (β : Φ ⋙ (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f) ≅
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            φ).functor ⋙ Φ')
    (hβ : ∀ K : CochainComplex (ModuleCat.{u} A) ℤ,
      β.hom.app (DerivedCategory.Q.obj K) ≫ Φ'.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).comparison.app K) =
        (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map (fac.hom.app K) ≫
          (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f).app
            ((HomotopyCategory.quotient _ _).obj
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          DerivedCategory.Qh.map ((Stacks.Homology.homotopyEdgeIso r).hom.app K) ≫
          fac'.inv.app (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O)
      (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X i)) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
        ((compQFactors fac).hom.app K) ≫
        (Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackIso f
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) hK hflat).hom ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso
              (Iso.refl ((ModuleCat.extendScalars.{u, u, u} φ) ⋙ G'))
              (ComplexShape.up ℤ)).symm).hom.app K) =
      β.hom.app (DerivedCategory.Q.obj K) ≫ Φ'.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).comparison.app K) ≫
        (compQFactors fac').hom.app (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) := by
  have h := congrArg (· ≫ (compQFactors fac').hom.app
    (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) (hβ K)
  simp only [Category.assoc] at h
  refine Eq.trans ?_ (h.symm.trans (Category.assoc _ _ _))
  unfold Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackIso
  simp only [compQFactors, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp, Category.assoc,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp]
  refine congrArg (_ ≫ ·) ?_
  rw [← Functor.map_comp_assoc,
    show (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).hom.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).inv = 𝟙 _ from
      Iso.hom_inv_id ((DerivedCategory.quotientCompQhIso _).app _)]
  refine Eq.trans (congrArg (· ≫ _) ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
    f).map_id _)) ?_
  refine Eq.trans (Category.id_comp _) ?_
  calc _ = (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ _).obj
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
          (((f.toModulesHom.pullbackModules).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl
            (ModuleCat.extendScalars.{u, u, u} φ ⋙ G')) (ComplexShape.up ℤ)).symm).hom.app K) := by
        rw [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, CategoryTheory.Functor.map_comp]
        first | rfl | (simp only [asIso_hom, Iso.app_hom]; done) | (simp only [asIso_hom, Iso.app_hom]; rfl)
    _ = (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ _).obj
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        DerivedCategory.Qh.map ((Stacks.Homology.homotopyEdgeIso r).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))).hom.app
          ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)) :=
        congrArg (_ ≫ ·) (DerivedCategory.quotientCompQhIso_hom_naturality
          ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl
              (ModuleCat.extendScalars.{u, u, u} φ ⋙ G'))
                  (ComplexShape.up ℤ)).symm).hom.app K)).symm
    _ = _ := by rw [Iso.inv_hom_id_app_assoc]


/-- The derived pullback of `Q(s)` followed by the comparison `Lf^* ⟶ f^*`, for a chain map `s`
out of a K-flat complex with flat terms, through the computation of Stacks 06YY. -/
theorem derivedPullback_map_Q_comparison
    {Y₁ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
        {Y₂ : CochainComplex (SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) ℤ}
    {Z : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) ℤ} (s : Y₁ ⟶ Y₂)
    (w : (((f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y₂) ⟶ Z)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) Y₁)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (Y₁.X i)) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map (DerivedCategory.Q.map s) ≫
        (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
            ((DerivedCategory.quotientCompQhIso
                (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)
                    Y.O)))).inv.app Y₂) ≫
        (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f).app
            ((HomotopyCategory.quotient _ _).obj Y₂) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map w) =
      (Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackIso f Y₁ hK hflat).hom ≫
        DerivedCategory.Q.map ((((f.toModulesHom.pullbackModules).mapHomologicalComplex
            (ComplexShape.up ℤ))).map s ≫ w) ≫
        (DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)
                X.O)))).inv.app Z := by
  have ha : DerivedCategory.Q.map s ≫ (DerivedCategory.quotientCompQhIso _).inv.app Y₂ =
      (DerivedCategory.quotientCompQhIso _).inv.app Y₁ ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map s) :=
    DerivedCategory.quotientCompQhIso_inv_naturality s
  have hb := (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)
  have hd := DerivedCategory.quotientCompQhIso_hom_naturality
    ((((f.toModulesHom.pullbackModules).mapHomologicalComplex
      (ComplexShape.up ℤ))).map s ≫ w)
  unfold Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackIso
  simp only [Functor.comp_map] at hb
  rw [← Functor.map_comp_assoc, ha, Functor.map_comp_assoc, reassoc_of% hb]
  have key : DerivedCategory.Qh.map (((f.toModulesHom.pullbackModules).mapHomotopyCategory
      (ComplexShape.up ℤ)).map ((HomotopyCategory.quotient _ _).map s)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map w) =
      (DerivedCategory.quotientCompQhIso _).hom.app _ ≫
        DerivedCategory.Q.map ((((f.toModulesHom.pullbackModules).mapHomologicalComplex
          (ComplexShape.up ℤ))).map s ≫ w) ≫
        (DerivedCategory.quotientCompQhIso _).inv.app Z := by
    calc _ = DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((((f.toModulesHom.pullbackModules).mapHomologicalComplex
            (ComplexShape.up ℤ))).map s ≫ w)) := by
          rw [(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp,
              DerivedCategory.Qh.map_comp]
          rfl
      _ = _ := by
          rw [← reassoc_of% hd, Iso.hom_inv_id_app]
          exact (Category.comp_id _).symm
  exact (congrArg (fun x => _ ≫ _ ≫ x) key).trans (Stacks.Generic.assoc_three_two _ _ _ _ _).symm

/-- **Stacks 07A4 at K-flat complexes with flat terms, against its two halves**: followed by the
computation of `Lf^*` in each factor and the K-flat comparison, it is the K-flat comparison
followed by the computation of `Lf^*` of the total complex and Stacks 03EL. -/
theorem derivedPullbackTensorIso_hom_app_comp_comparison
    (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
    (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L.X i)) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso f TX TY).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
      (TX.tensor.map (Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackIso f K hK
          hflatK).hom).app
        ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).obj
            (DerivedCategory.Q.obj L)) ≫
      (TX.tensor.obj (DerivedCategory.Q.obj
          ((Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.pullbackComplex f).obj K))).map
        (Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackIso f L hL hflatL).hom ≫
      (TX.comparison _ _ (Stacks.Cohomology.DerivedPullbackOfToposHom.kFlat_pullbackComplex'
          f K hK hflatK)
        (Stacks.Cohomology.DerivedPullbackOfToposHom.kFlat_pullbackComplex' f L hL hflatL)).hom =
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
          (TY.comparison K L hK hL).hom ≫
        (Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackIso f
          (HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
              (ComplexShape.up ℤ))
          (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hL)
          (isFlat_tensorComplex_X_general Y.O K L hflatK hflatL)).hom ≫
        DerivedCategory.Q.map
          (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorTotalComplexIso f
              K L).hom := by
  rw [Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_hom_app_model f TX TY K L
    hK hL hflatK hflatL]
  unfold Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorModelIso
    Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorModelLeft
    Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorModelRight
  refine Stacks.Generic.comp_trans_inv_cancel _ _ _ _ _ _ _ ?_
  rfl

omit [X.J.HasSheafCompose (forget RingCat)] [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [X.J.HasSheafCompose (forget AddCommGrpCat)] [HasSheafify X.J (Type u)] in
/-- A scalar of `A'` acting on a complex of `A'`-modules commutes with `Φ'(Q(-)) ≅ Q(G'(-))`. -/
theorem compQFactors_inv_smul {A' : Type u} [CommRing A']
    {G' : ModuleCat.{u} A' ⥤ SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))} [G'.Additive]
    {Φ' : DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))}
    (fac' : DerivedCategory.Q ⋙ Φ' ≅ (G'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomotopyCategory.quotient _ _) ⋙ DerivedCategory.Qh)
    (T : CochainComplex (ModuleCat.{u} A') ℤ) {Z : DerivedCategory (ModuleCat.{u} A')}
    (k : DerivedCategory.Q.obj T ⟶ Z) (c : A') :
    (compQFactors fac').inv.app T ≫ Φ'.map k ≫ Φ'.map (c • 𝟙 Z) =
      DerivedCategory.Q.map ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).map (c • 𝟙 T)) ≫
        (compQFactors fac').inv.app T ≫ Φ'.map k := by
  have hn := (compQFactors fac').inv.naturality (c • 𝟙 T)
  have hQ : DerivedCategory.Q.map (c • 𝟙 T) = c • 𝟙 _ := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, hQ, ← Stacks.Generic.map_smul_id_comp Φ' k c]


section Compat

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  {G : ModuleCat.{u} A ⥤ SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))}
          {G' : ModuleCat.{u} A' ⥤ SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))}
  [G.Additive] [G'.Additive] [(ModuleCat.extendScalars.{u, u, u} φ).Additive]
      [((ModuleCat.extendScalars.{u, u, u} φ) ⋙ G').Additive]
  {Φ : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))}
  {Φ' : DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))}
  (fac : DerivedCategory.Q ⋙ Φ ≅ (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomotopyCategory.quotient _ _) ⋙ DerivedCategory.Qh)
  (fac' : DerivedCategory.Q ⋙ Φ' ≅ (G'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomotopyCategory.quotient _ _) ⋙ DerivedCategory.Qh)
  (r : G ⋙ f.toModulesHom.pullbackModules ≅ (ModuleCat.extendScalars.{u, u, u} φ) ⋙ G')
  (β : Φ ⋙ (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f) ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor ⋙ Φ')
  (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)
  (B1 : Φ ⋙ TY.tensor ⋙ (Functor.whiskeringLeft _ _ _).obj Φ ≅
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor ⋙
        (Functor.whiskeringRight _ _ _).obj Φ)
  (t : ∀ P N : CochainComplex (ModuleCat.{u} A) ℤ,
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ))
        ≅ HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
  (hGk : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ, P.KFlat →
    Stacks.SheafOfModules.IsKFlat Y.O ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))

omit [HasSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The comparison through extension of scalars, at the tensor product of complexes. -/
theorem Q_map_pullbackExtensionTotalChain (P N : CochainComplex (ModuleCat.{u} A) ℤ)
    {Y₁ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (s : Y₁ ⟶ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A))
            (ComplexShape.up ℤ))) :
    DerivedCategory.Q.map (((f.toModulesHom.pullbackModules).mapHomologicalComplex
        (ComplexShape.up ℤ)).map s ≫
      ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
            (Iso.refl ((ModuleCat.extendScalars.{u, u, u} φ) ⋙ G'))
            (ComplexShape.up ℤ)).symm).hom.app (P ⊗ N) ≫
        (G'.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).inv)) =
      DerivedCategory.Q.map (((f.toModulesHom.pullbackModules).mapHomologicalComplex
          (ComplexShape.up ℤ)).map s) ≫
        DerivedCategory.Q.map (pullbackExtensionTotalChain f r
          (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N)) :=
  DerivedCategory.Q.map_comp _ _

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The comparison through Stacks 03EL on total complexes, after the inverse of the degreewise
pullback of `t`. -/
theorem Q_map_pullbackTensorTotalChain (P N : CochainComplex (ModuleCat.{u} A) ℤ)
    (t'' : (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                P) (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj N) (curriedTensor (ModuleCat.{u} A'))
                        (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
        ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                N)) (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :
    DerivedCategory.Q.map (((f.toModulesHom.pullbackModules).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (t P N).inv ≫
        pullbackTensorTotalChain f r (t P N) t'') =
      DerivedCategory.Q.map
          (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorTotalComplexIso f
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
            ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
                (Functor.mapHomologicalComplexCompIso
                    (Iso.refl ((ModuleCat.extendScalars.{u, u, u} φ) ⋙ G'))
                    (ComplexShape.up ℤ)).symm).hom.app P)
                        ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
                            (Functor.mapHomologicalComplexCompIso
                                (Iso.refl ((ModuleCat.extendScalars.{u, u, u} φ) ⋙ G'))
                                (ComplexShape.up ℤ)).symm).hom.app N)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map t''.inv := by
  have hch := Stacks.Generic.map_inv_hom_assoc
    ((f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ))
    (t P N).symm (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso f.toModulesHom
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)).hom
  unfold pullbackTensorTotalChain
  exact (congrArg DerivedCategory.Q.map ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) hch))).trans
    ((DerivedCategory.Q.map_comp _ _).trans (congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _)))

/-- **The left-hand composite of the compatibility of Stacks 07A4 with `β`**, at K-flat complexes
with flat terms: `Lf^*(Φ P ⊗ Φ N) ≅ Lf^*Φ(P ⊗ N) ≅ Φ'(D(P ⊗ N)) ≅ Φ'(D P ⊗ D N)`, read through
the degreewise pullback of the total complex and the comparison through extension of scalars. -/
theorem derivedPullbackTensorCompat_left
    (hβ : ∀ K : CochainComplex (ModuleCat.{u} A) ℤ,
      β.hom.app (DerivedCategory.Q.obj K) ≫ Φ'.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).comparison.app K) =
        (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map (fac.hom.app K) ≫
          (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f).app
            ((HomotopyCategory.quotient _ _).obj
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          DerivedCategory.Qh.map ((Stacks.Homology.homotopyEdgeIso r).hom.app K) ≫
          fac'.inv.app (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))
    (hB1 : ∀ (P N : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) (hN : N.KFlat),
      (B1.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N) =
        (TY.tensor.map ((compQFactors fac).hom.app P)).app (Φ.obj (DerivedCategory.Q.obj N)) ≫
        (TY.tensor.obj (DerivedCategory.Q.obj
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))).map
                ((compQFactors fac).hom.app N) ≫
        (TY.comparison ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (hGk P hP) (hGk N hN)).hom ≫
        DerivedCategory.Q.map (t P N).inv ≫ (compQFactors fac).inv.app
            (HomologicalComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A))
                (ComplexShape.up ℤ)) ≫
        Φ.map ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).comparison P
            N hP hN).inv)
    (P N : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) (hN : N.KFlat)
    (hT : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        (HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)))
    (hTf : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O)
        ((HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)).X i)) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
        ((B1.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)) ≫
        β.hom.app (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
            (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N)) ≫
        Φ'.map ((RingTheory.TorIndependence.extensionTensorIso φ).iso.inv.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
        Φ'.map (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.map
            ((RingTheory.TorIndependence.extensionComparison φ).app P)).app
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                φ).functor.obj (DerivedCategory.Q.obj N)) ≫
          ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.obj
              (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P))).map
                      ((RingTheory.TorIndependence.extensionComparison φ).app N)) =
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
          ((TY.tensor.map ((compQFactors fac).hom.app P)).app (Φ.obj (DerivedCategory.Q.obj N)) ≫
          (TY.tensor.obj (DerivedCategory.Q.obj
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))).map
                  ((compQFactors fac).hom.app N)) ≫
        (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
            (TY.comparison ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (hGk P hP) (hGk N hN)).hom ≫
        (Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackIso f
            (HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) hT hTf).hom ≫
        DerivedCategory.Q.map (((f.toModulesHom.pullbackModules).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
            (t P N).inv ≫ pullbackExtensionTotalChain f r
              (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N)) ≫
        (compQFactors fac').inv.app (HomologicalComplex.mapBifunctor
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                P) (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj N) (curriedTensor (ModuleCat.{u} A'))
                        (ComplexShape.up ℤ)) ≫
        Φ'.map ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').comparison
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                P) (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj N)
          (RingTheory.TorIndependence.kFlat_mapCochainComplex φ P hP)
          (RingTheory.TorIndependence.kFlat_mapCochainComplex φ N hN)).inv := by
  rw [hB1 P N hP hN]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_))
  have hPN : (P ⊗ N).KFlat := CochainComplex.DerivedTensor.isKFlat_tensor.{u, u} P N hP hN
  have := RingTheory.TorIndependence.isIso_extensionComparison_app φ P hP
  have := RingTheory.TorIndependence.isIso_extensionComparison_app φ N hN
  have := RingTheory.TorIndependence.isIso_extensionComparison_app φ (P ⊗ N) hPN
  have hnat := β.hom.naturality
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).comparison P N hP hN).inv
  simp only [Functor.comp_map] at hnat
  rw [reassoc_of% hnat]
  have tail : β.hom.app (DerivedCategory.Q.obj (P ⊗ N)) ≫
      Φ'.map ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.map ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).comparison
          P N hP hN).inv) ≫
      Φ'.map ((RingTheory.TorIndependence.extensionTensorIso φ).iso.inv.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      Φ'.map (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.map
          ((RingTheory.TorIndependence.extensionComparison φ).app P)).app
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).functor.obj (DerivedCategory.Q.obj N)) ≫
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.obj
            (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P))).map
                    ((RingTheory.TorIndependence.extensionComparison φ).app N)) =
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map (fac.hom.app (P ⊗ N)) ≫
        (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ _).obj
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (P ⊗ N))) ≫
        DerivedCategory.Qh.map ((Stacks.Homology.homotopyEdgeIso r).hom.app (P ⊗ N)) ≫
        fac'.inv.app (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (P ⊗ N)) ≫
        Φ'.map (DerivedCategory.Q.map (CochainComplex.ExtendScalars.extendScalarsMonoidalIso
            φ P N).inv) ≫
        Φ'.map ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').comparison
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                P) (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj N)
          (RingTheory.TorIndependence.kFlat_mapCochainComplex φ P hP)
          (RingTheory.TorIndependence.kFlat_mapCochainComplex φ N hN)).inv := by
    calc _ = β.hom.app (DerivedCategory.Q.obj (P ⊗ N)) ≫
          Φ'.map ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).functor.map ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
                  A).comparison P N hP hN).inv ≫
            (RingTheory.TorIndependence.extensionTensorIso φ).iso.inv.app
                (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) ≫
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.map
                ((RingTheory.TorIndependence.extensionComparison φ).app P)).app
                ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                    φ).functor.obj (DerivedCategory.Q.obj N)) ≫
              ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.obj
                  (DerivedCategory.Q.obj
                      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                          (ComplexShape.up ℤ)).obj P))).map
                ((RingTheory.TorIndependence.extensionComparison φ).app N))) :=
          congrArg (β.hom.app _ ≫ ·)
            ((Φ'.map_comp _ _).trans (congrArg (Φ'.map _ ≫ ·) (Φ'.map_comp _ _))).symm
      _ = β.hom.app (DerivedCategory.Q.obj (P ⊗ N)) ≫
          Φ'.map ((RingTheory.TorIndependence.extensionComparison φ).app (P ⊗ N) ≫
            DerivedCategory.Q.map
              (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).inv ≫
            ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').comparison _ _
                (RingTheory.TorIndependence.kFlat_mapCochainComplex φ P hP)
              (RingTheory.TorIndependence.kFlat_mapCochainComplex φ N hN)).inv) :=
          congrArg (fun x => β.hom.app (DerivedCategory.Q.obj (P ⊗ N)) ≫ Φ'.map x)
            (RingTheory.TorIndependence.extensionTensorIso_inv_app_comparison φ P N hP hN)
      _ = _ := by
          rw [Φ'.map_comp, Φ'.map_comp]
          exact ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ (Φ'.map _ ≫ Φ'.map _)) (hβ (P ⊗ N)))).trans
            (Stacks.Generic.assoc_four_two _ _ _ _ _ _)
  refine Eq.trans (congrArg (fun x => _ ≫ _ ≫ x) tail) ?_
  have e1 : fac'.inv.app (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (P ⊗ N)) ≫
      Φ'.map (DerivedCategory.Q.map (CochainComplex.ExtendScalars.extendScalarsMonoidalIso
          φ P N).inv) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).inv)) ≫
      fac'.inv.app (HomologicalComplex.mapBifunctor
          (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
          (curriedTensor (ModuleCat.{u} A')) (ComplexShape.up ℤ)) :=
    (fac'.inv.naturality (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).inv).symm
  have e2 : (compQFactors fac').inv.app (HomologicalComplex.mapBifunctor
      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
      (curriedTensor (ModuleCat.{u} A')) (ComplexShape.up ℤ)) =
      (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))).inv.app
              ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (HomologicalComplex.mapBifunctor
                      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                          (ComplexShape.up ℤ)).obj P)
                              (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                                  (ComplexShape.up ℤ)).obj N) (curriedTensor (ModuleCat.{u} A'))
                                      (ComplexShape.up ℤ))) ≫
        fac'.inv.app (HomologicalComplex.mapBifunctor
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                P) (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj N) (curriedTensor (ModuleCat.{u} A'))
                        (ComplexShape.up ℤ)) := by
    simp [compQFactors]
  have e3 : (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
      ((compQFactors fac).inv.app (P ⊗ N)) ≫
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map (fac.hom.app (P ⊗ N)) =
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
          ((DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)
                  Y.O)))).inv.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (P ⊗ N))) := by
    rw [← Functor.map_comp]
    congr 1
    simp [compQFactors]
  have lc := derivedPullback_map_Q_comparison f (t P N).inv
    ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl ((ModuleCat.extendScalars.{u, u, u} φ) ⋙ G'))
          (ComplexShape.up ℤ)).symm).hom.app (P ⊗ N) ≫
      (G'.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).inv)
    hT hTf
  have e4 : DerivedCategory.Qh.map ((Stacks.Homology.homotopyEdgeIso r).hom.app (P ⊗ N)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).inv)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso
              (Iso.refl ((ModuleCat.extendScalars.{u, u, u} φ) ⋙ G'))
              (ComplexShape.up ℤ)).symm).hom.app (P ⊗ N) ≫
        (G'.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N).inv)) := by
    rw [← DerivedCategory.Qh.map_comp, Stacks.Homology.homotopyEdgeIso_hom_app]
    exact congrArg DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map_comp _ _).symm
  exact Stacks.Generic.left_chain_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1 e3 e4
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq lc) (by heq_congr))))
    (Q_map_pullbackExtensionTotalChain f φ r P N (t P N).inv) e2


/-- **The right-hand composite of the compatibility of Stacks 07A4 with `β`**, at K-flat complexes
with flat terms: `Lf^*(Φ P ⊗ Φ N) ≅ Lf^*Φ P ⊗ Lf^*Φ N ≅ Φ' D P ⊗ Φ' D N ≅ Φ'(D P ⊗ D N)`, read
through the degreewise pullback of the total complex and the comparison through Stacks 03EL. -/
theorem derivedPullbackTensorCompat_right
    (hβ : ∀ K : CochainComplex (ModuleCat.{u} A) ℤ,
      β.hom.app (DerivedCategory.Q.obj K) ≫ Φ'.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).comparison.app K) =
        (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map (fac.hom.app K) ≫
          (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f).app
            ((HomotopyCategory.quotient _ _).obj
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          DerivedCategory.Qh.map ((Stacks.Homology.homotopyEdgeIso r).hom.app K) ≫
          fac'.inv.app (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))
    (B1' : Φ' ⋙ TX.tensor ⋙ (Functor.whiskeringLeft _ _ _).obj Φ' ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor ⋙
          (Functor.whiskeringRight _ _ _).obj Φ')
    (t' : ∀ P N : CochainComplex (ModuleCat.{u} A') ℤ,
      (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (HomologicalComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A'))
              (ComplexShape.up ℤ)) ≅
        HomologicalComplex.mapBifunctor ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))
    (hGk' : ∀ P : CochainComplex (ModuleCat.{u} A') ℤ, P.KFlat →
      Stacks.SheafOfModules.IsKFlat X.O ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (hB1' : ∀ (P N : CochainComplex (ModuleCat.{u} A') ℤ) (hP : P.KFlat) (hN : N.KFlat),
      (B1'.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N) =
        (TX.tensor.map ((compQFactors fac').hom.app P)).app (Φ'.obj (DerivedCategory.Q.obj N)) ≫
        (TX.tensor.obj (DerivedCategory.Q.obj
            ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))).map
          ((compQFactors fac').hom.app N) ≫
        (TX.comparison ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
          (hGk' P hP) (hGk' N hN)).hom ≫
        DerivedCategory.Q.map (t' P N).inv ≫ (compQFactors fac').inv.app
            (HomologicalComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A'))
                (ComplexShape.up ℤ)) ≫
        Φ'.map ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').comparison P
            N hP hN).inv)
    (P N : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) (hN : N.KFlat)
    (hPk : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (hPf : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O)
        (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X i))
    (hNk : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    (hNf : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O)
        (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N).X i))
    (hT : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        (HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)))
    (hTf : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O)
        ((HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)).X i)) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso f TX TY).hom.app
        (Φ.obj (DerivedCategory.Q.obj P), Φ.obj (DerivedCategory.Q.obj N)) ≫
      (TX.tensor.map (β.hom.app (DerivedCategory.Q.obj P))).app
          ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).obj
              (Φ.obj (DerivedCategory.Q.obj N))) ≫
      (TX.tensor.obj
          (Φ'.obj ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).functor.obj (DerivedCategory.Q.obj P)))).map
                  (β.hom.app (DerivedCategory.Q.obj N)) ≫
      (B1'.hom.app ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.obj (DerivedCategory.Q.obj P))).app
              ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                  φ).functor.obj (DerivedCategory.Q.obj N)) ≫
      Φ'.map (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.map
          ((RingTheory.TorIndependence.extensionComparison φ).app P)).app
              ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                  φ).functor.obj (DerivedCategory.Q.obj N)) ≫
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.obj
            (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P))).map
                    ((RingTheory.TorIndependence.extensionComparison φ).app N)) =
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
          ((TY.tensor.map ((compQFactors fac).hom.app P)).app (Φ.obj (DerivedCategory.Q.obj N)) ≫
          (TY.tensor.obj (DerivedCategory.Q.obj
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))).map
                  ((compQFactors fac).hom.app N)) ≫
        (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
            (TY.comparison ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (hGk P hP) (hGk N hN)).hom ≫
        (Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackIso f
            (HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) hT hTf).hom ≫
        DerivedCategory.Q.map (((f.toModulesHom.pullbackModules).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
            (t P N).inv ≫ pullbackTensorTotalChain f r (t P N)
                (t' (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj P)
                        (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                            (ComplexShape.up ℤ)).obj N))) ≫
        (compQFactors fac').inv.app (HomologicalComplex.mapBifunctor
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                P) (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj N) (curriedTensor (ModuleCat.{u} A'))
                        (ComplexShape.up ℤ)) ≫
        Φ'.map ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').comparison
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                P) (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj N)
          (RingTheory.TorIndependence.kFlat_mapCochainComplex φ P hP)
          (RingTheory.TorIndependence.kFlat_mapCochainComplex φ N hN)).inv := by
  have hEP := RingTheory.TorIndependence.kFlat_mapCochainComplex φ P hP
  have hEN := RingTheory.TorIndependence.kFlat_mapCochainComplex φ N hN
  have hpP := Stacks.Cohomology.DerivedPullbackOfToposHom.kFlat_pullbackComplex' f
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hPk hPf
  have hpN := Stacks.Cohomology.DerivedPullbackOfToposHom.kFlat_pullbackComplex' f
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) hNk hNf
  exact Stacks.Generic.right_chain_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Φ'.map_comp _ _)
    (NatTrans.congr_app (B1'.hom.naturality
        ((RingTheory.TorIndependence.extensionComparison φ).app P))
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                φ).functor.obj (DerivedCategory.Q.obj N)))
    ((B1'.hom.app (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            P))).naturality ((RingTheory.TorIndependence.extensionComparison φ).app N))
    (hB1' (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) hEP hEN)
    (Stacks.Generic.bifunctor_interleave_eq TX.tensor _ _ _ _ _ _ _ _ _ _ _ _
      (derivedPullback_compQFactors_flatPullbackIso f φ fac fac' r β hβ P hPk hPf).symm
      (derivedPullback_compQFactors_flatPullbackIso f φ fac fac' r β hβ N hNk hNf).symm)
    ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso f TX TY).hom.naturality
      ((((compQFactors fac).hom.app P, (compQFactors fac).hom.app N)) :
        ((Φ.obj (DerivedCategory.Q.obj P), Φ.obj (DerivedCategory.Q.obj N)) : _ × _) ⟶
            (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
                DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)))).symm
    (TX.comparison_naturality ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
            (Iso.refl ((ModuleCat.extendScalars.{u, u, u} φ) ⋙ G'))
            (ComplexShape.up ℤ)).symm).hom.app P)
                ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
                    (Functor.mapHomologicalComplexCompIso
                        (Iso.refl ((ModuleCat.extendScalars.{u, u, u} φ) ⋙ G'))
                        (ComplexShape.up ℤ)).symm).hom.app N) hpP
                            (hGk' (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                                (ComplexShape.up ℤ)).obj P) hEP) hpN
      (hGk' (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N) hEN))
    (derivedPullbackTensorIso_hom_app_comp_comparison f TX TY
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) hPk hNk hPf hNf)
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      (Q_map_pullbackTensorTotalChain f φ r t P N
          (t' (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              P) (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj N))))
      (by heq_congr))))


/-- **Stacks 07A4 on affine representables is compatible with the base change isomorphism `β`,
up to a unit.** There is a unit `c : A'` such that for all K-flat complexes `P`, `N` of `A`-modules
with flat terms,
`Lf^*(Φ P ⊗ Φ N) ≅ Lf^*Φ(P ⊗ N) ≅ Φ'(D(P ⊗ N)) ≅ Φ'(D P ⊗ D N)`, followed by multiplication by
`c`, is `Lf^*(Φ P ⊗ Φ N) ≅ Lf^*Φ P ⊗ Lf^*Φ N ≅ Φ' D P ⊗ Φ' D N ≅ Φ'(D P ⊗ D N)`. -/
theorem exists_derivedPullbackTensorCompat
    (hβ : ∀ K : CochainComplex (ModuleCat.{u} A) ℤ,
      β.hom.app (DerivedCategory.Q.obj K) ≫ Φ'.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).comparison.app K) =
        (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map (fac.hom.app K) ≫
          (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f).app
            ((HomotopyCategory.quotient _ _).obj
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          DerivedCategory.Qh.map ((Stacks.Homology.homotopyEdgeIso r).hom.app K) ≫
          fac'.inv.app (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))
    (hB1 : ∀ (P N : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) (hN : N.KFlat),
      (B1.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N) =
        (TY.tensor.map ((compQFactors fac).hom.app P)).app (Φ.obj (DerivedCategory.Q.obj N)) ≫
        (TY.tensor.obj (DerivedCategory.Q.obj
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))).map
                ((compQFactors fac).hom.app N) ≫
        (TY.comparison ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (hGk P hP) (hGk N hN)).hom ≫
        DerivedCategory.Q.map (t P N).inv ≫ (compQFactors fac).inv.app
            (HomologicalComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A))
                (ComplexShape.up ℤ)) ≫
        Φ.map ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).comparison P
            N hP hN).inv)
    (B1' : Φ' ⋙ TX.tensor ⋙ (Functor.whiskeringLeft _ _ _).obj Φ' ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor ⋙
          (Functor.whiskeringRight _ _ _).obj Φ')
    (t' : ∀ P N : CochainComplex (ModuleCat.{u} A') ℤ,
      (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (HomologicalComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A'))
              (ComplexShape.up ℤ)) ≅
        HomologicalComplex.mapBifunctor ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))
    (hGk' : ∀ P : CochainComplex (ModuleCat.{u} A') ℤ, P.KFlat →
      Stacks.SheafOfModules.IsKFlat X.O ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (hB1' : ∀ (P N : CochainComplex (ModuleCat.{u} A') ℤ) (hP : P.KFlat) (hN : N.KFlat),
      (B1'.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N) =
        (TX.tensor.map ((compQFactors fac').hom.app P)).app (Φ'.obj (DerivedCategory.Q.obj N)) ≫
        (TX.tensor.obj (DerivedCategory.Q.obj
            ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))).map
          ((compQFactors fac').hom.app N) ≫
        (TX.comparison ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
          (hGk' P hP) (hGk' N hN)).hom ≫
        DerivedCategory.Q.map (t' P N).inv ≫ (compQFactors fac').inv.app
            (HomologicalComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A'))
                (ComplexShape.up ℤ)) ≫
        Φ'.map ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').comparison P
            N hP hN).inv)
    (τ : ∀ M N : ModuleCat.{u} A, G.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).obj (G.obj N))
    (hτr : ∀ (M : ModuleCat.{u} A) {N N' : ModuleCat.{u} A} (g : N ⟶ N'),
      G.map (M ◁ g) ≫ (τ M N').hom = (τ M N).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (G.obj M)).map (G.map g))
    (hτl : ∀ {M M' : ModuleCat.{u} A} (g : M ⟶ M') (N : ModuleCat.{u} A),
      G.map (g ▷ N) ≫ (τ M' N).hom = (τ M N).hom ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map (G.map g)).app (G.obj N)))
    (τ' : ∀ M N : ModuleCat.{u} A', G'.obj (M ⊗ N) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).obj (G'.obj N))
    (hτr' : ∀ (M : ModuleCat.{u} A') {N N' : ModuleCat.{u} A'} (g : N ⟶ N'),
      G'.map (M ◁ g) ≫ (τ' M N').hom = (τ' M N).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G'.obj M)).map (G'.map g))
    (hτl' : ∀ {M M' : ModuleCat.{u} A'} (g : M ⟶ M') (N : ModuleCat.{u} A'),
      G'.map (g ▷ N) ≫ (τ' M' N).hom = (τ' M N).hom ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (G'.map g)).app (G'.obj N)))
    (hG' : G'.FullyFaithful)
    (ht : ∀ (P N : CochainComplex (ModuleCat.{u} A) ℤ) p q n h,
      G.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor (ModuleCat.{u} A))
          (ComplexShape.up ℤ) p q n h) ≫ (t P N).hom.f n =
        (τ (P.X p) (N.X q)).hom ≫ HomologicalComplex.ιMapBifunctor
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p q n h)
    (ht' : ∀ (P N : CochainComplex (ModuleCat.{u} A) ℤ) p q n h,
      G'.map (HomologicalComplex.ιMapBifunctor
          (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
          (curriedTensor (ModuleCat.{u} A')) (ComplexShape.up ℤ) p q n h) ≫
              (t' (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)
                      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                          (ComplexShape.up ℤ)).obj N)).hom.f n =
        (τ' ((ModuleCat.extendScalars.{u, u, u} φ).obj (P.X p))
            ((ModuleCat.extendScalars.{u, u, u} φ).obj (N.X q))).hom ≫
          HomologicalComplex.ιMapBifunctor
              ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj P))
            ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj N)) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
                        (ComplexShape.up ℤ) p q n h)
    (hGkf : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ, P.KFlat → (∀ n, Module.Flat A (P.X n)) →
      CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
        ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O)
            (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X i)) :
    ∃ c : A', IsUnit c ∧ ∀ (P N : CochainComplex (ModuleCat.{u} A) ℤ) (_ : P.KFlat) (_ : N.KFlat)
      (_ : ∀ n, Module.Flat A (P.X n)) (_ : ∀ n, Module.Flat A (N.X n)),
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
          ((B1.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)) ≫
          β.hom.app (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
              (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N)) ≫
          Φ'.map ((RingTheory.TorIndependence.extensionTensorIso φ).iso.inv.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫ Φ'.map (c • 𝟙 _) =
        (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso f TX TY).hom.app
            (Φ.obj (DerivedCategory.Q.obj P), Φ.obj (DerivedCategory.Q.obj N)) ≫
          (TX.tensor.map (β.hom.app (DerivedCategory.Q.obj P))).app
              ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).obj
                  (Φ.obj (DerivedCategory.Q.obj N))) ≫
          (TX.tensor.obj
              (Φ'.obj
                  ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                      φ).functor.obj (DerivedCategory.Q.obj P)))).map
                          (β.hom.app (DerivedCategory.Q.obj N)) ≫
          (B1'.hom.app
              ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                  φ).functor.obj (DerivedCategory.Q.obj P))).app
                      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u,
                          u} φ).functor.obj (DerivedCategory.Q.obj N)) := by
  obtain ⟨c, hcu, hc⟩ := exists_pullbackTensorTotalChain_eq f φ r τ hτr hτl τ' hτr' hτl' hG'
    t ht
        (fun P N => t' (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
          (fun P N => ht' P N)
    (fun P N => CochainComplex.ExtendScalars.extendScalarsMonoidalIso φ P N)
    (fun P N p q n h =>
      CochainComplex.ExtendScalars.extendScalars_map_ι_extendScalarsMonoidalIso_inv φ P N p q n h)
  refine ⟨c, hcu, fun P N hP hN hPf hNf => ?_⟩
  obtain ⟨hPk, hPfl⟩ := hGkf P hP hPf
  obtain ⟨hNk, hNfl⟩ := hGkf N hN hNf
  have hT := Stacks.SheafOfModules.kFlat_tensorComplex Y.O hPk hNk
  have hTf := isFlat_tensorComplex_X_general Y.O
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) hPfl hNfl
  have H1 := derivedPullbackTensorCompat_left (f := f) (φ := φ) (fac := fac) (fac' := fac') (r := r)
    (β := β) (TY := TY) (B1 := B1) (t := t) (hGk := hGk) hβ hB1 P N hP hN hT hTf
  have H2 := derivedPullbackTensorCompat_right (f := f) (φ := φ) (fac := fac)
      (fac' := fac') (r := r)
    (β := β) (TX := TX) (TY := TY) (t := t) (hGk := hGk) hβ B1' t' hGk' hB1' P N hP hN hPk hPfl
    hNk hNfl hT hTf
  have := RingTheory.TorIndependence.isIso_extensionComparison_app φ P hP
  have := RingTheory.TorIndependence.isIso_extensionComparison_app φ N hN
  have : IsIso (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.map
      ((RingTheory.TorIndependence.extensionComparison φ).app P)).app
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).functor.obj (DerivedCategory.Q.obj N))) :=
    NatIso.isIso_app_of_isIso _ _
  have : IsIso (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.obj
      (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P))).map
              ((RingTheory.TorIndependence.extensionComparison φ).app N)) :=
    Functor.map_isIso _ _
  have hDd : IsIso (Φ'.map (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
      A').tensor.map ((RingTheory.TorIndependence.extensionComparison φ).app P)).app
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).functor.obj (DerivedCategory.Q.obj N)) ≫
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A').tensor.obj
          (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))).map
                  ((RingTheory.TorIndependence.extensionComparison φ).app N))) :=
    Functor.map_isIso _ _
  have hC := congrArg (fun x => DerivedCategory.Q.map
    (((f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (t P N).inv ≫ x)) (hc P N)
  exact Stacks.Generic.final_chain_eq _ _ _ _ _ _ _ _ _ hDd _ _ _ _ _ _ _ _ _ H1 H2
    (hC.trans ((congrArg DerivedCategory.Q.map (Category.assoc _ _ _).symm).trans
      (DerivedCategory.Q.map_comp _ _)))
    (Stacks.Generic.map_smul_id_comp Φ' _ c) (compQFactors_inv_smul fac' _ _ c)

end Compat

end Derived

end Stacks.Sheaves.DerivedPullback



namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Concrete

variable (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- `AlgebraicGeometry.Space.representedAffineDerivedTensorBifunctorIso` at a pair of K-flat
complexes, as the explicit composite of the comparisons. -/
theorem representedAffineDerivedTensorBifunctorIso_hom_app_app_eq
    (P N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
        (hP : P.KFlat) (hN : N.KFlat) :
    ((representedAffineDerivedTensorBifunctorIso B S hS U).hom.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj N) =
      ((smallEtaleDerivedTensorProduct B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).tensor.map
              ((Stacks.Sheaves.DerivedPullback.compQFactors
                  (representedAffineToposDerivedFactors B S hS U)).hom.app P)).app
          ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)) ≫
        ((smallEtaleDerivedTensorProduct B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).tensor.obj
                (DerivedCategory.Q.obj (((representedAffineToposAssociated B S hS
                    U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))).map
                        ((Stacks.Sheaves.DerivedPullback.compQFactors
                            (representedAffineToposDerivedFactors B S hS U)).hom.app N) ≫
        ((smallEtaleDerivedTensorProduct B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).comparison
                (((representedAffineToposAssociated B S hS U).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj P)
                        (((representedAffineToposAssociated B S hS U).mapHomologicalComplex
                            (ComplexShape.up ℤ)).obj N)
                                (isKFlat_representedAffineToposAssociated B S hS U P hP)
          (isKFlat_representedAffineToposAssociated B S hS U N hN)).hom ≫
        DerivedCategory.Q.map (representedAffineToposTensorComplexIso B S hS U P N).inv ≫
        (Stacks.Sheaves.DerivedPullback.compQFactors
            (representedAffineToposDerivedFactors B S hS U)).inv.app
                (HomologicalComplex.mapBifunctor P N
                    (curriedTensor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
                    (ComplexShape.up ℤ)) ≫
        (representedAffineToposDerivedAssociated B S hS U).map
            ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
                Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).comparison P N hP hN).inv :=
  (representedAffineDerivedTensorBifunctorIso_hom_app_app B S hS U ⟨P, hP⟩ ⟨N, hN⟩).trans
    (Stacks.Generic.assoc_two_four _ _ _ _ _ _)

end Concrete


section ConcreteCompat

attribute [local instance] additive_extendScalars_representedAffineRingHom
  additive_pullbackModules_representedSpaceMap

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g₀ : U' ⟶ U)

/-- **Stacks 07A4 on affine representables, against the base change isomorphism, up to a
unit.** There is a unit `c : A'` such that, at all K-flat complexes `P`, `N` of `A`-modules with
flat terms, `Lg^*(Φ P ⊗ Φ N) ≅ Lg^*Φ(P ⊗ N) ≅ Φ'((P ⊗ N) ⊗ᴸ A') ≅ Φ'((P ⊗ᴸ A') ⊗ (N ⊗ᴸ A'))`
followed by `c` is `Lg^*(Φ P ⊗ Φ N) ≅ Lg^*Φ P ⊗ Lg^*Φ N ≅ Φ'(P ⊗ᴸ A') ⊗ Φ'(N ⊗ᴸ A')
≅ Φ'((P ⊗ᴸ A') ⊗ (N ⊗ᴸ A'))`. -/
theorem exists_representedAffineDerivedPullbackTensorCompat :
    ∃ c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤), IsUnit c ∧
      ∀ (P N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
        (_ : P.KFlat) (_ : N.KFlat)
        (_ : ∀ n, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (P.X n))
        (_ : ∀ n, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (N.X n)),
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀)).map
          (((representedAffineDerivedTensorBifunctorIso B S hS U).hom.app
              (DerivedCategory.Q.obj P)).app
          (DerivedCategory.Q.obj N)) ≫
        (representedAffineToposDerivedBaseChangeIso B S hS g₀).hom.app
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
                Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor.obj (DerivedCategory.Q.obj P)).obj
                    (DerivedCategory.Q.obj N)) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
            ((RingTheory.TorIndependence.extensionTensorIso
          (representedAffineCommRingCatHom B S hS g₀).hom).iso.inv.app
              (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
        (representedAffineToposDerivedAssociated B S hS U').map (c • 𝟙 _) =
      (smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀)).hom.app
          ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P),
              (representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)) ≫
        ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).map
          ((representedAffineToposDerivedBaseChangeIso B S hS g₀).hom.app
              (DerivedCategory.Q.obj P))).app
                  ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀)).obj
                      ((representedAffineToposDerivedAssociated B S hS U).obj
                          (DerivedCategory.Q.obj N))) ≫
        ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
          ((representedAffineToposDerivedAssociated B S hS U').obj
              ((representedAffineDerivedExtension B S hS g₀).functor.obj
                  (DerivedCategory.Q.obj P)))).map
                      ((representedAffineToposDerivedBaseChangeIso B S hS g₀).hom.app
                          (DerivedCategory.Q.obj N)) ≫
        ((representedAffineDerivedTensorBifunctorIso B S hS U').hom.app
            ((representedAffineDerivedExtension B S hS g₀).functor.obj
                (DerivedCategory.Q.obj P))).app
          ((representedAffineDerivedExtension B S hS g₀).functor.obj (DerivedCategory.Q.obj N)) :=
  Stacks.Sheaves.DerivedPullback.exists_derivedPullbackTensorCompat.{u, u + 1, u + 1}
      (f := (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g₀)))
    (φ := (representedAffineCommRingCatHom B S hS g₀).hom)
    (fac := representedAffineToposDerivedFactors B S hS U)
    (fac' := representedAffineToposDerivedFactors B S hS U')
    (r := representedAffineToposPullbackIso B S hS g₀)
        (β := (representedAffineToposDerivedBaseChangeIso B S hS g₀))
    (TX := smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
    (TY := smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (B1 := representedAffineDerivedTensorBifunctorIso B S hS U)
    (t := representedAffineToposTensorComplexIso B S hS U)
    (hGk := isKFlat_representedAffineToposAssociated B S hS U)
    (representedAffineToposDerivedBaseChangeIso_hom_app_comparison B S hS g₀)
    (representedAffineDerivedTensorBifunctorIso_hom_app_app_eq B S hS U)
    (representedAffineDerivedTensorBifunctorIso B S hS U')
    (representedAffineToposTensorComplexIso B S hS U')
    (isKFlat_representedAffineToposAssociated B S hS U')
    (representedAffineDerivedTensorBifunctorIso_hom_app_app_eq B S hS U')
    (representedAffineToposTensorIso B S hS U)
    (fun M _ _ g => representedAffineToposTensorIso_hom_naturality_right B S hS U M g)
    (fun g N => representedAffineToposTensorIso_hom_naturality_left B S hS U g N)
    (representedAffineToposTensorIso B S hS U')
    (fun M _ _ g => representedAffineToposTensorIso_hom_naturality_right B S hS U' M g)
    (fun g N => representedAffineToposTensorIso_hom_naturality_left B S hS U' g N)
    (representedAffineToposAssociatedFullyFaithful B S hS U')
    (fun _ _ p q n h => CategoryTheory.Functor.ι_mapBifunctorTotalIso_hom _ _ _ _ _ _ _ _ _
        _ _ _ p q n h)
    (fun _ _ p q n h => CategoryTheory.Functor.ι_mapBifunctorTotalIso_hom _ _ _ _ _ _ _ _ _
        _ _ _ p q n h)
    (fun P hP hPf => ⟨isKFlat_representedAffineToposAssociated B S hS U P hP,
      fun i => have := hPf i; isFlat_representedAffineAssociated_obj B S hS U (P.X i)⟩)

end ConcreteCompat

end AlgebraicGeometry.Space

end
