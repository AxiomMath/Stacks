module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsSingleDegree
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsSelfIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents

/-!
# The structure sheaf in one degree on an affine representable algebraic space

Let `U` be an object of the big fppf site over `S` with affine underlying scheme `Spec R`, and
write `Φ : D(R) ⥤ D(𝒪_{h_U})` for the associated module on derived categories (Stacks 08H1).
The object `Φ(R[p])` is the structure sheaf placed in degree `p`.  This file
computes its morphism sets and their behaviour under derived pullback:

* the endomorphisms of `Φ(R[p])` are the multiplications `Φ(s • 𝟙)` by the elements `s` of `R`,
  and they commute with each other;
* there are no nonzero morphisms `Φ(R[p]) ⟶ Φ(R[q])` for `p ≠ q`;
* for `g : U' ⟶ U` with `U'` affine and `φ : R ⟶ R'` the induced map of rings, the derived
  pullback `Lg^*Φ(R[p])` is isomorphic to `Φ(R'[p])`, by an isomorphism carrying `Lg^*Φ(s • 𝟙)`
  to `Φ(φ(s) • 𝟙)`.

These are the inputs of the affine case of Stacks 09RI for the structure sheaf: they identify
the system of endomorphism rings of the pullbacks of `Φ(R[p])` along a directed system of affine
representables with the system of their rings of global functions.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineUnitObj`: the object `Φ(R[p])`.
* `AlgebraicGeometry.Space.representedAffineUnitSmul`: multiplication by `s : R` on it.
* `AlgebraicGeometry.Space.representedAffineUnitPullbackIso`: `Lg^*Φ(R[p]) ≅ Φ(R'[p])`.

## Main results

* `AlgebraicGeometry.Space.bijective_representedAffineUnitSmul`: every endomorphism of `Φ(R[p])`
  is a unique multiplication.
* `AlgebraicGeometry.Space.representedAffineUnitObj_end_comm`: its endomorphisms commute.
* `AlgebraicGeometry.Space.subsingleton_hom_representedAffineUnitObj`: no morphisms between
  distinct degrees.
* `AlgebraicGeometry.Space.representedAffineUnitPullbackIso_conj`: derived pullback of a
  multiplication is the multiplication by the image under the map of rings.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.13.6 (Tag 08H1)](https://stacks.math.columbia.edu/tag/08H1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- **Conjugation by an isomorphism into an object with commutative endomorphisms does not depend
on the isomorphism.** -/
theorem CategoryTheory.conj_eq_conj_of_end_comm {C : Type*} [Category C] {M L : C}
    (hL : ∀ a b : L ⟶ L, a ≫ b = b ≫ a) (ι ι' : M ≅ L) (φ : M ⟶ M) :
    ι.inv ≫ φ ≫ ι.hom = ι'.inv ≫ φ ≫ ι'.hom := by
  have h1 : ι.inv ≫ φ ≫ ι.hom =
      ((ι.inv ≫ ι'.hom) ≫ (ι'.inv ≫ φ ≫ ι'.hom)) ≫ (ι'.inv ≫ ι.hom) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [h1, hL (ι.inv ≫ ι'.hom)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Conjugating the image of a morphism through a base change isomorphism.**  For
`β : Φ ⋙ L ≅ ext ⋙ Ψ` and `γ : ext X ≅ X'`, the conjugate of `L(Φ x)` by `β_X` followed by `Ψ γ`
is `Ψ y` as soon as the conjugate of `ext x` by `γ` is `y`. -/
theorem CategoryTheory.Iso.app_trans_mapIso_conj {C C' D E : Type*} [Category C] [Category C']
    [Category D] [Category E] {Φ : C ⥤ D} {L : D ⥤ E} {ext : C ⥤ C'} {Ψ : C' ⥤ E}
    (β : Φ ⋙ L ≅ ext ⋙ Ψ) {X : C} {X' : C'} (γ : ext.obj X ≅ X') (x : X ⟶ X) (y : X' ⟶ X')
    (hxy : γ.inv ≫ ext.map x ≫ γ.hom = y) :
    (β.app X ≪≫ Ψ.mapIso γ).inv ≫ L.map (Φ.map x) ≫ (β.app X ≪≫ Ψ.mapIso γ).hom = Ψ.map y := by
  have nat := β.hom.naturality x
  simp only [Functor.comp_map] at nat
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% nat, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, ← Functor.map_comp, hxy]

/-- Conjugating a multiplication by a scalar by an isomorphism gives the multiplication by the same
scalar. -/
theorem CategoryTheory.Iso.inv_comp_smul_id_comp_hom {R : Type*} [CommRing R] {C : Type*}
    [Category C] [Preadditive C] [Linear R C] {X Y : C} (γ : X ≅ Y) (r : R) :
    γ.inv ≫ (r • 𝟙 X) ≫ γ.hom = r • 𝟙 Y := by
  rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.inv_hom_id]

/-- **Multiplication by the elements of a commutative ring on the ring itself** is a bijection
onto its endomorphisms as a module. -/
theorem ModuleCat.bijective_smul_id (R : Type u) [CommRing R] :
    Function.Bijective (fun s : R => s • 𝟙 (ModuleCat.of R R)) := by
  refine ⟨fun s t h => ?_, fun f => ⟨f.hom 1, ?_⟩⟩
  · have := congrArg (fun φ : ModuleCat.of R R ⟶ ModuleCat.of R R => φ.hom 1) h
    simpa using this
  · ext
    simp

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Unit

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

/-- **The structure sheaf in degree `p` on an affine representable**, as `Φ(R[p])` for
`R = Γ(V, 𝒪)`, read in the derived category of `𝒪`-modules of the small étale ringed topos, the
category derived pullback is built on. -/
abbrev representedAffineUnitObj (p : ℤ) :
    @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)) _ _ (HasDerivedCategory.standard _) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  (representedAffineDerivedAssociated B S hS V).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) p).obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))

/-- **Multiplication by a global function** on `Φ(R[p])`. -/
def representedAffineUnitSmul (p : ℤ) (s : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    representedAffineUnitObj B S hS V p ⟶ representedAffineUnitObj B S hS V p :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  (representedAffineDerivedAssociated B S hS V).map (s • 𝟙 _)

/-- A functor out of a linear category carries the multiplication by a product to the composite
of the multiplications. -/
theorem _root_.CategoryTheory.Functor.map_mul_smul_id {R : Type*} [CommRing R] {C E : Type*}
    [Category C] [Category E] [Preadditive C] [Linear R C] (F : C ⥤ E) (X : C) (s t : R) :
    F.map ((s * t) • 𝟙 X) = F.map (s • 𝟙 X) ≫ F.map (t • 𝟙 X) := by
  rw [← Functor.map_comp, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
    mul_comm]

/-- Multiplication by a product is the composite of the multiplications. -/
theorem representedAffineUnitSmul_mul (p : ℤ) (s t : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    representedAffineUnitSmul B S hS V p (s * t) =
      representedAffineUnitSmul B S hS V p s ≫ representedAffineUnitSmul B S hS V p t :=
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  (representedAffineDerivedAssociated B S hS V).map_mul_smul_id _ s t

/-- **Every endomorphism of `Φ(R[p])` is multiplication by a unique global function.** -/
theorem bijective_representedAffineUnitSmul (p : ℤ) :
    Function.Bijective (representedAffineUnitSmul B S hS V p) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  have h₁ := (representedAffineDerivedAssociatedFullyFaithful B S hS V).map_bijective
    ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      p).obj (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      p).obj (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
  have h₂ := (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      p)).map_bijective
    (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  have key : ∀ s : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤),
      (DerivedCategory.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
        p).map (s • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) = s • 𝟙 _ := fun s => by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  have h₃ : (fun s : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) =>
      (representedAffineDerivedAssociated B S hS V).map (s • 𝟙
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V,
          ⊤)) p).obj (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))) =
      (representedAffineDerivedAssociated B S hS V).map ∘
        (DerivedCategory.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V,
          ⊤)) p).map ∘ (fun s : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) =>
            s • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
              Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) := by
    funext s
    simp only [Function.comp_apply, key]
  have h₄ := h₁.comp (h₂.comp (ModuleCat.bijective_smul_id _))
  rw [← h₃] at h₄
  exact h₄

/-- **The endomorphisms of `Φ(R[p])` commute**, being multiplications by the elements of the
commutative ring `R`. -/
theorem representedAffineUnitObj_end_comm (p : ℤ)
    (a b : representedAffineUnitObj B S hS V p ⟶ representedAffineUnitObj B S hS V p) :
    a ≫ b = b ≫ a := by
  obtain ⟨s, rfl⟩ := (bijective_representedAffineUnitSmul B S hS V p).2 a
  obtain ⟨t, rfl⟩ := (bijective_representedAffineUnitSmul B S hS V p).2 b
  rw [← representedAffineUnitSmul_mul, ← representedAffineUnitSmul_mul, mul_comm]

/-- **There are no nonzero morphisms between the structure sheaf in two distinct degrees.** -/
theorem subsingleton_hom_representedAffineUnitObj {p q : ℤ} (hpq : p ≠ q) :
    Subsingleton (representedAffineUnitObj B S hS V p ⟶ representedAffineUnitObj B S hS V q) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  have hZ : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) p).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
        q).obj (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) := by
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact DerivedCategory.isZero_of_isGE _ q p hlt
    · exact DerivedCategory.isZero_of_isLE _ q p hgt
  have : Projective (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :=
    ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} _)
  have hsub : Subsingleton ((DerivedCategory.singleFunctor
      (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) p).obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ⟶ (DerivedCategory.singleFunctor
      (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) q).obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) :=
    ((DerivedCategory.homologyFromSingleAddEquiv _ _ p).toEquiv.subsingleton_congr).2
      ⟨fun _ _ => hZ.eq_of_tgt _ _⟩
  exact (Equiv.ofBijective _ ((representedAffineDerivedAssociatedFullyFaithful B S hS
    V).map_bijective _ _)).symm.subsingleton

end Unit

section Pullback

variable {V' V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] (g : V' ⟶ V)

/-- **Derived extension of scalars of the ring in degree `p`** is the ring in degree `p`. -/
def representedAffineExtensionUnitIso (p : ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))
    (representedAffineDerivedExtension B S hS g).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
          p).obj (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))
          p).obj (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))
  have : Projective (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :=
    ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} _)
  CochainComplex.DerivedExtensionScalars.singleExtendIso
      (representedAffineCommRingCatHom B S hS g).hom
      (representedAffineDerivedExtension B S hS g).functor
      (representedAffineDerivedExtension B S hS g).comparison p _
      ((representedAffineDerivedExtension B S hS g).comparison_isIso_of_projective _ p) ≪≫
    (DerivedCategory.singleFunctor _ p).mapIso
      (ModuleCat.extendScalarsSelfIso (representedAffineCommRingCatHom B S hS g).hom)

/-- **The derived pullback of the structure sheaf in degree `p`** along a morphism of affine
representables is the structure sheaf in degree `p`: `Lg^*Φ(R[p]) ≅ Φ(R'[p])`, by affine base
change. -/
def representedAffineUnitPullbackIso (p : ℤ) :
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
        (representedAffineUnitObj B S hS V p) ≅ representedAffineUnitObj B S hS V' p :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))
  (representedAffineDerivedBaseChangeIso B S hS g).app _ ≪≫
    (representedAffineDerivedAssociated B S hS V').mapIso
      (representedAffineExtensionUnitIso B S hS g p)

/-- **Derived pullback of a multiplication is the multiplication by the image** under the map of
rings of global functions, read through `AlgebraicGeometry.Space.representedAffineUnitPullbackIso`.
-/
theorem representedAffineUnitPullbackIso_conj (p : ℤ)
    (s : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (representedAffineUnitPullbackIso B S hS g p).inv ≫
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
          (representedAffineUnitSmul B S hS V p s) ≫
        (representedAffineUnitPullbackIso B S hS g p).hom =
      representedAffineUnitSmul B S hS V' p ((representedAffineCommRingCatHom B S hS g).hom s) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))
  have hxy : (representedAffineExtensionUnitIso B S hS g p).inv ≫
      (representedAffineDerivedExtension B S hS g).functor.map (s • 𝟙 _) ≫
        (representedAffineExtensionUnitIso B S hS g p).hom =
      (representedAffineCommRingCatHom B S hS g).hom s • 𝟙 _ := by
    rw [RingTheory.TorIndependence.derivedExtension_scalar
      (representedAffineCommRingCatHom B S hS g).hom s
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V,
        ⊤)) p).obj (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))]
    exact Iso.inv_comp_smul_id_comp_hom _ _
  exact Iso.app_trans_mapIso_conj (representedAffineDerivedBaseChangeIso B S hS g)
    (representedAffineExtensionUnitIso B S hS g p) (s • 𝟙 _) _ hxy

end Pullback

end AlgebraicGeometry.Space

end
