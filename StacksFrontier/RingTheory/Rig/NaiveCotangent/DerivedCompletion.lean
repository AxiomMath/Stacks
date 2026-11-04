module

public import Mathlib.Algebra.Homology.Double
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.TensorComplex.TensorUnitIso

/-!
# Derived base change of complexes concentrated in two adjacent degrees

A complex concentrated in two adjacent degrees `i₀`, `i₁` of a complex shape is
`HomologicalComplex.double d hrel`, and Mathlib describes its terms and differentials and maps
out of it, but not maps *into* it from another such complex. This file supplies that: a
commuting square induces a morphism of two-term complexes, functorially, an isomorphism of
squares induces a homotopy of morphisms. Isomorphisms of such complexes are
`Rig.doubleIsoDouble`, and their compatibility with an additive functor is
`HomologicalComplex.doubleMapFunctorIso`.

It then identifies the derived tensor product along a flat ring map `f : R → S` with ordinary
extension of scalars. Tensoring complexes of `S`-modules with the unit complex — `S` placed in
degree `0` — is the identity functor, so the functor underlying the derived tensor product
`- ⊗^L_R S` is `- ⊗_R S`; flatness makes the latter exact, hence a functor inverting
quasi-isomorphisms, and the counit of a left derived functor of a functor inverting the
localizing maps is invertible.

## Main definitions

* `Rig.mkDoubleHom` — the morphism of complexes concentrated in two adjacent degrees induced
  by a commuting square.
* `Rig.tensorRightLargeUnitIso` — tensoring complexes with the unit complex is the identity
  functor, for modules in a universe above the ring's.
* `Rig.flatDerivedTensorIso` — **along a flat ring map the derived tensor product with the unit
  complex is ordinary extension of scalars.**

## Main results

* `Rig.mkDoubleHom_id` and `Rig.mkDoubleHom_comp` — the construction of a morphism from a
  commuting square is functorial.
* `Rig.nonempty_mkDoubleHomotopy` — a homotopy between two morphisms of two-term complexes,
  built from a homotopy of the underlying squares.

## References

* [Stacks Project, Lemma 88.3.2 (Tag 0GAF)](https://stacks.math.columbia.edu/tag/0GAF)
* [Stacks Project, Lemma 10.97.2 (Tag 00MB)](https://stacks.math.columbia.edu/tag/00MB)
* [Stacks Project, Lemma 15.57.3 (Tag 06Y6)](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped TensorProduct

universe u v w

namespace Rig

/-! ## Complexes concentrated in two adjacent degrees -/

section Double

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι} {X₀ X₁ Y₀ Y₁ : C} {d : X₀ ⟶ X₁} {d' : Y₀ ⟶ Y₁}

/-- The morphism of complexes concentrated in degrees `i₀` and `i₁` determined by a commuting
square `a ≫ d' = d ≫ b`. -/
public def mkDoubleHom (hrel : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
    (a : X₀ ⟶ Y₀) (b : X₁ ⟶ Y₁) (hab : a ≫ d' = d ≫ b) :
    HomologicalComplex.double d hrel ⟶ HomologicalComplex.double d' hrel :=
  HomologicalComplex.mkHomFromDouble hrel hne
    (a ≫ (HomologicalComplex.doubleXIso₀ d' hrel).inv)
    (b ≫ (HomologicalComplex.doubleXIso₁ d' hrel hne).inv)
    (by
      rw [HomologicalComplex.double_d d' hrel hne]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hab, Category.assoc])
    (fun k _ => by
      rw [HomologicalComplex.double_d_eq_zero₀ d' hrel i₁ k hne.symm, comp_zero])

/-- In degree `i₀`, `mkDoubleHom` is `a`, conjugated by the identifications `doubleXIso₀` of the
degree-`i₀` objects. -/
@[simp] public theorem mkDoubleHom_f₀ (hrel : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
    (a : X₀ ⟶ Y₀) (b : X₁ ⟶ Y₁) (hab : a ≫ d' = d ≫ b) :
    (mkDoubleHom hrel hne a b hab).f i₀ =
      (HomologicalComplex.doubleXIso₀ d hrel).hom ≫ a ≫
        (HomologicalComplex.doubleXIso₀ d' hrel).inv := by
  rw [mkDoubleHom, HomologicalComplex.mkHomFromDouble_f₀]

/-- In degree `i₁`, `mkDoubleHom` is `b`, conjugated by the identifications `doubleXIso₁` of the
degree-`i₁` objects. -/
@[simp] public theorem mkDoubleHom_f₁ (hrel : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
    (a : X₀ ⟶ Y₀) (b : X₁ ⟶ Y₁) (hab : a ≫ d' = d ≫ b) :
    (mkDoubleHom hrel hne a b hab).f i₁ =
      (HomologicalComplex.doubleXIso₁ d hrel hne).hom ≫ b ≫
        (HomologicalComplex.doubleXIso₁ d' hrel hne).inv := by
  rw [mkDoubleHom, HomologicalComplex.mkHomFromDouble_f₁]

/-- The square of identities induces the identity morphism. -/
public theorem mkDoubleHom_id (hrel : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) (d : X₀ ⟶ X₁)
    (hab : (𝟙 X₀) ≫ d = d ≫ (𝟙 X₁)) :
    mkDoubleHom hrel hne (𝟙 X₀) (𝟙 X₁) hab = 𝟙 (HomologicalComplex.double d hrel) := by
  refine HomologicalComplex.from_double_hom_ext (i₀ := i₀) (i₁ := i₁) ?_ ?_ <;>
    simp [HomologicalComplex.id_f]

/-- Horizontal composition of squares induces composition of morphisms. -/
public theorem mkDoubleHom_comp (hrel : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) {Z₀ Z₁ : C}
    {d'' : Z₀ ⟶ Z₁} (a : X₀ ⟶ Y₀) (b : X₁ ⟶ Y₁) (hab : a ≫ d' = d ≫ b)
    (a' : Y₀ ⟶ Z₀) (b' : Y₁ ⟶ Z₁) (hab' : a' ≫ d'' = d' ≫ b')
    (habc : (a ≫ a') ≫ d'' = d ≫ (b ≫ b')) :
    mkDoubleHom hrel hne (a ≫ a') (b ≫ b') habc =
      mkDoubleHom hrel hne a b hab ≫ mkDoubleHom hrel hne a' b' hab' := by
  refine HomologicalComplex.from_double_hom_ext (i₀ := i₀) (i₁ := i₁) ?_ ?_ <;>
    simp [HomologicalComplex.comp_f]

/-- **Homotopic squares induce homotopic morphisms.** If `a - a' = d ≫ s` and
`b - b' = s ≫ d'` for some `s : X₁ ⟶ Y₀`, the two induced morphisms of complexes
concentrated in degrees `-1` and `0` are homotopic. -/
public theorem nonempty_mkDoubleHomotopy {X₀ X₁ Y₀ Y₁ : C} {d : X₀ ⟶ X₁} {d' : Y₀ ⟶ Y₁}
    (hrel : (ComplexShape.up ℤ).Rel (-1) 0) (hne : (-1 : ℤ) ≠ 0)
    {a a' : X₀ ⟶ Y₀} {b b' : X₁ ⟶ Y₁}
    (hab : a ≫ d' = d ≫ b) (hab' : a' ≫ d' = d ≫ b') (s : X₁ ⟶ Y₀)
    (hs₀ : a - a' = d ≫ s) (hs₁ : b - b' = s ≫ d') :
    Nonempty (Homotopy (mkDoubleHom hrel hne a b hab)
      (mkDoubleHom hrel hne a' b' hab')) := by
  refine ⟨
    { hom := fun i j =>
        if hi : i = 0 then
          if hj : j = -1 then
            eqToHom (by rw [hi]) ≫ (HomologicalComplex.doubleXIso₁ d hrel hne).hom ≫ s ≫
              (HomologicalComplex.doubleXIso₀ d' hrel).inv ≫ eqToHom (by rw [hj])
          else 0
        else 0
      zero := ?_
      comm := ?_ }⟩
  · intro i j hij
    split_ifs with hi hj
    · subst hi hj
      exact absurd hrel hij
    all_goals rfl
  · intro i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (sub_add_cancel i 1)]
    by_cases h : i = -1
    · subst h
      rw [show ((-1 : ℤ) + 1) = 0 by norm_num,
        show ((-1 : ℤ) - 1) = -2 by norm_num,
        dite_eq_left (rfl : (0 : ℤ) = 0), dite_eq_left (rfl : (-1 : ℤ) = -1),
        dite_eq_right hne, HomologicalComplex.double_d d hrel hne,
        mkDoubleHom_f₀, mkDoubleHom_f₀, eq_add_of_sub_eq hs₀]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc,
        Iso.inv_hom_id_assoc, Preadditive.add_comp, Preadditive.comp_add, zero_comp,
        add_zero]
    · by_cases h' : i = 0
      · subst h'
        rw [show ((0 : ℤ) + 1) = 1 by norm_num,
          show ((0 : ℤ) - 1) = -1 by norm_num,
          HomologicalComplex.double_d_eq_zero₀ d hrel 0 1 (Ne.symm hne), zero_comp,
          dite_eq_left (rfl : (0 : ℤ) = 0), dite_eq_left (rfl : (-1 : ℤ) = -1),
          HomologicalComplex.double_d d' hrel hne, mkDoubleHom_f₁, mkDoubleHom_f₁,
          eq_add_of_sub_eq hs₁]
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc,
          Iso.inv_hom_id_assoc, Preadditive.add_comp, Preadditive.comp_add, zero_add]
      · exact (HomologicalComplex.isZero_double_X d hrel i h h').eq_of_src _ _

end Double

/-! ## Derived tensor product along a flat ring map -/

section FlatDerivedTensor

/-- Tensoring complexes of `S`-modules with the complex `S` in degree `0` is the identity
functor, at a module universe above the ring's. -/
public def tensorRightLargeUnitIso (S : Type u) [CommRing S] :
    CochainComplex.tensorRightLarge.{u, w}
        ((CochainComplex.singleFunctor (ModuleCat.{max w u} S) 0).obj
          (ModuleCat.of S (ULift.{w} S))) ≅
      𝟭 (CochainComplex (ModuleCat.{max w u} S) ℤ) :=
  letI := ModuleCat.liftedModuleMonoidalStruct.{u, w} (R := S)
  letI := ModuleCat.liftedModuleMonoidal.{u, w} (R := S)
  letI := ModuleCat.liftedModuleMonoidalPreadditive.{u, w} (R := S)
  trightCochainTensorUnitIso (ModuleCat.{max w u} S)

/-- **Along a flat ring map the derived tensor product with the unit is ordinary extension of
scalars.** If `f : R → S` is flat, extension of scalars along `f` is exact, so it inverts
quasi-isomorphisms; the counit of the derived functor is therefore invertible at every
complex, and the derived tensor product `- ⊗^L_R S` is computed by `- ⊗_R S`. -/
public def flatDerivedTensorIso {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.Flat)
    [HasDerivedCategory.{v} (ModuleCat.{max w u} R)]
    [HasDerivedCategory.{v} (ModuleCat.{max w u} S)]
    {N : CochainComplex (ModuleCat.{max w u} S) ℤ}
    (T : CochainComplex.DerivedTensor.DerivedTensorChangeOfRings f N)
    (hN : CochainComplex.tensorRightLarge.{u, max w u} N ≅
      𝟭 (CochainComplex (ModuleCat.{max w u} S) ℤ))
    (K : CochainComplex (ModuleCat.{max w u} R) ℤ) :
    T.F.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge f).obj K) := by
  let e : CochainComplex.extendScalarsLarge.{w, u, u} f ⋙
      CochainComplex.tensorRightLarge.{u, max w u} N ≅
      CochainComplex.extendScalarsLarge.{w, u, u} f :=
    Functor.isoWhiskerLeft _ hN ≪≫ Functor.rightUnitor _
  have hInv : (HomologicalComplex.quasiIso (ModuleCat.{max w u} R)
      (ComplexShape.up ℤ)).IsInvertedBy
      ((CochainComplex.extendScalarsLarge.{w, u, u} f ⋙
        CochainComplex.tensorRightLarge.{u, max w u} N) ⋙ DerivedCategory.Q) := by
    intro X Y g hg
    have : QuasiIso g := hg
    have := extendScalars_preservesHomology_of_flat.{u, w} f hf
    have : QuasiIso ((CochainComplex.extendScalarsLarge.{w, u, u} f).map g) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology g
        (ModuleCat.extendScalars.{u, u, max w u} f)
    exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight e DerivedCategory.Q) g).mpr
      (by dsimp; infer_instance)
  have := Functor.isIso_of_isLeftDerivedFunctor_of_inverts T.F T.directCounit hInv
  exact asIso (T.directCounit.app K) ≪≫ DerivedCategory.Q.mapIso (e.app K)

end FlatDerivedTensor

end Rig

end
