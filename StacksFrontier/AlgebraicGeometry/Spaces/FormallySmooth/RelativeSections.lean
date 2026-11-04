module

public import StacksFrontier.AlgebraicGeometry.Descent.FppfSingletonSheafEqualizer
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SpecOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSections

/-!
# Sections of an algebraic space over a base, on spectra of algebras

Fix a ring `A'` with `Spec A' ⟶ S` in the big fppf site of `S`, an algebraic space `X` over `S`
and a morphism `p : X ⟶ h_{Spec A'}`. For an `A'`-algebra `R` whose spectrum lies in the site,
`AlgebraicGeometry.Space.RelSec p R` is the set of sections of `X` over `Spec R` lying over the
structure morphism `Spec R ⟶ Spec A'`, and a map of `A'`-algebras `R → R'` restricts such
sections from `Spec R` to `Spec R'`.

Two properties of algebraic spaces are recorded here in this ring-theoretic form.

* **Glueing along a thickening (Stacks 07SY).** For a cartesian square of `A'`-algebras
  `R = R₁ ×_{R₃} R₂` in which `R₂ → R₃` is surjective with square-zero kernel, sections over
  `R₁` and `R₂` with the same restriction to `R₃` glue uniquely to a section over `R`
  (`AlgebraicGeometry.Space.RelSec.existsUnique_glue`).
* **Étale descent.** For an étale, faithfully flat `R`-algebra `R'`, a section over `R'` whose
  two restrictions to `R' ⊗_R R'` agree comes from a unique section over `R`
  (`AlgebraicGeometry.Space.RelSec.existsUnique_descend`).

These are the two inputs of the proof, in
`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmooth/OfIsSmooth.lean`, that a smooth morphism
of algebraic spaces is formally smooth.

## Main definitions

* `AlgebraicGeometry.Space.RelSec`, `AlgebraicGeometry.Space.RelSec.map`.

## References

* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A' : Type u} [CommRing A'] {s₀ : Spec (.of A') ⟶ S} {hA' : B.Contains (Spec (.of A'))}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X ⟶ yoneda.obj (specOver B S hS s₀ A' hA'))

/-- The spectrum of `R` lies in the site; an instance argument, so that it is found rather than
passed. -/
abbrev InSite (B : BigFppfSite.{u}) (R : Type u) [CommRing R] : Prop :=
  Fact (B.Contains (Spec (.of R)))

/-- **The sections of `X` over `Spec R` lying over `Spec A'`.** -/
def RelSec (R : Type u) [CommRing R] [Algebra A' R] [hR : InSite B R] : Type u :=
  {s : X.obj (op (specOver B S hS s₀ R hR.out)) //
    p.app _ s = specOverHom B S hS s₀ hA' hR.out (Algebra.ofId A' R)}

namespace RelSec

variable {p}

variable {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] [Algebra A' R]
  [Algebra A' R'] [Algebra A' R''] [hR : InSite B R] [hR' : InSite B R'] [hR'' : InSite B R'']

/-- The morphism of spectra induced by a map of `A'`-algebras commutes with the structure
morphisms to `Spec A'`. -/
theorem specOverHom_comp_ofId (g : R →ₐ[A'] R') :
    specOverHom B S hS s₀ hR.out hR'.out g ≫ specOverHom B S hS s₀ hA' hR.out (Algebra.ofId A' R) =
      specOverHom B S hS s₀ hA' hR'.out (Algebra.ofId A' R') := by
  rw [specOverHom_comp]
  exact specOverHom_congr (algHom_self_ext _ _)

/-- **Restriction of sections along a map of algebras.** -/
def map (g : R →ₐ[A'] R') (s : RelSec p R) : RelSec p R' :=
  ⟨X.map (specOverHom B S hS s₀ hR.out hR'.out g).op s.1, by
    rw [NatTrans.naturality_apply, s.2]
    exact specOverHom_comp_ofId g⟩

/-- The underlying section of a restriction is the restriction of the underlying section. -/
theorem map_val (g : R →ₐ[A'] R') (s : RelSec p R) :
    (map g s).1 = X.map (specOverHom B S hS s₀ hR.out hR'.out g).op s.1 :=
  rfl

/-- Two sections over `Spec A'` are equal when their underlying sections of `X` are. -/
theorem ext {s t : RelSec p R} (h : s.1 = t.1) : s = t :=
  Subtype.ext h

/-- Restricting along two maps in turn is restricting along their composite. -/
theorem map_map (g : R →ₐ[A'] R') (g' : R' →ₐ[A'] R'') (s : RelSec p R) :
    map g' (map g s) = map (g'.comp g) s := by
  refine ext ?_
  simp only [map_val]
  rw [← Functor.map_comp_apply, ← op_comp, specOverHom_comp]

/-- Restricting along the identity does nothing. -/
theorem map_id (s : RelSec p R) : map (AlgHom.id A' R) s = s := by
  refine ext ?_
  simp only [map_val, specOverHom_id, op_id, Functor.map_id_apply]

/-- Equal maps of algebras restrict a section in the same way. -/
theorem map_congr {g g' : R →ₐ[A'] R'} (h : g = g') (s : RelSec p R) : map g s = map g' s := by
  subst h; rfl

/-! ### Glueing along a thickening -/

/-- A section over `Spec R` whose restriction along `g` is a section `s'` over `Spec R'` has
image in `h_{Spec A'}` restricting to the structure morphism of `R'`. -/
private theorem map_app_eq_ofId (g : R →ₐ[A'] R')
    (s : X.obj (op (specOver B S hS s₀ R hR.out))) (s' : RelSec p R')
    (hs : X.map (specOverHom B S hS s₀ hR.out hR'.out g).op s = s'.1) :
    (yoneda.obj (specOver B S hS s₀ A' hA')).map
        (specOverHom B S hS s₀ hR.out hR'.out g).op (p.app _ s) =
      specOverHom B S hS s₀ hA' hR'.out (Algebra.ofId A' R') := by
  rw [← NatTrans.naturality_apply, hs, s'.2]

/-- **Stacks 07SY for sections over spectra of algebras.** Let `R = R₁ ×_{R₃} R₂` be a
cartesian square of `A'`-algebras in which `R₂ → R₃` is surjective with square-zero kernel. Two
sections of `X` over `Spec R₁` and `Spec R₂` lying over `Spec A'` and agreeing over `Spec R₃` are
the restrictions of a unique section over `Spec R`. -/
theorem existsUnique_glue (hX : IsAlgebraicSpace B S hS X)
    {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    [Algebra A' R₁] [Algebra A' R₂] [Algebra A' R₃]
    [hR₁ : InSite B R₁] [hR₂ : InSite B R₂] [hR₃ : InSite B R₃]
    (g₁ : R₁ →ₐ[A'] R₃) (g₂ : R₂ →ₐ[A'] R₃) (h₁ : R →ₐ[A'] R₁) (h₂ : R →ₐ[A'] R₂)
    (hpb : IsPullback (CommRingCat.ofHom h₁.toRingHom) (CommRingCat.ofHom h₂.toRingHom)
      (CommRingCat.ofHom g₁.toRingHom) (CommRingCat.ofHom g₂.toRingHom))
    (hsurj : Function.Surjective g₂) (hsq : RingHom.ker g₂.toRingHom ^ 2 = ⊥)
    (s₁ : RelSec p R₁) (s₂ : RelSec p R₂) (h : map g₁ s₁ = map g₂ s₂) :
    ∃! s : RelSec p R, map h₁ s = s₁ ∧ map h₂ s = s₂ := by
  let i := specOverHom B S hS s₀ hR₂.out hR₃.out g₂
  let f := specOverHom B S hS s₀ hR₁.out hR₃.out g₁
  let a := specOverHom B S hS s₀ hR.out hR₂.out h₂
  let b := specOverHom B S hS s₀ hR.out hR₁.out h₁
  have hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) :=
    (Stacks.Smooth.isFirstOrderThickening_specMap (CommRingCat.ofHom g₂.toRingHom) hsurj
      hsq).isThickening
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f) := by
    show _root_.AlgebraicGeometry.IsAffineHom (Spec.map _)
    infer_instance
  have hpo : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b) :=
    Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective _ _ _ _ hpb hsurj
  obtain ⟨s, ⟨hs₂, hs₁⟩, huniq⟩ := existsUnique_section_of_isThickening_of_isAffineHom B S hS
    i f a b hi hpo X hX s₂.1 s₁.1 (congrArg Subtype.val h).symm
  -- the glued section lies over `Spec A'`
  have hY := isAlgebraicSpace_yoneda B S hS (specOver B S hS s₀ A' hA')
  have hlies : p.app _ s = specOverHom B S hS s₀ hA' hR.out (Algebra.ofId A' R) := by
    have hc : (yoneda.obj (specOver B S hS s₀ A' hA')).map i.op
        (specOverHom B S hS s₀ hA' hR₂.out (Algebra.ofId A' R₂)) =
        (yoneda.obj (specOver B S hS s₀ A' hA')).map f.op
          (specOverHom B S hS s₀ hA' hR₁.out (Algebra.ofId A' R₁)) := by
      show i ≫ _ = f ≫ _
      rw [specOverHom_comp_ofId, specOverHom_comp_ofId]
    exact (existsUnique_section_of_isThickening_of_isAffineHom B S hS i f a b hi hpo _ hY
      _ _ hc).unique ⟨map_app_eq_ofId h₂ s s₂ hs₂, map_app_eq_ofId h₁ s s₁ hs₁⟩
      ⟨specOverHom_comp_ofId h₂, specOverHom_comp_ofId h₁⟩
  refine ⟨⟨s, hlies⟩, ⟨ext hs₁, ext hs₂⟩, fun t ht => ext ?_⟩
  exact huniq t.1 ⟨congrArg Subtype.val ht.2, congrArg Subtype.val ht.1⟩

/-! ### Étale descent -/

/-- The cartesian square of spectra of a tensor square. -/
theorem isPullback_specOverHom_tensor [Algebra R R'] [IsScalarTower A' R R']
    [hRR : InSite B (R' ⊗[R] R')] :
    IsPullback
      (specOverHom B S hS s₀ hR'.out hRR.out (Algebra.TensorProduct.includeLeft (S := A')))
      (specOverHom B S hS s₀ hR'.out hRR.out
        ((Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').restrictScalars A'))
      (specOverHom B S hS s₀ hR.out hR'.out (IsScalarTower.toAlgHom A' R R'))
      (specOverHom B S hS s₀ hR.out hR'.out (IsScalarTower.toAlgHom A' R R')) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R R' R')
  have : ReflectsLimit (cospan (specOverHom B S hS s₀ hR.out hR'.out
      (IsScalarTower.toAlgHom A' R R')) (specOverHom B S hS s₀ hR.out hR'.out
      (IsScalarTower.toAlgHom A' R R'))) (BigFppfOver.toScheme B S hS) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) h

/-- **Étale descent of sections over spectra of algebras.** For an étale, faithfully flat
`R`-algebra `R'`, a section of `X` over `Spec R'` lying over `Spec A'` whose two restrictions to
`Spec (R' ⊗_R R')` agree is the restriction of a unique section over `Spec R`. -/
theorem existsUnique_descend (hX : IsAlgebraicSpace B S hS X) [Algebra R R']
    [IsScalarTower A' R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    [hRR : InSite B (R' ⊗[R] R')] (s' : RelSec p R')
    (h : map (Algebra.TensorProduct.includeLeft (S := A')) s' =
      (map ((Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').restrictScalars A') s' :
        RelSec p (R' ⊗[R] R'))) :
    ∃! s : RelSec p R, map (IsScalarTower.toAlgHom A' R R') s = s' := by
  have hsurj : Surjective ((BigFppfOver.toScheme B S hS).map
      (specOverHom B S hS s₀ hR.out hR'.out (IsScalarTower.toAlgHom A' R R'))) := by
    show Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R')))
    rw [surjective_iff]
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  have het : Etale ((BigFppfOver.toScheme B S hS).map
      (specOverHom B S hS s₀ hR.out hR'.out (IsScalarTower.toAlgHom A' R R'))) := by
    show Etale (Spec.map (CommRingCat.ofHom (algebraMap R R')))
    rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
    infer_instance
  have hbij := BigFppfOver.bijective_mapToEqualizer_of_isSheaf_of_etale B S hS X hX.isSheaf _ _ _
    (isPullback_specOverHom_tensor (R := R) (R' := R')) hsurj het
  obtain ⟨s, hs⟩ := hbij.2 ⟨s'.1, congrArg Subtype.val h⟩
  have hs' : X.map (specOverHom B S hS s₀ hR.out hR'.out
      (IsScalarTower.toAlgHom A' R R')).op s = s'.1 :=
    congrArg Subtype.val hs
  -- the descended section lies over `Spec A'`
  have hY := isAlgebraicSpace_yoneda B S hS (specOver B S hS s₀ A' hA')
  have hlies : p.app _ s = specOverHom B S hS s₀ hA' hR.out (Algebra.ofId A' R) := by
    have hbijY := BigFppfOver.bijective_mapToEqualizer_of_isSheaf_of_etale B S hS _ hY.isSheaf
      _ _ _ (isPullback_specOverHom_tensor (R := R) (R' := R')) hsurj het
    refine hbijY.1 (Subtype.ext ?_)
    show (yoneda.obj _).map _ (p.app _ s) = (yoneda.obj _).map _ _
    rw [map_app_eq_ofId _ s s' hs']
    exact (specOverHom_comp_ofId _).symm
  refine ⟨⟨s, hlies⟩, ext hs', fun t ht => ext ?_⟩
  refine hbij.1 (Subtype.ext ?_)
  show X.map _ t.1 = X.map _ s
  rw [hs']
  exact congrArg Subtype.val ht

end RelSec

end AlgebraicGeometry.Space

end
