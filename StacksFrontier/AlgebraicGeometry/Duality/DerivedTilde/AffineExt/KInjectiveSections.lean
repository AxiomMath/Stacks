module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.TildeSliceHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.AlgebraicGeometry.ModuleSpecGammaAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsIsoOpenNaturalityDerived

/-!
# K-injective complexes and their sections

The degree-`n` cohomology of the Hom complex from `A` into a K-injective complex `J` is the group
of morphisms `A ⟶ J[n]` in the derived category. Sections over an open of `Spec R` carry
K-injective complexes of `𝒪_{Spec R}`-modules to K-injective complexes of `R`-modules, being right
adjoint to an exact functor, and a fully faithful exact functor reflects K-injectivity.

## Main results

* `CochainComplex.HomComplex.homologyAddEquivShiftedHom`: for `J` K-injective, the degree-`n`
  cohomology of the Hom complex from `A` to `J` is the group `Q(A) ⟶ Q(J)[n]`.
* `CochainComplex.isKInjective_of_fullyFaithful`: a fully faithful additive functor preserving
  acyclicity reflects K-injectivity.
* `AlgebraicGeometry.TildeSlice.isKInjective_sectionsR`: sections over an open `U` of `Spec R`
  carry K-injective complexes to K-injective complexes of `R`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace CochainComplex.HomComplex

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- A cohomology class of the Hom complex into a K-injective complex, read as a morphism in the
derived category. -/
def cohomologyClassAddEquivShiftedHom (A J : CochainComplex C ℤ) [J.IsKInjective] (n : ℤ) :
    CohomologyClass A J n ≃+ (DerivedCategory.Q.obj A ⟶ (DerivedCategory.Q.obj J)⟦n⟧) :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun x => (DerivedCategory.quotientCompQhIso C).inv.app A ≫
        DerivedCategory.Qh.map (CohomologyClass.homAddEquiv x) ≫
          (DerivedCategory.quotientCompQhIso C).hom.app (J⟦n⟧) ≫
            (DerivedCategory.Q.commShiftIso n).hom.app J) (fun x y => by simp))
    (((Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app A)
        ((DerivedCategory.quotientCompQhIso C).app (J⟦n⟧) ≪≫
          (DerivedCategory.Q.commShiftIso n).app J)).bijective.comp
      (CochainComplex.IsKInjective.Qh_map_bijective _ (J⟦n⟧))).comp
      CohomologyClass.homAddEquiv.bijective)

/-- The morphism attached to a cohomology class `x` is `Qh` applied to the homotopy class of `x`,
conjugated by the comparison isomorphisms `quotientCompQhIso` and `commShiftIso`. -/
lemma cohomologyClassAddEquivShiftedHom_apply (A J : CochainComplex C ℤ) [J.IsKInjective] (n : ℤ)
    (x : CohomologyClass A J n) :
    cohomologyClassAddEquivShiftedHom A J n x =
      (DerivedCategory.quotientCompQhIso C).inv.app A ≫
        DerivedCategory.Qh.map (CohomologyClass.homAddEquiv x) ≫
          (DerivedCategory.quotientCompQhIso C).hom.app (J⟦n⟧) ≫
            (DerivedCategory.Q.commShiftIso n).hom.app J :=
  rfl

/-- The derived morphism attached to the class of a cocycle is the image of the corresponding
morphism of complexes. -/
lemma cohomologyClassAddEquivShiftedHom_mk (A J : CochainComplex C ℤ) [J.IsKInjective] (n : ℤ)
    (z : Cocycle A J n) :
    cohomologyClassAddEquivShiftedHom A J n (CohomologyClass.mk z) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app J := by
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality (Cocycle.equivHomShift.symm z)
  dsimp only [Functor.comp_obj, Functor.comp_map] at h
  rw [cohomologyClassAddEquivShiftedHom_apply, CohomologyClass.homAddEquiv_apply,
    CohomologyClass.toHom_mk, reassoc_of% h, Iso.inv_hom_id_app_assoc]

/-- A cycle of the Hom complex is a cocycle. -/
def cycleCocycle (A J : CochainComplex C ℤ) (n : ℤ) (c : ((HomComplex A J).cycles n : Type _)) :
    Cocycle A J n :=
  (leftHomologyData A J n).cyclesIso.hom c

omit [HasDerivedCategory C] in
/-- The cochain underlying `cycleCocycle A J n c` is the image of `c` in the Hom complex. -/
lemma cycleCocycle_coe (A J : CochainComplex C ℤ) (n : ℤ)
    (c : ((HomComplex A J).cycles n : Type _)) :
    (cycleCocycle A J n c : Cochain A J n) = (HomComplex A J).iCycles n c :=
  ConcreteCategory.congr_hom ((leftHomologyData A J n).cyclesIso_hom_comp_i) c

/-- **Cohomology of the Hom complex into a K-injective complex.** For `J` K-injective, the
degree-`n` cohomology of the Hom complex from `A` to `J` is the group of morphisms
`A ⟶ J[n]` in the derived category. -/
def homologyAddEquivShiftedHom (A J : CochainComplex C ℤ) [J.IsKInjective] (n : ℤ) :
    ((HomComplex A J).homology n : Type _) ≃+
      (DerivedCategory.Q.obj A ⟶ (DerivedCategory.Q.obj J)⟦n⟧) :=
  (homologyAddEquiv A J n).trans (cohomologyClassAddEquivShiftedHom A J n)

end CochainComplex.HomComplex

namespace CochainComplex

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]

/-- **K-injectivity is reflected by a fully faithful functor preserving acyclicity.** If `Φ` is
additive, fully faithful and carries acyclic complexes to acyclic complexes, and `Φ(J)` is
K-injective, then `J` is K-injective. -/
theorem isKInjective_of_fullyFaithful (Φ : C ⥤ D) [Φ.Additive] [Φ.Full] [Φ.Faithful]
    (hΦ : ∀ K : CochainComplex C ℤ, K.Acyclic →
      HomologicalComplex.Acyclic ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (J : CochainComplex C ℤ)
    (hJ : CochainComplex.IsKInjective ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :
    J.IsKInjective := by
  refine ⟨fun {K} f hK => ?_⟩
  obtain ⟨h⟩ := hJ.nonempty_homotopy_zero ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
    (hΦ K hK)
  obtain ⟨z, hz⟩ := HomComplex.Cochain.equivHomotopy _ _ h
  let z' : HomComplex.Cochain K J (-1) := HomComplex.Cochain.mk fun p q hpq => Φ.preimage (z.v p q
      hpq)
  have hz' : z'.map Φ = z := by
    ext p q hpq
    exact Φ.map_preimage (z.v p q hpq)
  refine ⟨(HomComplex.Cochain.equivHomotopy f 0).symm ⟨z', ?_⟩⟩
  have hinj : Function.Injective (fun w : HomComplex.Cochain K J 0 => w.map Φ) := by
    intro w w' hw
    refine HomComplex.Cochain.ext _ _ fun p q hpq => ?_
    exact Φ.map_injective (by simpa using HomComplex.Cochain.congr_v hw p q hpq)
  apply hinj
  simp only [HomComplex.Cochain.map_add, HomComplex.Cochain.map_ofHom, ← HomComplex.δ_map, hz']
  simpa using hz

end CochainComplex

namespace AlgebraicGeometry.TildeSlice

variable {R : CommRingCat.{u}} (U : (Spec R).Opens)

/-- If `u'` is an additive right adjoint of an exact additive functor `v`, then `u'` carries a
K-injective complex `I` to a K-injective complex. -/
theorem isKInjective_mapHomologicalComplex_of_exact' {A B : Type*} [Category A] [Abelian A]
    [Category B] [Abelian B] (u' : A ⥤ B) (v : B ⥤ A) [u'.Additive] [v.Additive] (adj : v ⊣ u')
    [PreservesFiniteLimits v] [PreservesFiniteColimits v] (I : CochainComplex A ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective ((u'.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact u' v adj I

/-- Sections over `U` through the slice adjunction form an additive functor. -/
instance sliceSections_additive : (sliceSections U).Additive where
  map_add := by intros; rfl

/-- Sections over `U`, as `R`-modules, carry K-injective complexes to K-injective complexes. -/
theorem isKInjective_sectionsR (I : CochainComplex (Spec R).Modules ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective (((sectionsR U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        := by
  let F₁ := SheafOfModules.overFunctor (Spec R).ringCatSheaf U
  let F₂ := SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver (R := (Spec
      R).ringCatSheaf) U)
  have : F₂.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits F₁ :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U
  have : PreservesFiniteColimits F₁ :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U
  have := AlgebraicGeometry.tilde.preservesFiniteLimits R
  have := Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor R
  have h₁ : CochainComplex.IsKInjective ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    @Stacks.Cohomology.Localization.isKInjective_over _ _ (Opens.grothendieckTopology (Spec R))
      (Spec R).ringCatSheaf U I hI
  have h₂ := isKInjective_mapHomologicalComplex_of_exact' F₂ F₁
      (SheafOfModules.overPushforwardOverAdj U) _ h₁
  have h₃ := isKInjective_mapHomologicalComplex_of_exact' moduleSpecΓFunctor
      (tilde.functor R) tilde.adjunction _ h₂
  exact (CochainComplex.isKInjective_iff_of_iso
    ((NatIso.mapHomologicalComplex (sliceSectionsIso U) (ComplexShape.up ℤ)).app I)).1 h₃

end AlgebraicGeometry.TildeSlice

end
