module

public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsExists

/-!
# The derived tensor product with a fixed sheaf of modules is a left derived functor

Let `O` be a sheaf of commutative rings on a site and let `M` be a sheaf of `O`-modules. This
file constructs `- ⊗_O^L M` on the unbounded derived category of `O`-modules as the *total left
derived functor* of the degreewise tensor product `- ⊗_O M`, and records the comparison
exhibiting it as such, together with its absoluteness.

The construction is Stacks 0794 at the class of flat sheaves of modules, exactly as for derived
base change in
`StacksFrontier/Deformation/ToposThickening/DerivedExtensionOfScalarsExists.lean`: the only
hypothesis of 0794 with content is that `- ⊗_O M` carries a bounded above acyclic complex of
flat sheaves of modules to an acyclic complex, and that is read off the cycles sequences, whose
third terms are flat, by Stacks 03EX.

## Main definitions

* `Deformation.ComplexLift.tensorRight`: the degreewise tensor product `- ⊗_O M`.
* `Deformation.ComplexLift.derivedTensorRight`: the derived tensor product `- ⊗_O^L M`, with
  `Deformation.ComplexLift.derivedTensorRightCounit` exhibiting it as the left derived functor
  of `- ⊗_O M`.

## Main results

* `Deformation.ComplexLift.shortExact_map_tensorRight`: **Stacks 03EX for a fixed tensor
  factor on the right**, with the module universe independent of the two site universes.
* `Deformation.ComplexLift.acyclic_map_tensorRight`: `- ⊗_O M` carries a bounded above acyclic
  complex of flat sheaves of modules to an acyclic complex — the hypothesis `hFP` of
  Stacks 0794.
* `Deformation.ComplexLift.isLeftDerivedFunctor_derivedTensorRightCounit`: the comparison
  exhibits `- ⊗_O^L M` as the left derived functor of `- ⊗_O M` along the localization of
  cochain complexes at the quasi-isomorphisms.
* `Deformation.ComplexLift.isLeftDerivedFunctor_comp_derivedTensorRight`: that left derived
  functor is absolute.

## Implementation notes

**Why this is stated here and not through `Stacks.SheafOfModules.DerivedTensorProduct`.** The
derived tensor bifunctor of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/Interface.lean` is characterized by
its K-flat comparisons; nothing in that structure exhibits either of its partial functors as a
left derived functor, which is what `CategoryTheory.Functor.leftDerivedUnique` and
`CategoryTheory.LeftDerivedByResolutions.exists_leftDerivedIso_of_resolutions` consume. The
functor built here is derived by *flat* resolutions rather than K-flat ones, which is what makes
Stacks 0794 apply and what makes the comparison with derived base change — also derived by flat
resolutions — a formal consequence of uniqueness of left derived functors rather than a
comparison of two resolution calculi.

**The universes.** The module universe `u` is independent of the site universes `u'` and `v'`,
and the hom universe `d` of the derived category is independent of all three, as in
`Deformation.ComplexLift.DerivedExtensionOfScalars`. Keeping that generality is why the
instances for `- ⊗_O M` are assembled by hand from
`Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj`, whose three universes are free,
rather than taken from `Stacks.Sheaves.ChangeOfRings`, where the sections universe is tied to
the universe of objects of the site, or from
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean`, where it is `max u' v'`.

## References

* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe d v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-! ### The degreewise tensor product with a fixed sheaf of modules -/

/-- Tensoring with a fixed sheaf of `O`-modules `M`, with `M` in the right-hand slot: the
functor `- ⊗_O M` of `Mod(O)`, as given by the tensor bifunctor of Tag 06YM. -/
abbrev tensorRight (O : Sheaf J CommRingCat.{u})
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤ SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).flip.obj M

variable (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- `- ⊗_O M` preserves all colimits, by Tag 05NB and the symmetry of the tensor product. -/
theorem preservesColimits_tensorRight :
    PreservesColimitsOfSize.{u, u} (tensorRight O M) :=
  Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj.{u', v', u} O M

/-- `- ⊗_O M` is right exact. -/
instance preservesFiniteColimits_tensorRight : PreservesFiniteColimits (tensorRight O M) :=
  have := preservesColimits_tensorRight M
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- `- ⊗_O M` preserves sequential colimits, which is the hypothesis of Stacks 0794 that the
functor commute with the colimits along `ℕ` used to assemble the resolutions. -/
instance preservesColimitsOfShapeNat_tensorRight :
    PreservesColimitsOfShape ℕ (tensorRight O M) :=
  have := preservesColimits_tensorRight M
  have : PreservesColimitsOfSize.{0, 0} (tensorRight O M) := preservesColimitsOfSize_shrink _
  inferInstance

/-- `- ⊗_O M` preserves zero morphisms, being right exact. This is what `ShortComplex.map` and
`CategoryTheory.Functor.mapHomologicalComplex` ask for in their statements. -/
instance preservesZeroMorphisms_tensorRight : (tensorRight O M).PreservesZeroMorphisms :=
  inferInstance

/-- `- ⊗_O M` is additive: it is right exact, hence preserves binary biproducts. -/
instance additive_tensorRight : (tensorRight O M).Additive :=
  have : PreservesBinaryBiproducts (tensorRight O M) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-! ### Stacks 03EX for a fixed tensor factor on the right -/

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Stacks 03EX for a fixed tensor factor on the right**, with the module universe independent
of the two site universes: tensoring a short exact sequence whose third term is flat with a
fixed sheaf of modules leaves it short exact.

This is `Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj`, read at the
spelling `Deformation.ComplexLift.ringSheafOf` of the underlying sheaf of rings that the lift
statements of Tags 0DIY and 0DIZ are written with. The two spellings differ only in the proof of
the sheaf condition they carry, so they are the same sheaf of rings; instance search does not
see that, which is why the flat machinery is invoked with its arguments explicit. -/
theorem shortExact_map_tensorRight
    (S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
      (hS : S.ShortExact)
    (hflat : flatObjects O S.X₃) :
    (S.map (tensorRight O M)).ShortExact := by
  let S' : ShortComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', u} O)) := S
  have hS' : S'.ShortExact := hS
  have hflat' : AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', u, u} (O := O) S'.X₃ := hflat
  exact Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj.{v', u', u} O S' hS'
    hflat' M

/-! ### The hypothesis of Stacks 0794 -/

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **`- ⊗_O M` carries a bounded above acyclic complex of flat sheaves of modules to an acyclic
complex**: the hypothesis `hFP` of Stacks 0794.

The cycles sequences of the complex are short exact with flat third term
(`Deformation.ComplexLift.flatObjects_cycles_of_acyclic`), so Stacks 03EX keeps each of them
short exact after tensoring with `M`, and a complex whose cycles sequences stay short exact has
acyclic image. Neither exactness of `- ⊗_O M` nor flatness of `M` is used. -/
theorem acyclic_map_tensorRight (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (hLE : L.IsStrictlyLE a)
    (hflat : ∀ n : ℤ, flatObjects O (L.X n)) (hac : L.Acyclic) :
    (((tensorRight O M).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic :=
  CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact (tensorRight O M) L
    fun _ j hij ↦ shortExact_map_tensorRight M _
      (HomologicalComplex.cyclesShortComplex_shortExact L hij (hac j))
      (flatObjects_cycles_of_acyclic a L hLE hflat hac j)

/-! ### The derived tensor product with a fixed sheaf of modules -/

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]

/-- `- ⊗_O M` read on the homotopy category, followed by the localization to the derived
category: the functor whose left derived functor Stacks 0794 produces. -/
abbrev tensorRightHomotopy :
    HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  (tensorRight O M).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **Stacks 0794 applies to `- ⊗_O M`**: its left derived functor along
`Qh : K(Mod(O)) ⥤ D(Mod(O))` is defined at every object. -/
instance hasPointwiseLeftDerivedFunctor_tensorRight :
    (tensorRightHomotopy.{d} M).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) := by
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O)
  exact CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex
    (tensorRight O M) (flatObjects O) (flatObjects_biprod O) (flatObjects_cover O)
    (acyclic_map_tensorRight M)

/-- **The derived tensor product `- ⊗_O^L M`**: the total left derived functor of the degreewise
tensor product with `M`, which exists by Stacks 0794. -/
def derivedTensorRight :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  (tensorRightHomotopy M).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))

/-- Its counit, on the homotopy category. -/
def derivedTensorRightCounitHomotopy :
    DerivedCategory.Qh ⋙ derivedTensorRight.{d} M ⟶ tensorRightHomotopy M :=
  (tensorRightHomotopy M).totalLeftDerivedCounit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))

/-- The counit `Deformation.ComplexLift.derivedTensorRightCounitHomotopy` exhibits `- ⊗_O^L M`
as the left derived functor of `- ⊗_O M` along `Qh : K(Mod(O)) ⥤ D(Mod(O))`. -/
instance isLeftDerivedFunctor_derivedTensorRightCounitHomotopy :
    (derivedTensorRight.{d} M).IsLeftDerivedFunctor
      (derivedTensorRightCounitHomotopy M)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) := by
  dsimp only [derivedTensorRight, derivedTensorRightCounitHomotopy]
  infer_instance

/-- `- ⊗_O M` read on the homotopy category, precomposed with the homotopy quotient, is the
degreewise tensor product followed by the localization. -/
def quotientCompTensorRightIso :
    HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ) ⋙
        tensorRightHomotopy.{d} M ≅
      (tensorRight O M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight
      ((tensorRight O M).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm
      DerivedCategory.Qh ≪≫
    Functor.associator ((tensorRight O M).mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft
      ((tensorRight O M).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))

/-- **The comparison of `- ⊗_O^L M` with the degreewise tensor product**: the counit of
`Deformation.ComplexLift.derivedTensorRight`, read on complexes. -/
def derivedTensorRightCounit :
    DerivedCategory.Q ⋙ derivedTensorRight.{d} M ⟶
      (tensorRight O M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv (derivedTensorRight
          M) ≫
    Functor.whiskerLeft
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) (derivedTensorRightCounitHomotopy M) ≫
      (quotientCompTensorRightIso M).hom

/-- **The comparison exhibits `- ⊗_O^L M` as a left derived functor** along the localization of
cochain complexes at the quasi-isomorphisms: precomposition with the homotopy quotient is fully
faithful on functor categories, so the universal property along `Qh` is the universal property
along `Q`. -/
instance isLeftDerivedFunctor_derivedTensorRightCounit :
    (derivedTensorRight.{d} M).IsLeftDerivedFunctor
      (derivedTensorRightCounit M)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) :=
  StacksDraft.TorAmplitude.isLeftDerivedFunctor_of_homotopyCategory _
    (tensorRightHomotopy M) (quotientCompTensorRightIso M)
    (derivedTensorRight M) (derivedTensorRightCounitHomotopy M)
    (derivedTensorRightCounit M) (by
      ext X
      dsimp only [derivedTensorRightCounit, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app]
      rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      simp)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The derived tensor product with a fixed sheaf of modules is absolute**: for *every*
functor `G` out of `D(O)` the composite `(- ⊗_O^L M) ⋙ G` is the left derived functor of
`K ↦ G(K ⊗_O M)`, with the whiskered comparison.

This is the hypothesis `CategoryTheory.Adjunction.derived` — Stacks 09T5 — imposes on the left
derived functor of a derived adjunction, and it is what makes an identification of
`- ⊗_O^L M` with a composite of derived functors a consequence of uniqueness of left derived
functors. It holds because the functor is derived by resolutions: the flat objects resolve every
sheaf of modules and `- ⊗_O M` inverts the quasi-isomorphisms between the `P`-cellular
complexes. -/
theorem isLeftDerivedFunctor_comp_derivedTensorRight {E : Type*} [Category E]
    (G : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤ E) :
    (derivedTensorRight.{d} M ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedTensorRight.{d} M) G).inv ≫
        Functor.whiskerRight (derivedTensorRightCounitHomotopy M) G)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) := by
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O)
  exact CategoryTheory.Functor.isLeftDerivedFunctor_comp_of_acyclic_mapHomologicalComplex
    (tensorRight O M) (flatObjects O) (flatObjects_biprod O) (flatObjects_cover O)
    (acyclic_map_tensorRight M) DerivedCategory.Qh (derivedTensorRight M)
    (derivedTensorRightCounitHomotopy M) G

end Deformation.ComplexLift

end

end
