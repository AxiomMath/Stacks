module

public import StacksFrontier.Algebra.Homology.Koszul.AlternatingCechTotal
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCechComputesSections
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingLiftedRestriction

/-!
# The Koszul Čech complex computes derived sections over a union of basic opens

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`,
let `X = Spec A` and let `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`.  The total alternating Čech complex of
the family `D(f₁), …, D(f_r)` of opens of `X`, with coefficients in the complex of associated
sheaves `M̃^•` of a complex `M^•` of `A`-modules — this is the complex that Tag 08D1 identifies
with `colimₑ Hom^•(I^•(f^e), M^•)` — is the total alternating Čech complex of the induced
covering of the open subscheme `U`, with coefficients in `M̃^•|_U`.  Since the terms of `M̃^•|_U`
are quasi-coherent, the abelian form of Tag 08D2 applies and identifies that complex with
`RΓ(U, M̃^•)` in `D(Ab)`.

## Main definitions

* `Koszul.DerivedSystem.restrictComplexFunctor` is restriction of complexes of `𝒪_X`-modules to
  the open subscheme `U`.
* `Koszul.DerivedSystem.alternatingCechTotalIsoOfUnion` is the identification of the two total
  alternating Čech complexes.
* `Koszul.DerivedSystem.alternatingCechTotalDerivedIsoOfUnion` is the resulting identification
  of the total alternating Čech complex of `M̃^•` with `RΓ(U, M̃^•|_U)` in `D(Ab)`.

## Main results

* `Koszul.DerivedSystem.imF_inter_unionCover`: the image in `X` of an intersection occurring in
  the Čech complex of the covering of `U` is the corresponding intersection of the `D(fᵢ)`.
* `Koszul.DerivedSystem.isQuasicoherent_restrictFunctor_obj`: the restriction to `U` of a
  quasi-coherent `𝒪_X`-module is quasi-coherent.

## Implementation notes

Restriction of modules to the open subscheme is written as `Scheme.Modules.restrictFunctor`,
whose quasi-coherence is an instance, rather than as the extension-by-zero adjoint
`ExtensionByZeroModules.jStar` of the derived theory; the two functors are equal, which is
`Koszul.DerivedSystem.restrictFunctorOfUnion_eq_jStar`, and the equality is what carries the
identification of sections used below.

Sections of the restriction of a module over an open `W` of `U` are by construction the
sections of the module over the image of `W` in `X`, so the comparison of the two Čech
complexes is the identity on cochains; it is only the indexing that moves, the covering of `U`
being indexed by a lift of `Fin r` to the universe of the ring, as the unbounded Čech theory of
Tag 08C1 requires.

## References

* [Stacks Project, Tag 08D1](https://stacks.math.columbia.edu/tag/08D1)
* [Stacks Project, Tag 08D2](https://stacks.math.columbia.edu/tag/08D2)
* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open ExtensionByZeroModules CechCochains

universe u

namespace Koszul.DerivedSystem

attribute [local instance] HasDerivedCategory.standard

variable {A : CommRingCat.{u}} {r : ℕ}

/-! ### Restriction to the open subscheme -/

/-- Restriction of modules to the open subscheme `U = D(f₁) ∪ ⋯ ∪ D(f_r)`. -/
public abbrev restrictFunctorOfUnion (f : Fin r → A) :
    (Spec A).Modules ⥤ (unionScheme f).Modules :=
  Scheme.Modules.restrictFunctor (unionOfBasicOpens f).ι

/-- **Restriction to `U` is the restriction functor of the extension-by-zero adjunction.** -/
public theorem restrictFunctorOfUnion_eq_jStar (f : Fin r → A) :
    restrictFunctorOfUnion f = jStar (unionOfBasicOpens f) (Spec A).ringCatSheaf := by
  unfold restrictFunctorOfUnion Scheme.Modules.restrictFunctor ExtensionByZeroModules.jStar
  congr 1
  ext V
  simp
  rfl

/-- Restriction of complexes of `𝒪_X`-modules to the open subscheme `U`. -/
public abbrev restrictComplexFunctor (f : Fin r → A) :
    CochainComplex (Spec A).Modules ℤ ⥤ CochainComplex (unionScheme f).Modules ℤ :=
  (restrictFunctorOfUnion f).mapHomologicalComplex (up ℤ)

/-- The tilde functor on complexes of `A`-modules. -/
public abbrev tildeFunctorMapComplex (A : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (Spec A).Modules ℤ :=
  (AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)

/-! ### The intersections of the covering of `U` -/

/-- **The image in `X` of an intersection of the covering of `U` is the corresponding
intersection of the basic opens.** -/
public theorem imF_inter_unionCover (f : Fin r → A) {p : ℕ}
    (i : Fin (p + 1) → ULift.{u} (Fin r)) :
    (TopCat.Presheaf.imF (unionOfBasicOpens f)).obj (inter (unionSpaceCover f) i) =
      inter (basicOpens f) (fun k ↦ (i k).down) := by
  apply Opens.ext
  ext x
  change (∃ y : (unionOfBasicOpens f : (Spec A).Opens),
      y ∈ (inter (unionSpaceCover f) i : Set (unionSpace f)) ∧ y.val = x) ↔
    x ∈ (inter (basicOpens f) (fun k ↦ (i k).down) : Set (Spec A).toPresheafedSpace)
  simp only [inter, Opens.coe_iInf, Set.mem_iInter]
  constructor
  · rintro ⟨y, hy, rfl⟩ k
    exact Set.mem_iInter.mp hy k
  · exact fun hx ↦ ⟨⟨x, le_iSup (basicOpens f) (i 0).down (hx 0)⟩, Set.mem_iInter.mpr hx, rfl⟩

/-- The identification of the intersections, as an isomorphism of opens. -/
public def interIsoOfUnionCover (f : Fin r → A) (p : ℕ)
    (i : Fin (p + 1) → ULift.{u} (Fin r)) :
    (TopCat.Presheaf.imF (unionOfBasicOpens f)).obj (inter (unionSpaceCover f) i) ≅
      inter (basicOpens f) (fun k ↦ (i k).down) :=
  eqToIso (imF_inter_unionCover f i)

/-! ### Sections of a restricted module -/

/-- **Sections of the restriction of a module over an open of `U` are its sections over the
image of that open in `X`.** -/
public def restrictPresheafIsoOfUnion (f : Fin r → A) :
    restrictFunctorOfUnion f ⋙
        (SheafOfModules.forget (unionScheme f).ringCatSheaf ⋙
          PresheafOfModules.toPresheaf (unionScheme f).ringCatSheaf.obj) ≅
      (SheafOfModules.forget (Spec A).ringCatSheaf ⋙
          PresheafOfModules.toPresheaf (Spec A).ringCatSheaf.obj) ⋙
        (Functor.whiskeringLeft (Opens (unionSpace f))ᵒᵖ (Opens (Spec A).toPresheafedSpace)ᵒᵖ
            AddCommGrpCat.{u}).obj
          (TopCat.Presheaf.imF (unionOfBasicOpens f)).op :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun W ↦ Iso.refl _) (by intros; rfl))
    (by intros; rfl)

/-- Restriction to `U` is additive, being the restriction functor of the extension-by-zero
adjunction. -/
public instance restrictFunctorOfUnion_additive (f : Fin r → A) :
    (restrictFunctorOfUnion f).Additive := by
  rw [restrictFunctorOfUnion_eq_jStar f]
  exact ExtensionByZeroModules.jStar_additive _ _

/-- Restriction to `U` preserves zero morphisms. -/
public instance restrictFunctorOfUnion_preservesZeroMorphisms (f : Fin r → A) :
    (restrictFunctorOfUnion f).PreservesZeroMorphisms := by
  rw [restrictFunctorOfUnion_eq_jStar f]
  exact ⟨fun _ _ ↦ rfl⟩

/-- Reading the restriction of a module as an abelian presheaf preserves zero morphisms. -/
public theorem restrictPresheafFunctor_preservesZeroMorphisms (f : Fin r → A) :
    (restrictFunctorOfUnion f ⋙
      SheafOfModules.forget (unionScheme f).ringCatSheaf ⋙
        PresheafOfModules.toPresheaf (unionScheme f).ringCatSheaf.obj).PreservesZeroMorphisms :=
  ⟨fun X Y ↦
    (congrArg (SheafOfModules.forget (unionScheme f).ringCatSheaf ⋙
        PresheafOfModules.toPresheaf (unionScheme f).ringCatSheaf.obj).map
      (Functor.map_zero (restrictFunctorOfUnion f) X Y)).trans (Functor.map_zero _ _ _)⟩

/-- Precomposition of abelian presheaves with the image functor on opens preserves zero
morphisms. -/
public instance whiskeringLeft_imF_preservesZeroMorphisms (f : Fin r → A) :
    ((Functor.whiskeringLeft (Opens (unionSpace f))ᵒᵖ
        (Opens (Spec A).toPresheafedSpace)ᵒᵖ AddCommGrpCat.{u}).obj
      (TopCat.Presheaf.imF (unionOfBasicOpens f)).op).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ rfl⟩

/-- Reading a module as an abelian presheaf and then precomposing with the image functor on
opens preserves zero morphisms. -/
public theorem presheafWhiskeringLeft_preservesZeroMorphisms (f : Fin r → A) :
    ((SheafOfModules.forget (Spec A).ringCatSheaf ⋙
        PresheafOfModules.toPresheaf (Spec A).ringCatSheaf.obj) ⋙
      (Functor.whiskeringLeft (Opens (unionSpace f))ᵒᵖ
          (Opens (Spec A).toPresheafedSpace)ᵒᵖ AddCommGrpCat.{u}).obj
        (TopCat.Presheaf.imF (unionOfBasicOpens f)).op).PreservesZeroMorphisms :=
  inferInstance

/-- **Sections of a restricted complex, degreewise.**  The identification of sections of a
restriction with sections over the image, applied degreewise to a complex. -/
public def restrictPresheafComplexIsoOfUnion (f : Fin r → A) :
    restrictComplexFunctor f ⋙
        Stacks.Cech.underlyingPresheafComplexFunctor (unionSpace f)
          (unionScheme f).ringCatSheaf ≅
      Stacks.Cech.underlyingPresheafComplexFunctor (Spec A).toPresheafedSpace
          (Spec A).ringCatSheaf ⋙
        ((Functor.whiskeringLeft (Opens (unionSpace f))ᵒᵖ
              (Opens (Spec A).toPresheafedSpace)ᵒᵖ AddCommGrpCat.{u}).obj
            (TopCat.Presheaf.imF (unionOfBasicOpens f)).op).mapHomologicalComplex (up ℤ) :=
  @NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _
    (restrictPresheafFunctor_preservesZeroMorphisms f)
    (presheafWhiskeringLeft_preservesZeroMorphisms f) (restrictPresheafIsoOfUnion f) (up ℤ)

/-! ### The two total alternating Čech complexes agree -/

/-- **The total alternating Čech complex of the basic opens of `Spec A` is the total
alternating Čech complex of the induced covering of the open subscheme `U`.**  This is the
complex that Tag 08D1 identifies with `colimₑ Hom^•(I^•(f^e), M^•)`, read on `U`. -/
public def alternatingCechTotalIsoOfUnion (f : Fin r → A) :
    Koszul.alternatingCechTotalFunctor f ≅
      tildeFunctorMapComplex A ⋙ restrictComplexFunctor f ⋙
        Stacks.Cech.underlyingPresheafComplexFunctor (unionSpace f)
            (unionScheme f).ringCatSheaf ⋙
          Stacks.Cech.alternatingCechTotalComplexFunctor (unionSpaceCover f) :=
  Functor.isoWhiskerLeft
      (tildeFunctorMapComplex A ⋙ Stacks.Cech.underlyingPresheafComplexFunctor
        (Spec A).toPresheafedSpace (Spec A).ringCatSheaf)
      (Stacks.Cech.alternatingCechTotalComplexFunctorLiftedIso (basicOpens f) (unionSpaceCover f)
        (TopCat.Presheaf.imF (unionOfBasicOpens f)) (interIsoOfUnionCover f)) ≪≫
    Functor.isoWhiskerLeft (tildeFunctorMapComplex A)
      (Functor.isoWhiskerRight (restrictPresheafComplexIsoOfUnion f).symm
        (Stacks.Cech.alternatingCechTotalComplexFunctor (unionSpaceCover f)))

end Koszul.DerivedSystem

end
