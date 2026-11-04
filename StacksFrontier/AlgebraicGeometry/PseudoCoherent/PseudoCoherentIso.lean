module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectLocalRep
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.CategoryTheory.Functor.NatIsoMonoEpi
import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence does not depend on the representative

Let `X` be a ringed space and let `E` be an object of the derived category of `𝒪_X`-modules.
Stacks 08CC says that (1) if every point of `X` has an open neighbourhood `U` on which `E`
receives a morphism in `D(𝒪_U)` from a strictly perfect complex which is an isomorphism on
cohomology above `m` and an epimorphism in degree `m`, then `E` is `m`-pseudo-coherent, and
(2) if `E` is `m`-pseudo-coherent then *every* complex representing `E` is `m`-pseudo-coherent.

## Main definitions

* `AlgebraicGeometry.RingedSpace.restrictModulesOfLE` restricts `𝒪_U`-modules to an open
  subspace `V ≤ U` of `X`, both `U` and `V` being opens of `X`; it is restriction to the slice
  `Over U` of the site of opens of `X`, pushed to `Over V` and transported back.
* `AlgebraicGeometry.RingedSpace.localOverFunctor` reindexes the opens of `V` as objects of the
  slice `Over V'` of the site of opens of the subspace `U`, when `V'` is the open of `U`
  corresponding to `V`.
* `AlgebraicGeometry.RingedSpace.restrictOverHom`,
  `AlgebraicGeometry.RingedSpace.restrictOverComplexHom` and
  `AlgebraicGeometry.RingedSpace.restrictOverHomotopy` carry a morphism of modules, of complexes,
  resp. a homotopy over the slice `Over V'` of the site of opens of `U` to one over the open
  subspace `V` of `X`.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_derived_approximation`: an object of
  the derived category which locally receives a strictly perfect approximation in the derived
  categories of the open subspaces is `m`-pseudo-coherent.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_iso`: every complex representing an
  `m`-pseudo-coherent object of the derived category is `m`-pseudo-coherent.
* `AlgebraicGeometry.RingedSpace.exists_local_strictlyPerfect_approximation`: a strictly perfect
  approximation of a complex `𝒜` on an open `U` transports, after shrinking `U`, to a strictly
  perfect approximation of any complex quasi-isomorphic to `𝒜` over `U`, in particular of the
  restriction of a complex on `X`.
* `AlgebraicGeometry.RingedSpace.exists_local_lift_homotopy_of_le`: on an open subspace `U` of
  `X`, a morphism out of a strictly perfect complex vanishing below degree `a` lifts locally, up
  to homotopy, through a morphism which is an isomorphism on cohomology above `a` and an
  epimorphism in degree `a`, with the lift read on an open `W ≤ U` of `X`.
* `AlgebraicGeometry.RingedSpace.restrictModulesOfLECompIso`: restricting to `U` and then to
  `V ≤ U` is restricting to `V`; `AlgebraicGeometry.RingedSpace.restrictComplexOfLEIso` is the
  same on complexes.
* `AlgebraicGeometry.RingedSpace.isStrictlyPerfect_restrictModulesOfLE`: restriction to a smaller
  open subspace preserves strict perfection.
* `CategoryTheory.isIso_homologyMap_mapHomologicalComplex` and
  `CategoryTheory.epi_homologyMap_mapHomologicalComplex`: an exact functor applied degreewise to
  a morphism of complexes preserves being an isomorphism, resp. an epimorphism, on cohomology.

## Implementation notes

Restriction between opens of `X` is done through the slices of the site of opens of `X`:
`AlgebraicGeometry.RingedSpace.restrictModulesOfLE` is `SheafOfModules.overMap` conjugated by
Mathlib's equivalence `TopologicalSpace.Opens.sheafOfModulesEquivOver`, so that only opens of `X`
appear and transitivity is Mathlib's `SheafOfModules.overFunctorMap`. Restriction to open subspaces
is not transitive on the nose: the ringed spaces `X.restrict W.isOpenEmbedding` and
`(X.restrict U.isOpenEmbedding).restrict …` have different carriers. A morphism over the slice
`Over V'` of the site of opens of an open subspace `U` is carried to one over the open subspace of
`X` corresponding to `V'` by `AlgebraicGeometry.RingedSpace.restrictOverHom`, which is reindexing
along `AlgebraicGeometry.RingedSpace.localOverFunctor` and the identity on sections.

The statements are at `AlgebraicGeometry.RingedSpace.{u, u}` with `𝒪_X`-modules in universe `u`,
the generality in which `StrictlyPerfect.OXMod` and `StrictlyPerfect.IsStrictlyPerfect` are
defined. The derived category of `X` and the derived categories of its open subspaces are
hypotheses with independent universes.

## References

* [The Stacks Project, Lemma 20.46.8 (08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [The Stacks Project, Lemma 20.46.7 (08C9)](https://stacks.math.columbia.edu/tag/08C9)
* [The Stacks Project, Lemma 20.46.6 (08C8)](https://stacks.math.columbia.edu/tag/08C8)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace CategoryTheory

universe w₁ v₁ v₂ u₁ u₂

/-- The degree-`i` short complex of the complex obtained by applying an additive functor `F`
degreewise is the image under `F` of the degree-`i` short complex: both have the same three terms
and the same two maps. -/
public def mapHomologicalComplexShortComplexIso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    {P : CochainComplex C ℤ} (i : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).sc i ≅ (P.sc i).map F :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor'])
    (by simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor'])

/-- `CategoryTheory.mapHomologicalComplexShortComplexIso` as an isomorphism of functors. -/
public def mapHomologicalComplexShortComplexNatIso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive] (i : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℤ) i ≅
      HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i ⋙ F.mapShortComplex :=
  NatIso.ofComponents (fun P => mapHomologicalComplexShortComplexIso F i (P := P)) (by
    intro P Q f
    ext <;> simp [mapHomologicalComplexShortComplexIso, HomologicalComplex.sc,
      HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor'])

/-- An exact functor commutes with the cohomology of a complex: applying `F` degreewise and then
taking `Hⁱ` is isomorphic to taking `Hⁱ` and then applying `F`. -/
public def mapHomologicalComplexHomologyNatIso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (i : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i ⋙ F :=
  let FHC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let SCC := HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i
  let SCD := HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℤ) i
  let HSC := ShortComplex.homologyFunctor C
  let HSD := ShortComplex.homologyFunctor D
  calc FHC ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i
      ≅ FHC ⋙ SCD ⋙ HSD :=
        Functor.isoWhiskerLeft FHC (HomologicalComplex.homologyFunctorIso D _ i)
    _ ≅ (FHC ⋙ SCD) ⋙ HSD := (Functor.associator FHC SCD HSD).symm
    _ ≅ (SCC ⋙ F.mapShortComplex) ⋙ HSD :=
        Functor.isoWhiskerRight (mapHomologicalComplexShortComplexNatIso F i) HSD
    _ ≅ SCC ⋙ F.mapShortComplex ⋙ HSD := Functor.associator SCC F.mapShortComplex HSD
    _ ≅ SCC ⋙ HSC ⋙ F := Functor.isoWhiskerLeft SCC (ShortComplex.homologyFunctorIso F)
    _ ≅ (SCC ⋙ HSC) ⋙ F := (Functor.associator SCC HSC F).symm
    _ ≅ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i ⋙ F :=
        Functor.isoWhiskerRight (HomologicalComplex.homologyFunctorIso C _ i).symm F

/-- An exact functor applied degreewise to a morphism of complexes which is an isomorphism on
cohomology in degree `i` is again an isomorphism on cohomology in degree `i`. -/
public theorem isIso_homologyMap_mapHomologicalComplex {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {P Q : CochainComplex C ℤ} (f : P ⟶ Q)
    (i : ℤ) (hf : IsIso (HomologicalComplex.homologyMap f i)) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) i) :=
  (NatIso.isIso_map_iff (mapHomologicalComplexHomologyNatIso F i) f).mpr
    (inferInstance : IsIso (F.map (HomologicalComplex.homologyMap f i)))

/-- An exact functor applied degreewise to a morphism of complexes which is an epimorphism on
cohomology in degree `i` is again an epimorphism on cohomology in degree `i`. -/
public theorem epi_homologyMap_mapHomologicalComplex {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {P Q : CochainComplex C ℤ} (f : P ⟶ Q)
    (i : ℤ) (hf : Epi (HomologicalComplex.homologyMap f i)) :
    Epi (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) i) :=
  (NatIso.epi_map_iff (mapHomologicalComplexHomologyNatIso F i) f).mpr
    (inferInstance : Epi (F.map (HomologicalComplex.homologyMap f i)))

/-- Cohomology in a fixed degree takes a composite to the composite, so a composite of morphisms
of complexes which are isomorphisms on cohomology in degree `j` is again one. -/
public theorem isIso_homologyMap_comp {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {P Q R : CochainComplex C ℤ} (a : P ⟶ Q) (b : Q ⟶ R) (j : ℤ)
    (ha : IsIso (HomologicalComplex.homologyMap a j))
    (hb : IsIso (HomologicalComplex.homologyMap b j)) :
    IsIso (HomologicalComplex.homologyMap (a ≫ b) j) := by
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

/-- Cohomology in a fixed degree takes a composite to the composite, so a composite of morphisms
of complexes which are epimorphisms on cohomology in degree `j` is again one. -/
public theorem epi_homologyMap_comp {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {P Q R : CochainComplex C ℤ} (a : P ⟶ Q) (b : Q ⟶ R) (j : ℤ)
    (ha : Epi (HomologicalComplex.homologyMap a j))
    (hb : Epi (HomologicalComplex.homologyMap b j)) :
    Epi (HomologicalComplex.homologyMap (a ≫ b) j) := by
  rw [HomologicalComplex.homologyMap_comp]
  exact epi_comp _ _

/-- If `β ≫ φ` is homotopic to `ψ` and `Hʲ(φ)` is an isomorphism, then `Hʲ(β) = Hʲ(ψ) ≫ Hʲ(φ)⁻¹`. -/
private theorem homologyMap_eq_comp_inv_of_homotopy {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {P A B : CochainComplex C ℤ} {β : P ⟶ B} {φ : B ⟶ A} {ψ : P ⟶ A}
    (H : Homotopy (β ≫ φ) ψ) (j : ℤ) (hφ : IsIso (HomologicalComplex.homologyMap φ j)) :
    HomologicalComplex.homologyMap β j =
      HomologicalComplex.homologyMap ψ j ≫
        CategoryTheory.inv (HomologicalComplex.homologyMap φ j) :=
  (IsIso.eq_comp_inv _).2 (by simpa [HomologicalComplex.homologyMap_comp] using H.homologyMap_eq j)

/-- A lift up to homotopy inherits the cohomological properties of what it lifts: if `β ≫ φ` is
homotopic to `ψ` and `Hʲ(φ)` and `Hʲ(ψ)` are isomorphisms, then so is `Hʲ(β)`. -/
public theorem isIso_homologyMap_of_homotopy {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {P A B : CochainComplex C ℤ} {β : P ⟶ B} {φ : B ⟶ A} {ψ : P ⟶ A}
    (H : Homotopy (β ≫ φ) ψ) (j : ℤ) (hφ : IsIso (HomologicalComplex.homologyMap φ j))
    (hψ : IsIso (HomologicalComplex.homologyMap ψ j)) :
    IsIso (HomologicalComplex.homologyMap β j) := by
  rw [homologyMap_eq_comp_inv_of_homotopy H j hφ]
  infer_instance

/-- A lift up to homotopy inherits the cohomological properties of what it lifts: if `β ≫ φ` is
homotopic to `ψ`, `Hʲ(φ)` is an isomorphism and `Hʲ(ψ)` is an epimorphism, then `Hʲ(β)` is an
epimorphism. -/
public theorem epi_homologyMap_of_homotopy {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {P A B : CochainComplex C ℤ} {β : P ⟶ B} {φ : B ⟶ A} {ψ : P ⟶ A}
    (H : Homotopy (β ≫ φ) ψ) (j : ℤ) (hφ : IsIso (HomologicalComplex.homologyMap φ j))
    (hψ : Epi (HomologicalComplex.homologyMap ψ j)) :
    Epi (HomologicalComplex.homologyMap β j) := by
  rw [homologyMap_eq_comp_inv_of_homotopy H j hφ]
  infer_instance

/-- Cohomology of the numerator of a left fraction: if `α = Q(γ) ≫ Q(f)⁻¹` in the derived
category, then `Hʲ(Q(γ)) = Hʲ(α) ≫ Hʲ(Q(f))`. -/
public theorem homologyFunctor_map_Q_map_eq_of_left_fac {C : Type u₁} [Category.{v₁} C]
    [Abelian C] [HasDerivedCategory.{w₁} C] {E F G : CochainComplex C ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (γ : E ⟶ G) (f : F ⟶ G)
    (hf : IsIso (DerivedCategory.Q.map f))
    (hfac : α = DerivedCategory.Q.map γ ≫ CategoryTheory.inv (DerivedCategory.Q.map f))
    (j : ℤ) :
    (DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map γ) =
      (DerivedCategory.homologyFunctor C j).map α ≫
        (DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map f) := by
  rw [← (IsIso.eq_comp_inv _).1 hfac, CategoryTheory.Functor.map_comp]

/-- The numerator of a left fraction inherits the cohomological properties of the fraction: if
`α = Q(γ) ≫ Q(f)⁻¹` and `Hʲ(α)` is an isomorphism, then `Hʲ(γ)` is an isomorphism. -/
public theorem isIso_homologyMap_of_left_fac {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] {E F G : CochainComplex C ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (γ : E ⟶ G) (f : F ⟶ G)
    (hf : IsIso (DerivedCategory.Q.map f))
    (hfac : α = DerivedCategory.Q.map γ ≫ CategoryTheory.inv (DerivedCategory.Q.map f))
    (j : ℤ) (hα : IsIso ((DerivedCategory.homologyFunctor C j).map α)) :
    IsIso (HomologicalComplex.homologyMap γ j) := by
  have hQf : IsIso ((DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map f)) := by
    have := hf
    infer_instance
  refine (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C j) γ).mp ?_
  show IsIso ((DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map γ))
  rw [homologyFunctor_map_Q_map_eq_of_left_fac α γ f hf hfac j]
  infer_instance

/-- The numerator of a left fraction inherits the cohomological properties of the fraction: if
`α = Q(γ) ≫ Q(f)⁻¹` and `Hʲ(α)` is an epimorphism, then `Hʲ(γ)` is an epimorphism. -/
public theorem epi_homologyMap_of_left_fac {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] {E F G : CochainComplex C ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (γ : E ⟶ G) (f : F ⟶ G)
    (hf : IsIso (DerivedCategory.Q.map f))
    (hfac : α = DerivedCategory.Q.map γ ≫ CategoryTheory.inv (DerivedCategory.Q.map f))
    (j : ℤ) (hα : Epi ((DerivedCategory.homologyFunctor C j).map α)) :
    Epi (HomologicalComplex.homologyMap γ j) := by
  have hQf : IsIso ((DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map f)) := by
    have := hf
    infer_instance
  refine (NatIso.epi_map_iff (DerivedCategory.homologyFunctorFactors C j) γ).mp ?_
  show Epi ((DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map γ))
  rw [homologyFunctor_map_Q_map_eq_of_left_fac α γ f hf hfac j]
  have : Epi ((DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map f)) :=
    IsIso.epi_of_iso _
  exact epi_comp _ _

/-- A quasi-isomorphism of complexes read off from the invertibility of its image in the derived
category: the morphism induced on cohomology in every degree is an isomorphism. -/
public theorem isIso_homologyMap_of_isIso_Q_map {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] {E F : CochainComplex C ℤ} (f : E ⟶ F)
    (hf : IsIso (DerivedCategory.Q.map f)) (j : ℤ) :
    IsIso (HomologicalComplex.homologyMap f j) :=
  (quasiIsoAt_iff_isIso_homologyMap f j).1
    (((DerivedCategory.isIso_Q_map_iff_quasiIso (C := C) f).mp hf).quasiIsoAt j)

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

universe u d d'

variable {X : RingedSpace.{u, u}}

/-! ### Restriction from an open subspace to a smaller one -/

/-- Restriction of `𝒪_U`-modules to a smaller open subspace `V ≤ U` of `X`, both `U` and `V`
being opens of `X`.

It is defined through the slices of the site of opens of `X`: an `𝒪_U`-module is viewed as a
sheaf of modules over `Over U`, pushed forward along `Over.map` to `Over V`, and viewed again as
an `𝒪_V`-module. -/
public def restrictModulesOfLE (X : RingedSpace.{u, u}) {U V : Opens X.carrier} (h : V ≤ U) :
    OXMod.{u, u} (X.restrict U.isOpenEmbedding) ⥤
      OXMod.{u, u} (X.restrict V.isOpenEmbedding) :=
  (U.sheafOfModulesEquivOver (structureSheafOfRings X)).inverse ⋙
    SheafOfModules.overMap (structureSheafOfRings X) (homOfLE h) ⋙
      (V.sheafOfModulesEquivOver (structureSheafOfRings X)).functor

/-- Restriction to a smaller open subspace is additive. -/
public instance restrictModulesOfLE_additive (X : RingedSpace.{u, u}) {U V : Opens X.carrier}
    (h : V ≤ U) : (restrictModulesOfLE X h).Additive where
  map_add := by intros; ext _ _; rfl

/-- Pushing a sheaf of modules over the slice `Over U` forward to a smaller slice `Over V`
preserves finite limits. -/
public theorem overMap_preservesFiniteLimits (X : RingedSpace.{u, u}) {U V : Opens X.carrier}
    (h : V ≤ U) :
    PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (structureSheafOfRings X) (homOfLE h)) := by
  refine ⟨fun J _ _ => ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
  refine ⟨isLimitOfReflects (SheafOfModules.forget ((structureSheafOfRings X).over V))
    (PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun W => ?_)⟩
  exact isLimitOfPreserves
    (SheafOfModules.evaluation ((structureSheafOfRings X).over U)
      (Opposite.op ((Over.map (homOfLE h)).obj W.unop))) hc

/-- Restriction to a smaller open subspace preserves finite limits. -/
public instance restrictModulesOfLE_preservesFiniteLimits (X : RingedSpace.{u, u})
    {U V : Opens X.carrier} (h : V ≤ U) :
    PreservesFiniteLimits (restrictModulesOfLE.{u} X h) := by
  have : PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (structureSheafOfRings X) (homOfLE h)) :=
    overMap_preservesFiniteLimits X h
  exact inferInstanceAs (PreservesFiniteLimits
    ((U.sheafOfModulesEquivOver.{u} (structureSheafOfRings X)).inverse ⋙
      SheafOfModules.overMap.{u} (structureSheafOfRings X) (homOfLE h) ⋙
      (V.sheafOfModulesEquivOver.{u} (structureSheafOfRings X)).functor))

/-- Restriction to a smaller open subspace preserves finite colimits. -/
public instance restrictModulesOfLE_preservesFiniteColimits (X : RingedSpace.{u, u})
    {U V : Opens X.carrier} (h : V ≤ U) :
    PreservesFiniteColimits (restrictModulesOfLE.{u} X h) := by
  have : (SheafOfModules.overMap.{u} (structureSheafOfRings X) (homOfLE h)).IsLeftAdjoint :=
    inferInstance
  exact inferInstanceAs (PreservesFiniteColimits
    ((U.sheafOfModulesEquivOver.{u} (structureSheafOfRings X)).inverse ⋙
      SheafOfModules.overMap.{u} (structureSheafOfRings X) (homOfLE h) ⋙
      (V.sheafOfModulesEquivOver.{u} (structureSheafOfRings X)).functor))

/-- Restricting `𝒪_X`-modules to `U` and then to `V ≤ U` is restricting them to `V`. -/
public def restrictModulesOfLECompIso (X : RingedSpace.{u, u}) {U V : Opens X.carrier}
    (h : V ≤ U) : restrictModules X U ⋙ restrictModulesOfLE X h ≅ restrictModules X V := by
  let R := structureSheafOfRings X
  let EU := U.sheafOfModulesEquivOver.{u} R
  let EV := V.sheafOfModulesEquivOver.{u} R
  let F := SheafOfModules.overMap.{u} R (homOfLE h)
  have eBegin : restrictModules X U ⋙ (EU.inverse ⋙ F ⋙ EV.functor) ≅
      SheafOfModules.overFunctor.{u} R V ⋙ EV.functor :=
    calc restrictModules X U ⋙ (EU.inverse ⋙ F ⋙ EV.functor)
        ≅ (SheafOfModules.overFunctor.{u} R U ⋙ EU.functor) ⋙ (EU.inverse ⋙ F ⋙ EV.functor) :=
          Functor.isoWhiskerRight (restrictModulesIsoOverComp X U).symm _
      _ ≅ SheafOfModules.overFunctor.{u} R U ⋙ EU.functor ⋙ (EU.inverse ⋙ F ⋙ EV.functor) :=
          Functor.associator _ _ _
      _ ≅ SheafOfModules.overFunctor.{u} R U ⋙ (EU.functor ⋙ EU.inverse) ⋙ (F ⋙ EV.functor) :=
          Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm
      _ ≅ SheafOfModules.overFunctor.{u} R U ⋙ (F ⋙ EV.functor) :=
          Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight EU.unitIso.symm _)
      _ ≅ (SheafOfModules.overFunctor.{u} R U ⋙ F) ⋙ EV.functor :=
          (Functor.associator _ _ _).symm
      _ ≅ SheafOfModules.overFunctor.{u} R V ⋙ EV.functor :=
          Functor.isoWhiskerRight (SheafOfModules.overFunctorMap.{u} R (homOfLE h)) EV.functor
  exact eBegin.trans (restrictModulesIsoOverComp X V)

/-- Restricting a complex of `𝒪_X`-modules to `U` and then to `V ≤ U` gives its restriction
to `V`. -/
public def restrictComplexOfLEIso (X : RingedSpace.{u, u}) {U V : Opens X.carrier} (h : V ≤ U)
    (A : CochainComplex (OXMod.{u, u} X) ℤ) :
    ((restrictModulesOfLE X h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (restrictComplex A U) ≅ restrictComplex A V :=
  (Functor.mapHomologicalComplexCompIso
    (restrictModulesOfLECompIso X h) (ComplexShape.up ℤ)).app A

/-- Restriction to an open subspace of a morphism of complexes of `𝒪_X`-modules, with source and
target written as `AlgebraicGeometry.RingedSpace.restrictComplex`. -/
public def restrictComplexMap {A B : CochainComplex (OXMod.{u, u} X) ℤ} (g : A ⟶ B)
    (U : Opens X.carrier) : restrictComplex A U ⟶ restrictComplex B U :=
  ((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).map g

/-- Restriction to an open subspace preserves being an isomorphism on cohomology in a given
degree, since it is exact. -/
public theorem isIso_homologyMap_restrictComplexMap {A B : CochainComplex (OXMod.{u, u} X) ℤ}
    (g : A ⟶ B) (U : Opens X.carrier) (j : ℤ)
    (h : IsIso (HomologicalComplex.homologyMap g j)) :
    IsIso (HomologicalComplex.homologyMap (restrictComplexMap g U) j) :=
  isIso_homologyMap_mapHomologicalComplex (restrictModules X U) g j h

/-- Restriction to an open subspace preserves being an epimorphism on cohomology in a given
degree, since it is exact. -/
public theorem epi_homologyMap_restrictComplexMap {A B : CochainComplex (OXMod.{u, u} X) ℤ}
    (g : A ⟶ B) (U : Opens X.carrier) (j : ℤ)
    (h : Epi (HomologicalComplex.homologyMap g j)) :
    Epi (HomologicalComplex.homologyMap (restrictComplexMap g U) j) :=
  epi_homologyMap_mapHomologicalComplex (restrictModules X U) g j h

/-- Restriction to a smaller open subspace takes `𝒪_U` to `𝒪_V`. -/
public def restrictModulesOfLEUnitIso (X : RingedSpace.{u, u}) {U V : Opens X.carrier}
    (h : V ≤ U) :
    (restrictModulesOfLE X h).obj (structureModule (X.restrict U.isOpenEmbedding)) ≅
      structureModule (X.restrict V.isOpenEmbedding) :=
  let R := structureSheafOfRings X
  let EU := U.sheafOfModulesEquivOver.{u} R
  let EV := V.sheafOfModulesEquivOver.{u} R
  EV.functor.mapIso
      ((SheafOfModules.overMap.{u} R (homOfLE h)).mapIso
        (EU.inverse.mapIso (U.sheafOfModulesEquivOverUnit R).symm ≪≫
          (EU.unitIso.app (SheafOfModules.unit (R.over U))).symm) ≪≫
        SheafOfModules.overMapUnitIso (R := R) (homOfLE h)) ≪≫
    V.sheafOfModulesEquivOverUnit R

/-- Restriction to a smaller open subspace preserves being a direct summand of a finite free
module. -/
public theorem isDirectSummandOfFiniteFree_restrictModulesOfLE {U V : Opens X.carrier}
    (h : V ≤ U) {A : OXMod.{u, u} (X.restrict U.isOpenEmbedding)}
    (hA : IsDirectSummandOfFiniteFree A) :
    IsDirectSummandOfFiniteFree ((restrictModulesOfLE X h).obj A) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract _).mp hA
  exact (isDirectSummandOfFiniteFree_iff_retract _).mpr
    ⟨n, ⟨(ρ.map (restrictModulesOfLE X h)).trans
      (((restrictModulesOfLE X h).retractMapBiproduct
          (fun _ : Fin n => structureModule (X.restrict U.isOpenEmbedding))).trans
        (Retract.ofIso (biproduct.mapIso fun _ => restrictModulesOfLEUnitIso X h)))⟩⟩

/-- The restriction of a strictly perfect complex of `𝒪_U`-modules to a smaller open subspace is
strictly perfect. -/
public theorem isStrictlyPerfect_restrictModulesOfLE {U V : Opens X.carrier} (h : V ≤ U)
    {P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ}
    (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect (((restrictModulesOfLE X h).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) where
  bounded := hP.bounded.subset fun _ hi hz => hi ((restrictModulesOfLE X h).isZero_obj hz)
  directSummand i := isDirectSummandOfFiniteFree_restrictModulesOfLE h (hP.directSummand i)

/-! ### Carrying a local lift from the slice idiom to a smaller open subspace -/

/-- Reindexing of the opens of `W` as objects of the slice `Over V` of the site of opens of the
subspace `U`, for `W ≤ U` an open of `X` contained in the open `V` of `U`.

An open `Z` of `W` is sent to its image in `X`, viewed as an open of `U` contained in `V`. -/
public def localOverFunctor (U W : Opens X.carrier) (hWU : W ≤ U)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) (hWV : ∀ p : U, p.1 ∈ W → p ∈ V) :
    Opens W ⥤ Over V where
  obj Z := Over.mk (homOfLE (show
      U.overEquivalence.functor.obj
        (Over.mk (homOfLE (le_trans (leOfHom (W.overEquivalence.inverse.obj Z).hom) hWU))) ≤ V from
      fun p hp => hWV p ((leOfHom (W.overEquivalence.inverse.obj Z).hom) hp)))
  map f := Over.homMk (U.overEquivalence.functor.map
    (Over.homMk ((W.overEquivalence.inverse.map f).left)))

variable {U W : Opens X.carrier}

/-- A morphism of `𝒪_U`-modules restricted to the slice `Over V` of the site of opens of the
subspace `U`, read as a morphism of their restrictions to the open subspace `W ≤ U` of `X`.

This is pure reindexing: the sections over an open `Z` of `W` of the restriction of a module to
`W` are its sections over the image of `Z`, which is the value at `Z` of
`AlgebraicGeometry.RingedSpace.localOverFunctor`. -/
public def restrictOverHom (hWU : W ≤ U) (V : Opens (X.restrict U.isOpenEmbedding).carrier)
    (hWV : ∀ p : U, p.1 ∈ W → p ∈ V)
    {P Q : OXMod.{u, u} (X.restrict U.isOpenEmbedding)}
    (f : (SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj P ⟶
      (SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj Q) :
    (restrictModulesOfLE X hWU).obj P ⟶ (restrictModulesOfLE X hWU).obj Q where
  val :=
    { app := fun Z => by
        letI : Module ↑((W.sheafRestrict.obj (structureSheafOfRings X)).obj.obj Z)
            ↑(((restrictModulesOfLE X hWU).obj P).val.obj Z) := ModuleCat.isModule _
        letI : Module ↑((W.sheafRestrict.obj (structureSheafOfRings X)).obj.obj Z)
            ↑(((restrictModulesOfLE X hWU).obj Q).val.obj Z) := ModuleCat.isModule _
        exact ModuleCat.ofHom
          (X := ↑(((restrictModulesOfLE X hWU).obj P).val.obj Z))
          (Y := ↑(((restrictModulesOfLE X hWU).obj Q).val.obj Z))
          { toFun := fun x => f.val.app ((localOverFunctor U W hWU V hWV).op.obj Z) x
            map_add' := (f.val.app ((localOverFunctor U W hWU V hWV).op.obj Z)).hom.map_add'
            map_smul' := by
              intro r x
              exact (f.val.app ((localOverFunctor U W hWU V hWV).op.obj Z)).hom.map_smul' _ x }
      naturality := by
        intro Z Z' g
        ext x
        exact congrArg (fun k => k x)
          (f.val.naturality ((localOverFunctor U W hWU V hWV).op.map g)) }

variable (hWU : W ≤ U) (V : Opens (X.restrict U.isOpenEmbedding).carrier)
  (hWV : ∀ p : U, p.1 ∈ W → p ∈ V)

/-- Reindexing a composite is the composite of the reindexings. -/
public theorem restrictOverHom_comp {P Q R : OXMod.{u, u} (X.restrict U.isOpenEmbedding)}
    (a : (SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj P ⟶
      (SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj Q)
    (b : (SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj Q ⟶
      (SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj R) :
    restrictOverHom hWU V hWV (a ≫ b) =
      restrictOverHom hWU V hWV a ≫ restrictOverHom hWU V hWV b := by
  ext Z x
  rfl

/-- Reindexing the restriction of a morphism of `𝒪_U`-modules to the slice gives its restriction
to the open subspace `W`. -/
public theorem restrictOverHom_map {P Q : OXMod.{u, u} (X.restrict U.isOpenEmbedding)}
    (g : P ⟶ Q) :
    restrictOverHom hWU V hWV ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).map g) =
      (restrictModulesOfLE X hWU).map g := by
  ext Z x
  rfl

/-- Reindexing takes the zero morphism to the zero morphism. -/
public theorem restrictOverHom_zero {P Q : OXMod.{u, u} (X.restrict U.isOpenEmbedding)} :
    restrictOverHom hWU V hWV (0 : (SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj P ⟶
      (SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj Q) = 0 := by
  ext Z x
  rfl

/-- Reindexing is additive. -/
public theorem restrictOverHom_add {P Q : OXMod.{u, u} (X.restrict U.isOpenEmbedding)}
    (a b : (SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj P ⟶
      (SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).obj Q) :
    restrictOverHom hWU V hWV (a + b) =
      restrictOverHom hWU V hWV a + restrictOverHom hWU V hWV b := by
  ext Z x
  rfl

variable {P Q : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ}

/-- A morphism of complexes of `𝒪_U`-modules restricted to the slice `Over V`, read degreewise as
a morphism of their restrictions to the open subspace `W ≤ U` of `X`. -/
public def restrictOverComplexHom
    (f : ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ⟶
      ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Q) :
    ((restrictModulesOfLE X hWU).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      ((restrictModulesOfLE X hWU).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q where
  f i := restrictOverHom hWU V hWV (f.f i)
  comm' i j hij := by
    refine (congrArg (restrictOverHom hWU V hWV (P := P.X i) (Q := Q.X j)) (f.comm i j)).trans ?_
    ext Z x
    rfl

/-- The degreewise description of `AlgebraicGeometry.RingedSpace.restrictOverComplexHom`. -/
@[simp]
public theorem restrictOverComplexHom_f
    (f : ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ⟶
      ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Q) (i : ℤ) :
    (restrictOverComplexHom hWU V hWV f).f i = restrictOverHom hWU V hWV (f.f i) := rfl

/-- Reindexing a composite of morphisms of complexes is the composite of the reindexings. -/
public theorem restrictOverComplexHom_comp
    {R : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ}
    (a : ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ⟶
      ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Q)
    (b : ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Q ⟶
      ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj R) :
    restrictOverComplexHom hWU V hWV (a ≫ b) =
      restrictOverComplexHom hWU V hWV a ≫ restrictOverComplexHom hWU V hWV b :=
  HomologicalComplex.hom_ext _ _ fun i => restrictOverHom_comp hWU V hWV (a.f i) (b.f i)

/-- Reindexing the restriction to the slice of a morphism of complexes of `𝒪_U`-modules gives its
restriction to the open subspace `W`. -/
public theorem restrictOverComplexHom_map (g : P ⟶ Q) :
    restrictOverComplexHom hWU V hWV (((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding))
          V).mapHomologicalComplex (ComplexShape.up ℤ)).map g) =
      ((restrictModulesOfLE X hWU).mapHomologicalComplex (ComplexShape.up ℤ)).map g :=
  HomologicalComplex.hom_ext _ _ fun i => restrictOverHom_map hWU V hWV (g.f i)

/-- A homotopy between morphisms of complexes of `𝒪_U`-modules restricted to the slice `Over V`,
read as a homotopy between their reindexings to the open subspace `W ≤ U` of `X`. -/
public def restrictOverHomotopy
    {f g : ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ⟶
      ((SheafOfModules.overFunctor
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Q}
    (H : Homotopy f g) :
    Homotopy (restrictOverComplexHom hWU V hWV f) (restrictOverComplexHom hWU V hWV g) where
  hom i j := restrictOverHom hWU V hWV (H.hom i j)
  zero i j hij := by rw [H.zero i j hij, restrictOverHom_zero]
  comm i := by
    refine (congrArg (restrictOverHom hWU V hWV (P := P.X i) (Q := Q.X i)) (H.comm i)).trans ?_
    ext Z x
    rfl

/-! ### Local lifts up to homotopy on an open subspace -/

/-- Let `U` be an open of the ringed space `X`, let `α : 𝒫 ⟶ 𝒜` be a morphism of complexes of
`𝒪_U`-modules out of a strictly perfect complex `𝒫` with `𝒫ʲ = 0` for `j < a`, and let
`f : ℬ ⟶ 𝒜` be an isomorphism on cohomology in every degree above `a` and an epimorphism on
cohomology in degree `a`. Then every point of `U` has an open neighbourhood `W ≤ U` in `X` over
which the restriction of `α` lifts through the restriction of `f` up to homotopy. -/
public theorem exists_local_lift_homotopy_of_le
    {A B : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ}
    (α : P ⟶ A) (f : B ⟶ A) (a : ℤ) (hP : IsStrictlyPerfect P)
    (hPa : ∀ j : ℤ, j < a → IsZero (P.X j))
    (hf_gt : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_a : Epi (HomologicalComplex.homologyMap f a)) (x : X.carrier) (hxU : x ∈ U) :
    ∃ (W : Opens X.carrier) (hWU : W ≤ U), x ∈ W ∧
      ∃ β : ((restrictModulesOfLE X hWU).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
          ((restrictModulesOfLE X hWU).mapHomologicalComplex (ComplexShape.up ℤ)).obj B,
        Nonempty (Homotopy
          (β ≫ ((restrictModulesOfLE X hWU).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          (((restrictModulesOfLE X hWU).mapHomologicalComplex (ComplexShape.up ℤ)).map α)) := by
  obtain ⟨V, hxV, β, ⟨H⟩⟩ := exists_local_lift_homotopy α f a hP hPa hf_gt hf_a ⟨x, hxU⟩
  have hWU : (U.overEquivalence.inverse.obj V).left ≤ U :=
    leOfHom (U.overEquivalence.inverse.obj V).hom
  have hWV (p : U) (hp : p.1 ∈ (U.overEquivalence.inverse.obj V).left) : p ∈ V :=
    Subtype.val_injective.mem_set_image.1 hp
  exact ⟨_, hWU, ⟨⟨x, hxU⟩, hxV, rfl⟩, restrictOverComplexHom hWU V hWV β,
    ⟨(Homotopy.ofEq (by rw [restrictOverComplexHom_comp, restrictOverComplexHom_map])).trans
      ((restrictOverHomotopy hWU V hWV H).trans
        (Homotopy.ofEq (restrictOverComplexHom_map hWU V hWV α)))⟩⟩

/-! ### Pseudo-coherence does not depend on the representative -/

/-- Let `U` be an open of the ringed space `X`, let `𝒜` be a complex of `𝒪_U`-modules receiving a
morphism `α` from a strictly perfect complex `𝒫` which is an isomorphism on cohomology above `m`
and an epimorphism in degree `m`, and let `f : ℱ|_U ⟶ 𝒜` be a quasi-isomorphism from the
restriction to `U` of a complex `ℱ` of `𝒪_X`-modules. Then every point of `U` has an open
neighbourhood `W ⊆ U` in `X` carrying a strictly perfect complex and a morphism to `ℱ|_W` with the
same two cohomological properties. -/
public theorem exists_local_strictlyPerfect_approximation {K : CochainComplex (OXMod.{u, u} X) ℤ}
    {A P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ}
    (hP : IsStrictlyPerfect P) (m : ℤ) (α : P ⟶ A)
    (hα : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hα₀ : Epi (HomologicalComplex.homologyMap α m))
    (f : restrictComplex K U ⟶ A)
    (hf : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap f j))
    (x : X.carrier) (hxU : x ∈ U) :
    ∃ W : Opens X.carrier, x ∈ W ∧
      ∃ P' : CochainComplex (OXMod.{u, u} (X.restrict W.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P' ∧
        ∃ β : P' ⟶ restrictComplex K W,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
          Epi (HomologicalComplex.homologyMap β m) := by
  obtain ⟨a, ha⟩ := Stacks.Cohomology.LocalNullHomotopy.exists_lower_bound hP
  obtain ⟨W, hWU, hxW, β, ⟨H⟩⟩ := exists_local_lift_homotopy_of_le α f a hP ha
    (fun j _ => hf j) (by have := hf a; exact IsIso.epi_of_iso _) x hxU
  refine ⟨W, hxW, ((restrictModulesOfLE X hWU).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    isStrictlyPerfect_restrictModulesOfLE hWU hP, β ≫ (restrictComplexOfLEIso X hWU K).hom, ?_, ?_⟩
  · exact fun j hj => isIso_homologyMap_comp _ _ j
      (isIso_homologyMap_of_homotopy H j
        (isIso_homologyMap_mapHomologicalComplex _ f j (hf j))
        (isIso_homologyMap_mapHomologicalComplex _ α j (hα j hj)))
      inferInstance
  · exact epi_homologyMap_comp _ _ m
      (epi_homologyMap_of_homotopy H m
        (isIso_homologyMap_mapHomologicalComplex _ f m (hf m))
        (epi_homologyMap_mapHomologicalComplex _ α m hα₀))
      (IsIso.epi_of_iso _)

variable [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- Let `E` be an `m`-pseudo-coherent object of the derived category of `𝒪_X`-modules. Then every
complex of `𝒪_X`-modules representing `E` is `m`-pseudo-coherent. -/
@[stacks 08CC "part (2)", sga "6 I 2.2" "a)"]
public theorem isPseudoCoherentComplexFrom_of_iso (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ)
    (hE : IsPseudoCoherentFrom E m) (K : CochainComplex (OXMod.{u, u} X) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E) : IsPseudoCoherentComplexFrom K m := by
  obtain ⟨K', hK', ⟨e'⟩⟩ := hE
  obtain ⟨G, γ, f, hf, hfac⟩ := DerivedCategory.left_fac (e' ≪≫ e.symm).hom
  have hγiso : IsIso (DerivedCategory.Q.map γ) := by
    rw [← (IsIso.eq_comp_inv _).1 hfac]
    infer_instance
  have hγ : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap γ j) := fun j =>
    isIso_homologyMap_of_isIso_Q_map γ hγiso j
  have hfq : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap f j) := fun j =>
    isIso_homologyMap_of_isIso_Q_map f hf j
  intro x
  obtain ⟨U, hxU, P, hP, α, hα, hα₀⟩ := hK' x
  have hαG : ∀ j : ℤ, m < j →
      IsIso (HomologicalComplex.homologyMap (α ≫ restrictComplexMap γ U) j) := fun j hj =>
    isIso_homologyMap_comp _ _ j (hα j hj) (isIso_homologyMap_restrictComplexMap γ U j (hγ j))
  have hαG₀ : Epi (HomologicalComplex.homologyMap (α ≫ restrictComplexMap γ U) m) :=
    epi_homologyMap_comp _ _ m hα₀
      (by have := isIso_homologyMap_restrictComplexMap γ U m (hγ m); exact IsIso.epi_of_iso _)
  exact exists_local_strictlyPerfect_approximation (K := K) hP m
    (α ≫ restrictComplexMap γ U) hαG hαG₀ (restrictComplexMap f U)
    (fun j => isIso_homologyMap_restrictComplexMap f U j (hfq j)) x hxU

/-- Let `E` be an object of the derived category of `𝒪_X`-modules and suppose that every point of
`X` has an open neighbourhood `U` on which some strictly perfect complex `𝒫` maps to `E|_U` in
`D(𝒪_U)` by a morphism which is an isomorphism on cohomology above `m` and an epimorphism in degree
`m`. Then `E` is `m`-pseudo-coherent. Here `E|_U` is presented as `Q(𝒦|_U)` for a complex `𝒦`
representing `E`. -/
@[stacks 08CC "part (1)", sga "6 I 2.2" "b) (ii')=>(ii)"]
public theorem isPseudoCoherentFrom_of_local_derived_approximation
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ) (K : CochainComplex (OXMod.{u, u} X) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        ∃ α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (restrictComplex K U),
          (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor _ m).map α)) :
    IsPseudoCoherentFrom E m := by
  refine ⟨K, fun x => ?_, ⟨e⟩⟩
  obtain ⟨U, hxU, P, hP, α, hα, hα₀⟩ := h x
  obtain ⟨G, γ, f, hf, hfac⟩ := DerivedCategory.left_fac α
  exact exists_local_strictlyPerfect_approximation (K := K) hP m γ
    (fun j hj => isIso_homologyMap_of_left_fac α γ f hf hfac j (hα j hj))
    (epi_homologyMap_of_left_fac α γ f hf hfac m hα₀) f
    (fun j => isIso_homologyMap_of_isIso_Q_map f hf j) x hxU

end AlgebraicGeometry.RingedSpace

end
