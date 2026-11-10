module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.ShortExactFunctorsTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# The Mayer--Vietoris triangle of a cover by two opens, for module coefficients

Let `X` be a scheme covered by two open subschemes `U` and `V` and let `Λ` be a ring.  For every
object `K` of the derived category of sheaves of `Λ`-modules on the small étale site of `X`
there is a distinguished triangle
`j_{U ∩ V!} K|_{U ∩ V} ⟶ j_{U!} K|_U ⊕ j_{V!} K|_V ⟶ K ⟶ (j_{U ∩ V!} K|_{U ∩ V})[1]`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleCoverComparison`: for an étale morphism factoring through
  an open immersion `j`, the canonical map `j_{W!} j_W^{-1} ⟶ j_! j^{-1}`.
* `Stacks.EtaleCohomology.etaleModuleCoverBiprod`: the functor `F ↦ j_{U!}F|_U ⊕ j_{V!}F|_V`.
* `Stacks.EtaleCohomology.etaleModuleCoverToBiprod` and
  `Stacks.EtaleCohomology.etaleModuleCoverFromBiprod`: the two maps of the Mayer--Vietoris
  sequence.

## Main results

* `Stacks.EtaleCohomology.shortExact_etaleModuleCoverShortComplex`: the resulting short complex
  of sheaves of `Λ`-modules is short exact.
* `Stacks.EtaleCohomology.exists_distTriang_etaleModuleCover`: **Stacks Project, Tag 0GKK**, the
  distinguished triangle above, for an arbitrary ring of coefficients.
* `Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleInverseImage_family`: a family of morphisms
  to `X` whose images cover `X` jointly reflects isomorphisms of sheaves of modules on
  `X_étale`.
* `Stacks.EtaleCohomology.jointlyReflectIsomorphisms_etaleModuleInverseImage_residueGeometricPoint`
  — the inverse images at the residue geometric points of `X` jointly reflect isomorphisms.

## The sign

The source displays the sequence
`0 → j_{U ∩ V!}F|_{U ∩ V} → j_{U!}F|_U ⊕ j_{V!}F|_V → F → 0`
without signs.  It is exact only with a sign: on `U ∩ V` both summands restrict to `F` and the
two canonical maps to `F` agree, so an unsigned first map composes with the second to twice the
inclusion rather than to zero.  The first map below is therefore `(ι, -ι)`, the second
`(ε_U, ε_V)`; that is the corrected form, and it is what the source's own proof supports.

## Implementation notes

The proof is the one of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle`, which is the
case `Λ = ℤ`, carried out over an arbitrary ring: the four functors involved are exact, so it
suffices to produce the short exact sequence of sheaves of modules, and that is checked at the
geometric points of `X`.  Nothing in the argument is special to abelian groups — what the
coefficients have to supply is that `j_!` is exact, which is
`Stacks.EtaleCohomology.etaleModuleExtensionByZero_preservesFiniteLimits` (Tag 03S5 for module
coefficients), and that the fibre functors at a conservative family of points jointly reflect
isomorphisms, which Mathlib's
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms` gives
for any concrete coefficient category whose forgetful functor preserves filtered colimits.

## References

* [Stacks Project, Tag 0GKK](https://stacks.math.columbia.edu/tag/0GKK)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 0F70](https://stacks.math.columbia.edu/tag/0F70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe w u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ]

/-! ### Exactness of restriction along an étale morphism -/

section EtaleDirectImage

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- Restriction of sheaves of modules along an étale morphism preserves finite limits, being
right adjoint to extension by zero. -/
instance etaleModuleRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModuleRestriction.{u, r} Λ j) :=
  have : PreservesLimits (etaleModuleRestriction.{u, r} Λ j) :=
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- Restriction of sheaves of modules along an étale morphism preserves finite colimits, being
left adjoint to the direct image; with the previous instance this says it is exact. -/
instance etaleModuleRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleRestriction.{u, r} Λ j) :=
  have : PreservesColimits (etaleModuleRestriction.{u, r} Λ j) :=
    (etaleModuleEtaleDirectImageAdj.{u, r} Λ j).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

end EtaleDirectImage

/-! ### Comparing the two inverse images along an étale morphism -/

/-- The inverse image on sheaves of modules of a composite is the composite of the inverse
images, in the other order. -/
def etaleModuleInverseImageCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleModuleInverseImage.{u, r} Λ (f ≫ g) ≅
      etaleModuleInverseImage.{u, r} Λ g ⋙ etaleModuleInverseImage.{u, r} Λ f := by
  let : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) g :=
    ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) g :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let e : smallEtaleBaseChange (f ≫ g) ≅
      smallEtaleBaseChange g ⋙ smallEtaleBaseChange f :=
    MorphismProperty.Over.pullbackComp f g
  exact ((Functor.sheafAdjunctionContinuous (smallEtaleBaseChange (f ≫ g))
      (ModuleCat.{max (u + 1) r} Λ) Z.smallEtaleTopology X.smallEtaleTopology).leftAdjointUniq
    (((Functor.sheafAdjunctionContinuous (smallEtaleBaseChange g)
        (ModuleCat.{max (u + 1) r} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).comp
      (Functor.sheafAdjunctionContinuous (smallEtaleBaseChange f)
        (ModuleCat.{max (u + 1) r} Λ) Y.smallEtaleTopology X.smallEtaleTopology)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' e.symm (ModuleCat.{max (u + 1) r} Λ)
        Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology)))

/-! ### Sections over an empty object -/

/-- A sheaf of modules on the small étale site has zero sections over an object whose underlying
scheme is empty. -/
theorem isZero_etaleModule_sections_of_isEmpty {X : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ X) (V : X.Etale) (hV : IsEmpty V.left) :
    IsZero (F.obj.obj (op V)) :=
  (F.isTerminalOfBotCover V (bot_mem_smallEtaleTopology_of_isEmpty V hV)).isZero

/-- A sheaf of modules on the small étale site all of whose modules of sections vanish is
zero. -/
theorem isZero_etaleModule_of_forall_isZero_sections {X : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ X) (hF : ∀ V : X.Etale, IsZero (F.obj.obj (op V))) : IsZero F :=
  IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) F
    ((Functor.isZero_iff _).2 fun V ↦ hF V.unop)

/-! ### Vanishing away from the open an extension by zero comes from -/

section Disjoint

variable {T U X : Scheme.{u}} (g : T ⟶ X) (j : U ⟶ X) [Etale j]
  (hgj : Disjoint (Set.range g.base) (Set.range j.base))

include hgj

/-- Restricting to `U` a direct image of sheaves of modules along a morphism whose image misses
`U` gives zero. -/
theorem isZero_etaleModuleRestriction_etaleModuleDirectImage_of_disjoint
    (G : EtaleModules.{u, r} Λ T) :
    IsZero ((etaleModuleRestriction.{u, r} Λ j).obj
      ((etaleModuleDirectImage.{u, r} Λ g).obj G)) :=
  isZero_etaleModule_of_forall_isZero_sections Λ _ fun W ↦
    isZero_etaleModule_sections_of_isEmpty Λ G _
      (isEmpty_smallEtaleBaseChange_smallEtaleCompose_of_disjoint g j hgj W)

/-- The inverse image along `g` of an extension by zero of sheaves of modules from `U` is zero
when the images of `g` and of `j` are disjoint. -/
theorem isZero_etaleModuleInverseImage_extensionByZero_of_disjoint
    (G : EtaleModules.{u, r} Λ U) :
    IsZero ((etaleModuleInverseImage.{u, r} Λ g).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj G)) := by
  rw [IsZero.iff_id_eq_zero]
  exact ((etaleModuleInverseImageAdj.{u, r} Λ g).homEquiv _ _).injective
    (((etaleModuleExtensionByZeroAdj.{u, r} Λ j).homEquiv _ _).injective
      ((isZero_etaleModuleRestriction_etaleModuleDirectImage_of_disjoint Λ g j hgj _).eq_of_tgt
        _ _))

end Disjoint

/-! ### The counit after an inverse image factoring through the open -/

section Factors

variable {T U X : Scheme.{u}} (g : T ⟶ X) (j : U ⟶ X) [IsOpenImmersion j] (k : T ⟶ U)
  (hk : k ≫ j = g)

include hk

/-- The counit `j_! j^{-1} F ⟶ F` of an open immersion becomes an isomorphism on sheaves of
modules after inverse image along any morphism factoring through `j`. -/
theorem isIso_etaleModuleInverseImage_map_counit_of_factors (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleInverseImage.{u, r} Λ g).map
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F)) := by
  subst hk
  have _ : IsIso ((etaleModuleInverseImage.{u, r} Λ j).map
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F)) :=
    (NatIso.isIso_map_iff (etaleModuleInverseImageRestrictionIso.{u, r} Λ j)
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F)).mpr
        (isIso_etaleModuleRestriction_map_counit.{u, r} Λ j F)
  exact (NatIso.isIso_map_iff (etaleModuleInverseImageCompIso.{u, r} Λ k j)
    ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F)).mpr
      (Functor.map_isIso (etaleModuleInverseImage.{u, r} Λ k) _)

/-- The counit `j_! j^{-1} F ⟶ F` of an open immersion becomes an isomorphism on sheaves of
modules after restriction along any étale morphism factoring through `j`. -/
theorem isIso_etaleModuleRestriction_map_counit_of_factors [Etale g]
    (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleRestriction.{u, r} Λ g).map
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F)) :=
  (NatIso.isIso_map_iff (etaleModuleInverseImageRestrictionIso.{u, r} Λ g)
    ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F)).mp
      (isIso_etaleModuleInverseImage_map_counit_of_factors Λ g j k hk F)

end Factors

/-! ### A covering family of morphisms reflects isomorphisms -/

/-- A family of morphisms `g a : T a ⟶ X` whose images cover `X` jointly reflects isomorphisms
of sheaves of `Λ`-modules on the small étale site of `X`.

The residue geometric points of the `T a`, pushed forward along the `g a`, form a conservative
family of points of `X_étale`, and the stalk of an inverse image at such a point is the stalk of
the original sheaf at its image. -/
theorem isIso_of_isIso_etaleModuleInverseImage_family {X : Scheme.{u}} {ι : Type u}
    {T : ι → Scheme.{u}} (g : ∀ a, T a ⟶ X)
    (hg : ⋃ a, Set.range (g a).base = Set.univ)
    {F G : EtaleModules.{u, r} Λ X} (γ : F ⟶ G)
    (hγ : ∀ a, IsIso ((etaleModuleInverseImage.{u, r} Λ (g a)).map γ)) : IsIso γ := by
  have _ : PreservesColimits
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r, r, max (u + 1) r,
      max (u + 1) r} Λ
  have _ : PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) r} Λ)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat) (forget AddCommGrpCat)
  have hcov := iUnion_range_residueGeometricPoint_comp_eq_univ g hg
  let Φ := fun p : (a : ι) × (T a) ↦
    (pointSmallEtale (residueGeometricPoint (T p.1) p.2 ≫ g p.1)).ulift.{max (u + 1) r}
  have hP : (ObjectProperty.ofObj Φ).IsConservativeFamilyOfPoints :=
    Scheme.isConservative_pointSmallEtale_ulift _ hcov
  have happ : ∀ q : (ObjectProperty.ofObj Φ).FullSubcategory,
      IsIso (q.obj.sheafFiber.map γ) := by
    rintro ⟨_, ⟨a, t⟩⟩
    have _ := hγ a
    exact (NatIso.isIso_map_iff (etaleModuleInverseImageSheafFiberIso.{u, r} Λ (g a)
      (residueGeometricPoint (T a) t)) γ).mp
        (Functor.map_isIso ((pointSmallEtale
          (residueGeometricPoint (T a) t)).ulift.{max (u + 1) r}).sheafFiber _)
  exact (hP.jointlyReflectIsomorphisms (ModuleCat.{max (u + 1) r} Λ)).isIso γ

/-- The inverse images of sheaves of `Λ`-modules at the residue geometric points of a scheme
`X` jointly reflect isomorphisms. -/
theorem jointlyReflectIsomorphisms_etaleModuleInverseImage_residueGeometricPoint
    {X : Scheme.{u}} :
    JointlyReflectIsomorphisms (fun x : X ↦
      etaleModuleInverseImage.{u, r} Λ (residueGeometricPoint X x)) :=
  ⟨isIso_of_isIso_etaleModuleInverseImage_family Λ (residueGeometricPoint X)
    (Set.eq_univ_of_forall fun x ↦
      Set.mem_iUnion.2 ⟨x, default, residueGeometricPoint_apply X x default⟩)⟩

/-! ### The comparison of two extensions by zero -/

section Comparison

variable {W U X : Scheme.{u}} (jW : W ⟶ X) [Etale jW] (j : U ⟶ X) [IsOpenImmersion j]
  (k : W ⟶ U) (hk : k ≫ j = jW)

include hk

/-- For an étale `jW` factoring through the open immersion `j`, restricting the counit of
`j_! ⊣ j^{-1}` along `jW` gives an isomorphism of functors. -/
def etaleModuleRestrictionCounitIso :
    etaleModuleExtensionByZeroOfRestriction.{u, r} Λ j ⋙ etaleModuleRestriction.{u, r} Λ jW ≅
      etaleModuleRestriction.{u, r} Λ jW := by
  have _ : ∀ F, IsIso ((Functor.whiskerRight
      (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit
      (etaleModuleRestriction.{u, r} Λ jW)).app F) :=
    isIso_etaleModuleRestriction_map_counit_of_factors Λ jW j k hk
  have _ : IsIso (Functor.whiskerRight (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit
      (etaleModuleRestriction.{u, r} Λ jW)) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerRight (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit
    (etaleModuleRestriction.{u, r} Λ jW))

/-- The canonical map `j_{W!} j_W^{-1} ⟶ j_! j^{-1}` of sheaves of modules attached to an étale
`jW` factoring through the open immersion `j`: the transpose, under `j_{W!} ⊣ j_W^{-1}`, of the
inverse of `Stacks.EtaleCohomology.etaleModuleRestrictionCounitIso`. -/
def etaleModuleCoverComparison :
    etaleModuleExtensionByZeroOfRestriction.{u, r} Λ jW ⟶
      etaleModuleExtensionByZeroOfRestriction.{u, r} Λ j :=
  Functor.whiskerRight (etaleModuleRestrictionCounitIso.{u, r} Λ jW j k hk).inv
      (etaleModuleExtensionByZero.{u, r} Λ jW) ≫
    Functor.whiskerLeft (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ j)
      (etaleModuleExtensionByZeroAdj.{u, r} Λ jW).counit

/-- The comparison followed by the counit of `j_! ⊣ j^{-1}` is the counit of
`j_{W!} ⊣ j_W^{-1}`; this is what pins the comparison down. -/
theorem etaleModuleCoverComparison_comp_counit (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleCoverComparison.{u, r} Λ jW j k hk).app F ≫
        (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F =
      (etaleModuleExtensionByZeroAdj.{u, r} Λ jW).counit.app F := by
  have hinv : (etaleModuleRestrictionCounitIso.{u, r} Λ jW j k hk).inv.app F ≫
      (etaleModuleRestriction.{u, r} Λ jW).map
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F) = 𝟙 _ :=
    (etaleModuleRestrictionCounitIso.{u, r} Λ jW j k hk).inv_hom_id_app F
  have hnat := (etaleModuleExtensionByZeroAdj.{u, r} Λ jW).counit.naturality
    ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F)
  simp only [Functor.comp_map, Functor.id_map] at hnat
  dsimp only [etaleModuleCoverComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc, ← hnat, ← Functor.map_comp_assoc, hinv]
  simp

end Comparison

/-! ### Inverse images at a residue geometric point -/

section ResidueGeometricPoint

variable {X : Scheme.{u}}

/-- A residue geometric point at a point of an open subscheme factors through that open
subscheme. -/
theorem exists_hom_comp_ι_eq_residueGeometricPoint (W : X.Opens) (y : X) (hy : y ∈ W) :
    ∃ κ : Spec (.of (SeparableClosure (X.residueField y))) ⟶ (W : Scheme.{u}),
      κ ≫ W.ι = residueGeometricPoint X y := by
  have hsub : Set.range (residueGeometricPoint X y) ⊆ Set.range W.ι := by
    rintro z ⟨t, rfl⟩
    rwa [Scheme.Opens.range_ι, residueGeometricPoint_apply]
  exact ⟨IsOpenImmersion.lift W.ι (residueGeometricPoint X y) hsub,
    IsOpenImmersion.lift_fac _ _ hsub⟩

/-- The counit `j_{W!} F|_W ⟶ F` becomes an isomorphism of sheaves of modules after inverse
image at a residue geometric point lying in the open subscheme `W`. -/
theorem isIso_etaleModuleInverseImage_residueGeometricPoint_map_counit (W : X.Opens) (y : X)
    (hy : y ∈ W) (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleInverseImage.{u, r} Λ (residueGeometricPoint X y)).map
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ W.ι).counit.app F)) := by
  obtain ⟨κ, hκ⟩ := exists_hom_comp_ι_eq_residueGeometricPoint W y hy
  exact isIso_etaleModuleInverseImage_map_counit_of_factors Λ _ W.ι κ hκ F

/-- An extension by zero from an open subscheme `W` has zero inverse image at a residue
geometric point outside `W`. -/
theorem isZero_etaleModuleInverseImage_residueGeometricPoint_extensionByZero (W : X.Opens)
    (y : X) (hy : y ∉ W) (F : EtaleModules.{u, r} Λ X) :
    IsZero ((etaleModuleInverseImage.{u, r} Λ (residueGeometricPoint X y)).obj
      ((etaleModuleExtensionByZeroOfRestriction.{u, r} Λ W.ι).obj F)) := by
  have hd : Disjoint (Set.range (residueGeometricPoint X y).base) (Set.range (W.ι).base) := by
    rw [Set.disjoint_left]
    rintro z ⟨t, rfl⟩ hz
    rw [Scheme.Opens.range_ι, residueGeometricPoint_apply] at hz
    exact hy hz
  exact isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ _ W.ι hd _

variable (W W' : X.Opens) (k : (W : Scheme.{u}) ⟶ (W' : Scheme.{u})) (hk : k ≫ W'.ι = W.ι)
  (y : X) (F : EtaleModules.{u, r} Λ X)

/-- The comparison `j_{W!} F|_W ⟶ j_{W'!} F|_{W'}` of two extensions by zero is an isomorphism
after inverse image at a residue geometric point of `W`: both sides then compute the counit. -/
theorem isIso_etaleModuleInverseImage_residueGeometricPoint_map_coverComparison_of_mem
    (hyW : y ∈ W) (hyW' : y ∈ W') :
    IsIso ((etaleModuleInverseImage.{u, r} Λ (residueGeometricPoint X y)).map
      ((etaleModuleCoverComparison.{u, r} Λ W.ι W'.ι k hk).app F)) := by
  have _ := isIso_etaleModuleInverseImage_residueGeometricPoint_map_counit Λ W y hyW F
  have _ := isIso_etaleModuleInverseImage_residueGeometricPoint_map_counit Λ W' y hyW' F
  have hfac : (etaleModuleInverseImage.{u, r} Λ (residueGeometricPoint X y)).map
        ((etaleModuleCoverComparison.{u, r} Λ W.ι W'.ι k hk).app F) ≫
        (etaleModuleInverseImage.{u, r} Λ (residueGeometricPoint X y)).map
          ((etaleModuleExtensionByZeroAdj.{u, r} Λ W'.ι).counit.app F) =
      (etaleModuleInverseImage.{u, r} Λ (residueGeometricPoint X y)).map
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ W.ι).counit.app F) := by
    rw [← Functor.map_comp, etaleModuleCoverComparison_comp_counit]
  exact IsIso.of_isIso_fac_right hfac

/-- The comparison `j_{W!} F|_W ⟶ j_{W'!} F|_{W'}` of two extensions by zero is an isomorphism
after inverse image at a residue geometric point outside both opens: both sides vanish. -/
theorem isIso_etaleModuleInverseImage_residueGeometricPoint_map_coverComparison_of_notMem
    (hyW : y ∉ W) (hyW' : y ∉ W') :
    IsIso ((etaleModuleInverseImage.{u, r} Λ (residueGeometricPoint X y)).map
      ((etaleModuleCoverComparison.{u, r} Λ W.ι W'.ι k hk).app F)) :=
  ⟨⟨0, (isZero_etaleModuleInverseImage_residueGeometricPoint_extensionByZero Λ W y hyW
      F).eq_of_src _ _,
    (isZero_etaleModuleInverseImage_residueGeometricPoint_extensionByZero Λ W' y hyW'
      F).eq_of_src _ _⟩⟩

end ResidueGeometricPoint

/-! ### The Mayer--Vietoris short complex of a cover by two opens -/

section Cover

variable {X : Scheme.{u}} (U V : X.Opens)

/-- The functor `F ↦ j_{U!}F|_U ⊕ j_{V!}F|_V` of a pair of open subschemes, on sheaves of
`Λ`-modules. -/
abbrev etaleModuleCoverBiprod : EtaleModules.{u, r} Λ X ⥤ EtaleModules.{u, r} Λ X :=
  Functor.pointwiseBiprod (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ U.ι)
    (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ V.ι)

/-- The canonical map `j_{U ∩ V!}F|_{U ∩ V} ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V`.  The second component
carries a sign: without it the composite with the next map is twice the inclusion of
`j_{U ∩ V!}F|_{U ∩ V}` in `F`, not zero. -/
def etaleModuleCoverToBiprod :
    etaleModuleExtensionByZeroOfRestriction.{u, r} Λ (U ⊓ V).ι ⟶
      etaleModuleCoverBiprod.{u, r} Λ U V :=
  Functor.pointwiseBiprod.lift _ _
    (etaleModuleCoverComparison.{u, r} Λ (U ⊓ V).ι U.ι (X.homOfLE inf_le_left)
      (X.homOfLE_ι _))
    (-etaleModuleCoverComparison.{u, r} Λ (U ⊓ V).ι V.ι (X.homOfLE inf_le_right)
      (X.homOfLE_ι _))

/-- The canonical map `j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F`, given by the two counits. -/
def etaleModuleCoverFromBiprod : etaleModuleCoverBiprod.{u, r} Λ U V ⟶ 𝟭 _ :=
  Functor.pointwiseBiprod.desc _ _ (etaleModuleExtensionByZeroAdj.{u, r} Λ U.ι).counit
    (etaleModuleExtensionByZeroAdj.{u, r} Λ V.ι).counit

/-- The two canonical maps of the Mayer--Vietoris sequence compose to zero. -/
theorem etaleModuleCoverToBiprod_comp_coverFromBiprod (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleCoverToBiprod.{u, r} Λ U V).app F ≫
      (etaleModuleCoverFromBiprod.{u, r} Λ U V).app F = 0 := by
  change biprod.lift
      ((etaleModuleCoverComparison.{u, r} Λ (U ⊓ V).ι U.ι (X.homOfLE inf_le_left)
        (X.homOfLE_ι _)).app F)
      (-((etaleModuleCoverComparison.{u, r} Λ (U ⊓ V).ι V.ι (X.homOfLE inf_le_right)
        (X.homOfLE_ι _)).app F)) ≫
    biprod.desc ((etaleModuleExtensionByZeroAdj.{u, r} Λ U.ι).counit.app F)
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ V.ι).counit.app F) = 0
  rw [biprod.lift_desc, Preadditive.neg_comp, etaleModuleCoverComparison_comp_counit,
    etaleModuleCoverComparison_comp_counit, add_neg_cancel]

/-- Both comparisons out of `j_{U ⊓ V!}F|_{U ⊓ V}`, followed by the counit of the open they
land over, give the counit of `j_{U ⊓ V!} ⊣ j_{U ⊓ V}^{-1}`, hence agree. -/
theorem etaleModuleCoverComparison_counit_comm (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleCoverComparison.{u, r} Λ (U ⊓ V).ι U.ι (X.homOfLE inf_le_left)
          (X.homOfLE_ι _)).app F ≫
        (etaleModuleExtensionByZeroAdj.{u, r} Λ U.ι).counit.app F =
      (etaleModuleCoverComparison.{u, r} Λ (U ⊓ V).ι V.ι (X.homOfLE inf_le_right)
          (X.homOfLE_ι _)).app F ≫
        (etaleModuleExtensionByZeroAdj.{u, r} Λ V.ι).counit.app F := by
  rw [etaleModuleCoverComparison_comp_counit, etaleModuleCoverComparison_comp_counit]

/-- The comparison `j_{U ⊓ V!}F|_{U ⊓ V} ⟶ j_{V!}F|_V` of sheaves of modules is an isomorphism
after inverse image at any residue geometric point of `U`: inside `V` both sides compute the
counit, outside `V` both vanish. -/
theorem isIso_etaleModuleInverseImage_residueGeometricPoint_map_coverComparison_of_mem_left
    (x : X) (F : EtaleModules.{u, r} Λ X) (hxU : x ∈ U) :
    IsIso ((etaleModuleInverseImage.{u, r} Λ (residueGeometricPoint X x)).map
      ((etaleModuleCoverComparison.{u, r} Λ (U ⊓ V).ι V.ι (X.homOfLE inf_le_right)
        (X.homOfLE_ι _)).app F)) := by
  by_cases hxV : x ∈ V
  · exact isIso_etaleModuleInverseImage_residueGeometricPoint_map_coverComparison_of_mem
      Λ (U ⊓ V) V _ _ x F ⟨hxU, hxV⟩ hxV
  · exact isIso_etaleModuleInverseImage_residueGeometricPoint_map_coverComparison_of_notMem
      Λ (U ⊓ V) V _ _ x F (fun h ↦ hxV h.2) hxV

variable (hUV : U ⊔ V = ⊤)

include hUV

/-- The Mayer--Vietoris short exact sequence of a cover of `X` by two open subschemes: for every
sheaf `F` of `Λ`-modules on the small étale site of `X` the sequence
`0 ⟶ j_{U ∩ V!}F|_{U ∩ V} ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`
is short exact, the first map being `(ι, -ι)` and the second the pair of counits.

Exactness is checked at the geometric points of `X`: at a point of `U ∩ V` all four maps become
invertible, and at a point of only one of the two opens the terms belonging to the other open
vanish. -/
theorem shortExact_etaleModuleCoverShortComplex (F : EtaleModules.{u, r} Λ X) :
    (ShortComplex.mk ((etaleModuleCoverToBiprod.{u, r} Λ U V).app F)
      ((etaleModuleCoverFromBiprod.{u, r} Λ U V).app F)
      (etaleModuleCoverToBiprod_comp_coverFromBiprod.{u, r} Λ U V F)).ShortExact := by
  change (ShortComplex.biprodMayerVietoris
      ((etaleModuleCoverComparison.{u, r} Λ (U ⊓ V).ι U.ι (X.homOfLE inf_le_left)
        (X.homOfLE_ι _)).app F)
      ((etaleModuleCoverComparison.{u, r} Λ (U ⊓ V).ι V.ι (X.homOfLE inf_le_right)
        (X.homOfLE_ι _)).app F)
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ U.ι).counit.app F)
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ V.ι).counit.app F)
      (etaleModuleCoverComparison_counit_comm.{u, r} Λ U V F)).ShortExact
  let Lf : (x : X) → EtaleModules.{u, r} Λ X ⥤
      EtaleModules.{u, r} Λ (Spec (.of (SeparableClosure (X.residueField x)))) :=
    fun x ↦ etaleModuleInverseImage.{u, r} Λ (residueGeometricPoint X x)
  have _ : ∀ x, PreservesFiniteLimits (Lf x) := fun x ↦
    etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ (residueGeometricPoint X x)
  have _ : ∀ x, PreservesFiniteColimits (Lf x) := fun x ↦
    etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ (residueGeometricPoint X x)
  have hL : JointlyReflectIsomorphisms Lf :=
    jointlyReflectIsomorphisms_etaleModuleInverseImage_residueGeometricPoint.{u, r} Λ
  refine (hL.shortExact_iff _).2 fun x ↦ ?_
  refine ShortComplex.shortExact_map_biprodMayerVietoris (Lf x) _ _ _ _ _ ?_
  by_cases hxU : x ∈ U
  · have _ := isIso_etaleModuleInverseImage_residueGeometricPoint_map_counit Λ U x hxU F
    have _ :=
      isIso_etaleModuleInverseImage_residueGeometricPoint_map_coverComparison_of_mem_left
        Λ U V x F hxU
    exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_fst _ _ _ _ _
  · have hxV : x ∈ V :=
      (TopologicalSpace.Opens.mem_sup.1 (hUV.ge trivial : x ∈ U ⊔ V)).resolve_left hxU
    have _ := isIso_etaleModuleInverseImage_residueGeometricPoint_map_counit Λ V x hxV F
    have _ := isIso_etaleModuleInverseImage_residueGeometricPoint_map_coverComparison_of_notMem
      Λ (U ⊓ V) U (X.homOfLE inf_le_left) (X.homOfLE_ι _) x F (fun h ↦ hxU h.1) hxU
    exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_snd _ _ _ _ _

/-- **Stacks Project, Tag 0GKK.**  Let `Λ` be a ring and let `X` be a scheme with `X = U ∪ V`
for open subschemes `U` and `V`.  For every object `K` of the derived category of sheaves of
`Λ`-modules on the small étale site of `X` there is a distinguished triangle
`j_{U ∩ V!} K|_{U ∩ V} ⟶ j_{U!} K|_U ⊕ j_{V!} K|_V ⟶ K ⟶ (j_{U ∩ V!} K|_{U ∩ V})[1]`,
the first arrow being `(ι, -ι)` and the second the pair of counits of `j_! ⊣ j^{-1}`, both
induced on the derived category by exactness of the functors involved.

Correction to the source: the displayed sequence is exact only with the Mayer--Vietoris sign on
one of the two components of the first arrow, which is carried here. -/
@[stacks 0GKK "first map carries the Mayer-Vietoris sign"]
theorem exists_distTriang_etaleModuleCover
    [HasDerivedCategory.{w} (EtaleModules.{u, r} Λ X)]
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    ∃ δ : K ⟶ ((etaleModuleExtensionByZeroOfRestriction.{u, r} Λ
        (U ⊓ V).ι).mapDerivedCategory.obj K)⟦(1 : ℤ)⟧,
      Triangle.mk
        ((derivedNatTrans
          (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ (U ⊓ V).ι)
          (etaleModuleCoverBiprod.{u, r} Λ U V)
          (etaleModuleCoverToBiprod.{u, r} Λ U V)).app K)
        (((etaleModuleCoverBiprod.{u, r} Λ U V).mapDerivedCategoryTransToId
          (etaleModuleCoverFromBiprod.{u, r} Λ U V)).app K) δ ∈
        distTriang (DerivedCategory (EtaleModules.{u, r} Λ X)) :=
  DerivedCategory.exists_distTriang_of_natTrans_shortExact_toId _ _
    (etaleModuleCoverToBiprod.{u, r} Λ U V) (etaleModuleCoverFromBiprod.{u, r} Λ U V)
    (etaleModuleCoverToBiprod_comp_coverFromBiprod.{u, r} Λ U V)
    (shortExact_etaleModuleCoverShortComplex.{u, r} Λ U V hUV) K

end Cover

end Stacks.EtaleCohomology

end
