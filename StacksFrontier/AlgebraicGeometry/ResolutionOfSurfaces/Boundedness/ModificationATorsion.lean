module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionInFirstCohomology

/-!
# The `a`-torsion in the first cohomology of a normal modification

Let `A` be a normal domain, `f : X ⟶ Spec A` a modification, and `a ∈ A` nonzero. Multiplication
by `a` on `𝒪_X` is injective and its cokernel is the structure sheaf of the closed subscheme
`Z ⊂ X` cut out by `a`, so the cokernel of `A ⟶ Γ(Z, 𝒪_Z)` is the `a`-torsion of `H¹(X, 𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.zeroSchemeStructureSheaf` is `𝒪_X / a𝒪_X`, the structure sheaf of the closed
  subscheme of `X` cut out by an element of the base ring.
* `AlgebraicGeometry.baseToZeroSchemeSections` is the canonical `A`-linear map from `A` to the
  global sections of that sheaf.

## Main results

* `AlgebraicGeometry.mono_baseSmulModules_unit`: multiplication by a nonzero global function is
  injective on the structure sheaf of an integral scheme.
* `AlgebraicGeometry.exists_connecting_base_firstCohomology`: a connecting map from the global
  sections of `𝒪_X / a𝒪_X` to `H¹(X, 𝒪_X)` whose kernel is the image of `A` and whose image is
  the `a`-torsion.
* `AlgebraicGeometry.nonempty_quotient_baseToZeroSchemeSections_equiv_torsionBy`: the cokernel of
  `A ⟶ Γ(Z, 𝒪_Z)` and the `a`-torsion of `H¹(X, 𝒪_X)` are isomorphic `A`-modules.
* `AlgebraicGeometry.length_quotient_baseToZeroSchemeSections_eq`: their lengths agree.

## Implementation notes

The closed subscheme cut out by `a` enters only through its structure sheaf as a sheaf on `X`,
which is the quotient of `𝒪_X` by multiplication by `a`; its global sections are `H⁰(Z, 𝒪_Z)`.

Injectivity of multiplication by `a` is checked on the sections over each open: those over a
nonempty open form a domain in which the restricted function is nonzero, and those over the empty
open vanish. The identification of `A` with the global functions of `X` is the direct-image
statement for a modification of the spectrum of a normal domain.

## References

* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] Scheme.commRingRingCatSheafObj

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))

/-- The structure sheaf of the closed subscheme of `X` cut out by an element of the base ring:
the quotient of `𝒪_X` by multiplication by that element. -/
def zeroSchemeStructureSheaf (a : A) : SheafOfModules.{u} X.ringCatSheaf :=
  cokernel (baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf))

/-- The restriction of a global function of `X` to the closed subscheme cut out by an element of
the base ring. -/
def toZeroSchemeStructureSheaf (a : A) :
    SheafOfModules.unit X.ringCatSheaf ⟶ zeroSchemeStructureSheaf X f a :=
  cokernel.π _

/-- The image of an element of the base ring among the global functions of `X`, as a map of
`A`-modules. -/
def baseSectionLinearMap :
    A →ₗ[A] globalSectionsAsBaseModule X f (SheafOfModules.unit X.ringCatSheaf) where
  toFun r := baseSection X f r
  map_add' r s := map_add ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom r s
  map_smul' r s := map_mul ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom r s

/-- The image of an element of the base ring among the global sections of the closed subscheme
cut out by `a`. -/
def baseToZeroSchemeSections (a : A) :
    A →ₗ[A] globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f a) :=
  (globalSectionsMapAsBaseModule X f (toZeroSchemeStructureSheaf X f a)).hom.comp
    (baseSectionLinearMap X f)

/-- Multiplication by a nonzero global function coming from the base is injective on the structure
sheaf of an integral scheme. -/
theorem mono_baseSmulModules_unit [IsIntegral X] (a : A) (ha : baseSection X f a ≠ 0) :
    Mono (baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf)) := by
  have hinj : ∀ U : (X.Opens)ᵒᵖ,
      Function.Injective
        ((baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf)).val.app U) := by
    intro U
    have key : Function.Injective (fun z : Γ(X, U.unop) =>
        X.presheaf.map (isTerminalTop.from U.unop).op (baseSection X f a) * z) := by
      by_cases hne : Nonempty U.unop
      · have hr : X.presheaf.map (isTerminalTop.from U.unop).op (baseSection X f a) ≠ 0 := by
          intro h0
          exact ha (map_injective_of_isIntegral X (isTerminalTop.from U.unop)
            (h0.trans (map_zero _).symm))
        exact fun _ _ h => mul_left_cancel₀ hr h
      · have hbot : U.unop = ⊥ :=
          TopologicalSpace.Opens.coe_eq_empty.mp
            (Set.not_nonempty_iff_eq_empty.mp fun ⟨z, hz⟩ => hne ⟨⟨z, hz⟩⟩)
        have hsub : Subsingleton Γ(X, U.unop) := hbot ▸ inferInstance
        exact fun _ _ _ => Subsingleton.elim _ _
    exact key
  have hmono : ∀ U, Mono (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      ((SheafOfModules.forget X.ringCatSheaf).map
        (baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf)))).app U) :=
    fun U => ConcreteCategory.mono_of_injective _ (hinj U)
  exact (SheafOfModules.forget _).mono_of_mono_map
    ((PresheafOfModules.toPresheaf _).mono_of_mono_map (NatTrans.mono_of_mono_app _))

/-- The map from `A` to the global functions of a modification of `Spec A` is bijective. -/
private theorem bijective_baseSection_of_isModification [IsNormalDomain A]
    (hf : IsModification f) :
    Function.Bijective ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom := by
  have := hf.isIso_appTop
  exact ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop)

/-- The image of a nonzero element of a normal domain among the global functions of a modification
of its spectrum is nonzero. -/
theorem baseSection_ne_zero_of_isModification [IsNormalDomain A] (hf : IsModification f)
    {a : A} (ha : a ≠ 0) : baseSection X f a ≠ 0 := by
  intro h0
  exact ha ((bijective_baseSection_of_isModification X f hf).1 (h0.trans (map_zero _).symm))

/-- The canonical map from `A` to the global functions of a modification of `Spec A` is
surjective, so the image of `A` among the global sections of any sheaf of modules on `X` is the
image of `Γ(X, 𝒪_X)`. -/
theorem range_baseToZeroSchemeSections [IsNormalDomain A] (hf : IsModification f) (a : A) :
    LinearMap.range (baseToZeroSchemeSections X f a) =
      LinearMap.range
        (globalSectionsMapAsBaseModule X f (toZeroSchemeStructureSheaf X f a)).hom := by
  have hsurj : Function.Surjective (baseSectionLinearMap X f) :=
    (bijective_baseSection_of_isModification X f hf).2
  rw [baseToZeroSchemeSections, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj,
    Submodule.map_top]

/-- **The connecting map of the sequence `0 ⟶ 𝒪_X ⟶ 𝒪_X ⟶ 𝒪_Z ⟶ 0` cut out by `a` has the image
of `A` as its kernel and the `a`-torsion of `H¹(X, 𝒪_X)` as its image.** -/
theorem exists_connecting_base_firstCohomology [IsNormalDomain A] (hf : IsModification f)
    {a : A} (ha : a ≠ 0) :
    ∃ δ : globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f a) →ₗ[A]
        firstCohomologyAsBaseModule X f,
      LinearMap.ker δ = LinearMap.range (baseToZeroSchemeSections X f a) ∧
      LinearMap.range δ = Submodule.torsionBy A (firstCohomologyAsBaseModule X f) a := by
  have : IsIntegral X := hf.source_isIntegral
  have hmono := mono_baseSmulModules_unit X f a
    (baseSection_ne_zero_of_isModification X f hf ha)
  have hS : (ShortComplex.mk (baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf))
      (toZeroSchemeStructureSheaf X f a) (cokernel.condition _)).ShortExact := by
    have h : (ShortComplex.cokernelSequence
        (baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf))).ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := hmono
        epi_g := inferInstance }
    exact h
  obtain ⟨δ, hker, hrange⟩ := exists_connecting_firstCohomology X f a
    (zeroSchemeStructureSheaf X f a) (toZeroSchemeStructureSheaf X f a) (cokernel.condition _) hS
  exact ⟨δ, hker.trans (range_baseToZeroSchemeSections X f hf a).symm, hrange⟩

/-- **Stacks Project, Tag 0AXK.** For a nonzero element `a` of a normal domain `A` and a
modification `f : X ⟶ Spec A`, the cokernel of `A ⟶ H⁰(Z, 𝒪_Z)`, for `Z ⊂ X` cut out by `a`, is
the `a`-torsion submodule of `H¹(X, 𝒪_X)`. -/
@[stacks 0AXK]
theorem nonempty_quotient_baseToZeroSchemeSections_equiv_torsionBy [IsNormalDomain A]
    (hf : IsModification f) {a : A} (ha : a ≠ 0) :
    Nonempty ((globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f a) ⧸
        LinearMap.range (baseToZeroSchemeSections X f a)) ≃ₗ[A]
      Submodule.torsionBy A (firstCohomologyAsBaseModule X f) a) := by
  obtain ⟨δ, hker, hrange⟩ := exists_connecting_base_firstCohomology X f hf ha
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans
    (δ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))⟩

/-- The cokernel of `A ⟶ H⁰(Z, 𝒪_Z)` and the `a`-torsion of `H¹(X, 𝒪_X)` have the same length. -/
theorem length_quotient_baseToZeroSchemeSections_eq [IsNormalDomain A] (hf : IsModification f)
    {a : A} (ha : a ≠ 0) :
    Module.length A (globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f a) ⧸
        LinearMap.range (baseToZeroSchemeSections X f a))
      = Module.length A (Submodule.torsionBy A (firstCohomologyAsBaseModule X f) a) :=
  (nonempty_quotient_baseToZeroSchemeSections_equiv_torsionBy X f hf ha).some.length_eq

end AlgebraicGeometry

end
