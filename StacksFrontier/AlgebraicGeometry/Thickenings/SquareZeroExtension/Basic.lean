module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QuasiCoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections

/-!
# First-order thickenings and square-zero extensions of the structure sheaf

A square-zero extension of the structure sheaf of a scheme `X` over `S`, whose kernel is
quasi-coherent, defines a scheme on the same topological space and exhibits `X` as a
first-order thickening inside it over `S`. Conversely every first-order thickening over `S`
arises this way.

This file sets up the extension, the short exact sequence `0 ⟶ I ⟶ A ⟶ 𝒪_X ⟶ 0` of sheaves of
abelian groups, the stalks of the extension sheaf, and the locally ringed space it defines.

## Main definitions

* `Stacks.Thickenings.thickenedSpace`: the underlying space of a scheme equipped with a
  prescribed sheaf of rings.
* `Stacks.Thickenings.SquareZeroExtension`: a relative square-zero extension of the
  structure sheaf, together with its quasi-coherent kernel.

## Implementation notes

The kernel is carried as a quasi-coherent sheaf of modules and its scalar action is
characterized by multiplication by arbitrary local lifts. The quotient map is required to be
locally surjective, equivalently surjective on every stalk; surjectivity on sections over
every open is not needed, and epimorphy of sheaves of rings does not express the condition.
The realization records an isomorphism of sheafed spaces so that the identification with the
prescribed sheaf is retained.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Thickenings

private theorem isUnit_of_map_isUnit_of_surjective_squareZero
    {R T : Type u} [CommRing R] [CommRing T] (f : R →+* T)
    (hf : Function.Surjective f) {a : R} (ha : IsUnit (f a))
    (hker : ∀ r ∈ RingHom.ker f, r ^ 2 = 0) : IsUnit a := by
  obtain ⟨b, hb⟩ := hf (↑(ha.unit⁻¹))
  have hab : f (a * b - 1) = 0 := by
    rw [map_sub, map_mul, ← ha.unit_spec, hb]
    simp
  have habker : a * b - 1 ∈ RingHom.ker f := RingHom.mem_ker.mpr hab
  have hnil : IsNilpotent (a * b - 1) :=
    ⟨2, by simpa [pow_two] using hker (a * b - 1) habker⟩
  have habunit : IsUnit (a * b) := by
    have h := hnil.isUnit_one_add
    rwa [show 1 + (a * b - 1) = a * b by ring] at h
  exact isUnit_of_mul_isUnit_left habunit

private theorem isLocalRing_of_surjective_squareZero
    {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing T]
    (f : R →+* T) (hf : Function.Surjective f)
    (hker : ∀ r ∈ RingHom.ker f, r ^ 2 = 0) : IsLocalRing R := by
  let _ : Nontrivial R := hf.nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
  intro a b hab
  have hab' : IsUnit (f a + f b) := by simpa only [map_add] using IsUnit.map f hab
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hab' with ha | hb
  · exact Or.inl (isUnit_of_map_isUnit_of_surjective_squareZero f hf ha hker)
  · exact Or.inr (isUnit_of_map_isUnit_of_surjective_squareZero f hf hb hker)

/-- The sheafed space with the topology of `X` and a prescribed sheaf of rings. -/
public def thickenedSpace (X : Scheme.{u}) (A : TopCat.Sheaf CommRingCat.{u} X) :
    SheafedSpace CommRingCat.{u} where
  carrier := X.carrier
  presheaf := A.presheaf
  IsSheaf := A.2

attribute [-instance] Stacks.SheafOfModules.coefficientSheafification
  Stacks.SheafOfModules.coefficientLocallyBijective in
/-- A relative square-zero extension of `𝒪_X`, including its quasi-coherent kernel. -/
public structure SquareZeroExtension {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The extension sheaf. -/
  A : TopCat.Sheaf CommRingCat.{u} X
  /-- The surjection to the structure sheaf. -/
  π : A ⟶ X.sheaf
  /-- Sections of the structure sheaf lift locally to the extension sheaf. -/
  locallySurjective_π : TopCat.Presheaf.IsLocallySurjective π.hom
  /-- The canonical map from `X` into the ringed space with sheaf `A`. -/
  inclusion : X.toSheafedSpace ⟶ thickenedSpace X A
  inclusion_base : inclusion.hom.base = 𝟙 (X : TopCat)
  inclusion_sheaf : HEq inclusion.hom.c π.hom
  /-- The algebra structure over the base. -/
  toBase : thickenedSpace X A ⟶ S.toSheafedSpace
  over_base : inclusion ≫ toBase = f.toLRSHom.toShHom
  /-- The kernel as a module over `𝒪_X`. -/
  I : X.Modules
  quasicoherent : I.IsQuasicoherent
  /-- The inclusion of the kernel, locally on every open. -/
  ι (U : (Opens X)ᵒᵖ) : I.val.obj U →+ A.presheaf.obj U
  naturality {U V : (Opens X)ᵒᵖ} (g : U ⟶ V) (x : I.val.obj U) :
    ι V (I.val.map g x) = A.presheaf.map g (ι U x)
  mem_kernel (U : (Opens X)ᵒᵖ) (x : I.val.obj U) :
    π.hom.app U (ι U x) = 0
  exact_kernel (U : (Opens X)ᵒᵖ) (a : A.presheaf.obj U)
      (ha : π.hom.app U a = 0) : ∃! x, ι U x = a
  smul_lift (U : (Opens X)ᵒᵖ) (a : A.presheaf.obj U) (x : I.val.obj U) :
    ι U (((I.val.obj U).smul (π.hom.app U a)).asHom.hom x) = a * ι U x
  square_zero (U : (Opens X)ᵒᵖ) (x y : I.val.obj U) :
    ι U x * ι U y = 0

/-- The locally surjective quotient map is also a categorical epimorphism. -/
public theorem SquareZeroExtension.epi_π {X S : Scheme.{u}} {f : X ⟶ S}
    (E : SquareZeroExtension f) : Epi E.π := by
  have : CategoryTheory.Sheaf.IsLocallySurjective E.π := E.locallySurjective_π
  exact CategoryTheory.Sheaf.epi_of_isLocallySurjective E.π

private theorem squareZero_kernelMap_injective
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : (Opens X)ᵒᵖ) : Function.Injective (E.ι U) := by
  intro x y hxy
  obtain ⟨z, -, hzuniq⟩ := E.exact_kernel U (E.ι U x) (E.mem_kernel U x)
  exact (hzuniq x rfl).trans (hzuniq y hxy.symm).symm

theorem squareZero_sectionMap_kernel_eq_range
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : (Opens X)ᵒᵖ) (a : E.A.presheaf.obj U) :
    (E.π.hom.app U).hom a = 0 ↔ a ∈ Set.range (E.ι U) :=
  ⟨fun ha => (E.exact_kernel U a ha).exists, by rintro ⟨x, rfl⟩; exact E.mem_kernel U x⟩

/-- The inclusion of the kernel of a square-zero extension as a map of sheaves of abelian groups,
given by `Stacks.Thickenings.SquareZeroExtension.ι` on sections over every open. -/
def squareZero_kernelSheafInclusion
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj E.I ⟶
      (SheafOfModules.toSheaf
        ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)).obj
        (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)) := by
  refine ⟨{ app U := AddCommGrpCat.ofHom (E.ι U), naturality := ?_ }⟩
  intro U V i
  ext x
  exact E.naturality i x

/-- The quotient map of a square-zero extension as a map of sheaves of abelian groups: the
additive part of `Stacks.Thickenings.SquareZeroExtension.π` on sections over every open. -/
def squareZero_quotientSheafMap
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    (SheafOfModules.toSheaf
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)).obj
      (SheafOfModules.unit
        ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)) ⟶
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) := by
  refine ⟨{
    app := fun U => AddCommGrpCat.ofHom (((E.π.hom.app U).hom).toAddMonoidHom)
    naturality := ?_ }⟩
  intro U V i
  ext x
  exact congrFun (congrArg (fun q => q.hom) (E.π.hom.naturality i)) x

/-- The kernel inclusion of a square-zero extension composed with the quotient map is zero. -/
theorem squareZero_kernel_quotient_comp_zero
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    squareZero_kernelSheafInclusion E ≫ squareZero_quotientSheafMap E = 0 := by
  ext U x
  exact E.mem_kernel U x

private theorem squareZero_kernelSheafInclusion_mono
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    Mono (squareZero_kernelSheafInclusion E) := by
  constructor
  intro Z f g h
  apply (TopCat.Sheaf.forget AddCommGrpCat X).map_injective
  ext U x
  let U' : (Opens X)ᵒᵖ := Opposite.op U
  apply squareZero_kernelMap_injective E U'
  exact congrArg (fun q => q.hom.app U' x) h

private noncomputable def squareZero_kernelFactorElement
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    {Z : TopCat.Sheaf AddCommGrpCat.{u} X}
    (q : Z ⟶ (SheafOfModules.toSheaf
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)).obj
        (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)))
    (hq : ∀ (U : (Opens X)ᵒᵖ) (x : Z.presheaf.obj U),
      (E.π.hom.app U).hom (q.hom.app U x) = 0) :
    (U : (Opens X)ᵒᵖ) → Z.presheaf.obj U → E.I.val.obj U := fun U x =>
    Classical.choose (E.exact_kernel U (q.hom.app U x) (hq U x))
private theorem squareZero_kernelFactorElement_spec
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    {Z : TopCat.Sheaf AddCommGrpCat.{u} X}
    (q : Z ⟶ (SheafOfModules.toSheaf
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)).obj
        (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)))
    (hq : ∀ (U : (Opens X)ᵒᵖ) (x : Z.presheaf.obj U),
      (E.π.hom.app U).hom (q.hom.app U x) = 0)
    (U : (Opens X)ᵒᵖ) (x : Z.presheaf.obj U) :
    E.ι U (squareZero_kernelFactorElement E q hq U x) = q.hom.app U x :=
  (Classical.choose_spec (E.exact_kernel U (q.hom.app U x) (hq U x))).1

private noncomputable def squareZero_kernelFactor
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    {Z : TopCat.Sheaf AddCommGrpCat.{u} X}
    (q : Z ⟶ (SheafOfModules.toSheaf
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)).obj
        (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)))
    (hq : ∀ (U : (Opens X)ᵒᵖ) (x : Z.presheaf.obj U),
      (E.π.hom.app U).hom (q.hom.app U x) = 0) :
    Z ⟶ (SheafOfModules.toSheaf X.ringCatSheaf).obj E.I := by
  classical
  refine ⟨{
    app := fun U => AddCommGrpCat.ofHom {
      toFun := squareZero_kernelFactorElement E q hq U
      map_zero' := by
        apply squareZero_kernelMap_injective E U
        simp only [squareZero_kernelFactorElement_spec, map_zero]
        rfl
      map_add' := by
        intro x y
        apply squareZero_kernelMap_injective E U
        simp only [squareZero_kernelFactorElement_spec, map_add]
        rfl
    }
    naturality := ?_ }⟩
  intro U V i
  ext x
  apply squareZero_kernelMap_injective E V
  change E.ι V (squareZero_kernelFactorElement E q hq V (Z.presheaf.map i x)) =
    E.ι V (E.I.val.map i (squareZero_kernelFactorElement E q hq U x))
  rw [E.naturality i, squareZero_kernelFactorElement_spec,
    squareZero_kernelFactorElement_spec]
  exact congrFun (congrArg (fun t => t.hom) (q.hom.naturality i)) x

private theorem squareZero_kernelFactor_fac
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    {Z : TopCat.Sheaf AddCommGrpCat.{u} X}
    (q : Z ⟶ (SheafOfModules.toSheaf
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)).obj
        (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)))
    (hq : ∀ (U : (Opens X)ᵒᵖ) (x : Z.presheaf.obj U),
      (E.π.hom.app U).hom (q.hom.app U x) = 0) :
    squareZero_kernelFactor E q hq ≫ squareZero_kernelSheafInclusion E = q := by
  apply (TopCat.Sheaf.forget AddCommGrpCat X).map_injective
  ext U x
  let U' : (Opens X)ᵒᵖ := Opposite.op U
  change E.ι U' (squareZero_kernelFactorElement E q hq U' x) = q.hom.app U' x
  exact squareZero_kernelFactorElement_spec E q hq U' x

private theorem squareZero_kernelFactor_unique
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    {Z : TopCat.Sheaf AddCommGrpCat.{u} X}
    (q : Z ⟶ (SheafOfModules.toSheaf
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)).obj
        (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)))
    (hq : ∀ (U : (Opens X)ᵒᵖ) (x : Z.presheaf.obj U),
      (E.π.hom.app U).hom (q.hom.app U x) = 0)
    (r : Z ⟶ (SheafOfModules.toSheaf X.ringCatSheaf).obj E.I)
    (hr : r ≫ squareZero_kernelSheafInclusion E = q) :
    r = squareZero_kernelFactor E q hq := by
  have := squareZero_kernelSheafInclusion_mono E
  exact (cancel_mono (squareZero_kernelSheafInclusion E)).1
    (hr.trans (squareZero_kernelFactor_fac E q hq).symm)

private noncomputable def squareZero_kernelSheafInclusion_isKernel
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    IsLimit (KernelFork.ofι (f := squareZero_quotientSheafMap E)
      (squareZero_kernelSheafInclusion E)
      (squareZero_kernel_quotient_comp_zero E)) := by
  refine KernelFork.IsLimit.ofι (squareZero_kernelSheafInclusion E)
    (squareZero_kernel_quotient_comp_zero E)
    (fun {Z} q hq => squareZero_kernelFactor E q fun U x => congrArg (fun t => t.hom.app U x) hq)
    (fun {Z} q hq => squareZero_kernelFactor_fac E q fun U x =>
      congrArg (fun t => t.hom.app U x) hq)
    (fun {Z} q hq r hr => squareZero_kernelFactor_unique E q
      (fun U x => congrArg (fun t => t.hom.app U x) hq) r hr)

private theorem squareZero_kernelSheaf_sequence_exact
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    (ShortComplex.mk (squareZero_kernelSheafInclusion E)
      (squareZero_quotientSheafMap E) (squareZero_kernel_quotient_comp_zero E)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (squareZero_kernelSheafInclusion_isKernel E)

private theorem squareZero_quotientSheafMap_epi
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    Epi (squareZero_quotientSheafMap E) := by
  have htype : TopCat.Presheaf.IsLocallySurjective
      (Functor.whiskerRight (squareZero_quotientSheafMap E).hom
        (forget AddCommGrpCat.{u})) := by
    change TopCat.Presheaf.IsLocallySurjective
      (Functor.whiskerRight E.π.hom (forget CommRingCat.{u}))
    exact (CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget
      (Opens.grothendieckTopology (X : TopCat)) E.π.hom).mp E.locallySurjective_π
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi (squareZero_quotientSheafMap E)).mp
    ((CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget
      (Opens.grothendieckTopology (X : TopCat))
      (squareZero_quotientSheafMap E).hom).mpr htype)

/-- For a square-zero extension `E` of `𝒪_X`, the sequence `0 ⟶ I ⟶ A ⟶ 𝒪_X ⟶ 0` of sheaves of
abelian groups is short exact. -/
theorem squareZero_kernelSheaf_sequence_shortExact
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    (ShortComplex.mk (squareZero_kernelSheafInclusion E)
      (squareZero_quotientSheafMap E) (squareZero_kernel_quotient_comp_zero E)).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · exact squareZero_kernelSheaf_sequence_exact E
  · exact squareZero_kernelSheafInclusion_mono E
  · exact squareZero_quotientSheafMap_epi E

/-- The inclusion of the kernel of a square-zero extension as a map of sheaves of abelian groups,
given by `Stacks.Thickenings.SquareZeroExtension.ι` on sections over every open. -/
public def SquareZeroExtension.kernelSheafInclusion
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj E.I ⟶
      (SheafOfModules.toSheaf
        ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)).obj
        (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)) := by
  refine ⟨{ app U := AddCommGrpCat.ofHom (E.ι U), naturality := ?_ }⟩
  intro U V i
  ext x
  exact E.naturality i x

/-- The quotient map of a square-zero extension as a map of sheaves of abelian groups: the
additive part of `Stacks.Thickenings.SquareZeroExtension.π` on sections over every open. -/
public def SquareZeroExtension.quotientSheafMap
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    (SheafOfModules.toSheaf
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)).obj
      (SheafOfModules.unit
        ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)) ⟶
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) := by
  refine ⟨{
    app := fun U => AddCommGrpCat.ofHom (((E.π.hom.app U).hom).toAddMonoidHom)
    naturality := ?_ }⟩
  intro U V i
  ext x
  exact congrFun (congrArg (fun q => q.hom) (E.π.hom.naturality i)) x

/-- The kernel inclusion of a square-zero extension composed with the quotient map is zero. -/
public theorem SquareZeroExtension.kernel_quotient_comp_zero
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    E.kernelSheafInclusion ≫ E.quotientSheafMap = 0 :=
  squareZero_kernel_quotient_comp_zero E

/-- For a square-zero extension `E` of `𝒪_X`, the sequence `0 ⟶ I ⟶ A ⟶ 𝒪_X ⟶ 0` of sheaves of
abelian groups is short exact. -/
public theorem SquareZeroExtension.kernelSheaf_sequence_shortExact
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    (ShortComplex.mk E.kernelSheafInclusion E.quotientSheafMap
      E.kernel_quotient_comp_zero).ShortExact :=
  squareZero_kernelSheaf_sequence_shortExact E

/-- A section of the extension whose image in the stalk of `𝒪_X` at `x` vanishes restricts, on a
neighbourhood of `x`, to a section of the kernel. -/
private theorem exists_kernel_section_of_germ_eq_zero
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X) {U : X.Opens}
    (hxU : x ∈ U) (a : E.A.presheaf.obj (Opposite.op U))
    (ha : TopCat.Presheaf.germ X.sheaf.obj U x hxU (E.π.hom.app (Opposite.op U) a) = 0) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ (iVU : V ⟶ U) (z : E.I.val.obj (Opposite.op V)),
      E.ι (Opposite.op V) z = E.A.presheaf.map iVU.op a := by
  have ha' : TopCat.Presheaf.germ X.sheaf.obj U x hxU (E.π.hom.app (Opposite.op U) a) =
      TopCat.Presheaf.germ X.sheaf.obj ⊤ x True.intro 0 := by simpa using ha
  obtain ⟨V, hxV, iVU, iVtop, hres⟩ := TopCat.Presheaf.germ_eq X.sheaf.obj
    (U := U) (V := ⊤) x hxU True.intro (E.π.hom.app (Opposite.op U) a) 0 ha'
  obtain ⟨z, hz, -⟩ := E.exact_kernel (Opposite.op V) (E.A.presheaf.map iVU.op a)
    (by simp [hres])
  exact ⟨V, hxV, iVU, z, hz⟩

private theorem squareZero_stalkMap_ker
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X) :
    ∀ r ∈ RingHom.ker
      (((TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom).hom), r ^ 2 = 0 := by
  intro r hr
  obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq E.A.presheaf r
  have hr0 : (((TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom).hom)
      (TopCat.Presheaf.germ E.A.presheaf U x hxU a) = 0 := RingHom.mem_ker.mp hr
  obtain ⟨V, hxV, iVU, z, hz⟩ := exists_kernel_section_of_germ_eq_zero E x hxU a
    (by rwa [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hr0)
  have hgerm : TopCat.Presheaf.germ E.A.presheaf V x hxV (E.ι (Opposite.op V) z) =
      TopCat.Presheaf.germ E.A.presheaf U x hxU a := by
    rw [hz]
    exact TopCat.Presheaf.germ_res_apply E.A.presheaf iVU x hxV a
  have hsq : TopCat.Presheaf.germ E.A.presheaf V x hxV (E.ι (Opposite.op V) z) *
      TopCat.Presheaf.germ E.A.presheaf V x hxV (E.ι (Opposite.op V) z) = 0 := by
    rw [← map_mul, E.square_zero, map_zero]
  rw [← hgerm]
  exact (sq _).trans hsq

theorem squareZero_stalkMap_surjective
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X) :
    Function.Surjective
      (((TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom).hom) :=
  (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks E.π.hom).mp
    E.locallySurjective_π x

theorem squareZero_stalkMap_isLocalHom
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X) :
    IsLocalHom (((TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom).hom) :=
  ⟨fun _ ha => isUnit_of_map_isUnit_of_surjective_squareZero _
    (squareZero_stalkMap_surjective E x) ha (squareZero_stalkMap_ker E x)⟩

theorem squareZero_stalk_kernel_eq_range
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X)
    (a : (TopCat.Presheaf.stalkFunctor CommRingCat x).obj E.A.presheaf) :
    (((TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom).hom a = 0) ↔
      ∃ (U : X.Opens) (hxU : x ∈ U) (z : E.I.val.obj (Opposite.op U)),
        TopCat.Presheaf.germ E.A.presheaf U x hxU (E.ι (Opposite.op U) z) = a := by
  constructor
  · intro ha
    obtain ⟨U, hxU, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq E.A.presheaf a
    obtain ⟨V, hxV, iVU, z, hz⟩ := exists_kernel_section_of_germ_eq_zero E x hxU b
      (by rwa [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ha)
    refine ⟨V, hxV, z, ?_⟩
    rw [hz]
    exact TopCat.Presheaf.germ_res_apply E.A.presheaf iVU x hxV b
  · rintro ⟨U, hxU, z, hza⟩
    rw [← hza, TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change TopCat.Presheaf.germ X.sheaf.obj U x hxU
      ((E.π.hom.app (Opposite.op U)).hom (E.ι (Opposite.op U) z)) = 0
    rw [E.mem_kernel]
    simp

private noncomputable abbrev squareZero_extensionAdditiveSheaf
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :=
  (SheafOfModules.toSheaf
    ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A)).obj
    (SheafOfModules.unit
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A))

private theorem squareZero_kernel_germ_injective
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X)
    {U V : X.Opens} (hxU : x ∈ U) (hxV : x ∈ V)
    (a : E.I.val.obj (Opposite.op U)) (b : E.I.val.obj (Opposite.op V))
    (hab : TopCat.Presheaf.germ (squareZero_extensionAdditiveSheaf E).obj U x hxU
        (E.ι (Opposite.op U) a) =
      TopCat.Presheaf.germ (squareZero_extensionAdditiveSheaf E).obj V x hxV
        (E.ι (Opposite.op V) b)) :
    TopCat.Presheaf.germ
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj U x hxU a =
      TopCat.Presheaf.germ
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj V x hxV b := by
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  let s := E.I.val.map iWU.op a
  let t := E.I.val.map iWV.op b
  have hW : TopCat.Presheaf.germ (squareZero_extensionAdditiveSheaf E).obj W x hxW
      ((squareZero_extensionAdditiveSheaf E).obj.map iWU.op (E.ι (Opposite.op U) a)) =
      TopCat.Presheaf.germ (squareZero_extensionAdditiveSheaf E).obj W x hxW
      ((squareZero_extensionAdditiveSheaf E).obj.map iWV.op (E.ι (Opposite.op V) b)) := by
    calc
      _ = TopCat.Presheaf.germ (squareZero_extensionAdditiveSheaf E).obj U x hxU
            (E.ι (Opposite.op U) a) :=
        TopCat.Presheaf.germ_res_apply (squareZero_extensionAdditiveSheaf E).obj iWU x hxW _
      _ = TopCat.Presheaf.germ (squareZero_extensionAdditiveSheaf E).obj V x hxV
            (E.ι (Opposite.op V) b) := hab
      _ = _ := (TopCat.Presheaf.germ_res_apply
        (squareZero_extensionAdditiveSheaf E).obj iWV x hxW _).symm
  have hs : E.ι (Opposite.op W) s =
      (squareZero_extensionAdditiveSheaf E).obj.map iWU.op (E.ι (Opposite.op U) a) :=
    E.naturality iWU.op a
  have ht : E.ι (Opposite.op W) t =
      (squareZero_extensionAdditiveSheaf E).obj.map iWV.op (E.ι (Opposite.op V) b) :=
    E.naturality iWV.op b
  have hW' : TopCat.Presheaf.germ (squareZero_extensionAdditiveSheaf E).obj W x hxW
      (E.ι (Opposite.op W) s) =
      TopCat.Presheaf.germ (squareZero_extensionAdditiveSheaf E).obj W x hxW
      (E.ι (Opposite.op W) t) := by simpa [hs, ht] using hW
  obtain ⟨T, hxT, iTW, iTtop, hres⟩ :=
    TopCat.Presheaf.germ_eq (squareZero_extensionAdditiveSheaf E).obj
    (U := W) (V := W) x hxW hxW (E.ι (Opposite.op W) s) (E.ι (Opposite.op W) t) hW'
  have hi : iTW = iTtop := Subsingleton.elim _ _
  rw [← hi] at hres
  have hrestrict :
      (squareZero_extensionAdditiveSheaf E).obj.map iTW.op (E.ι (Opposite.op W) s) =
      (squareZero_extensionAdditiveSheaf E).obj.map iTW.op (E.ι (Opposite.op W) t) := hres
  have hsections : E.I.val.map iTW.op s = E.I.val.map iTW.op t := by
    apply squareZero_kernelMap_injective E (Opposite.op T)
    have h₁ : E.ι (Opposite.op T) (E.I.val.map iTW.op s) =
        (squareZero_extensionAdditiveSheaf E).obj.map iTW.op (E.ι (Opposite.op W) s) :=
      E.naturality iTW.op s
    have h₂ : (squareZero_extensionAdditiveSheaf E).obj.map iTW.op
        (E.ι (Opposite.op W) t) = E.ι (Opposite.op T) (E.I.val.map iTW.op t) :=
      (E.naturality iTW.op t).symm
    exact h₁.trans (hrestrict.trans h₂)
  calc
    TopCat.Presheaf.germ
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj U x hxU a =
      TopCat.Presheaf.germ
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj W x hxW s :=
      (TopCat.Presheaf.germ_res_apply
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj iWU x hxW a).symm
    _ = TopCat.Presheaf.germ
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj T x hxT
          (E.I.val.map iTW.op s) :=
      (TopCat.Presheaf.germ_res_apply
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj iTW x hxT s).symm
    _ = TopCat.Presheaf.germ
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj T x hxT
          (E.I.val.map iTW.op t) := by rw [hsections]
    _ = TopCat.Presheaf.germ
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj W x hxW t :=
      (TopCat.Presheaf.germ_res_apply
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj iTW x hxT t)
    _ = TopCat.Presheaf.germ
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj V x hxV b :=
      TopCat.Presheaf.germ_res_apply
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj
        iWV x hxW b

theorem squareZero_stalk_kernel_inclusion_injective
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X) :
    Function.Injective
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (squareZero_kernelSheafInclusion E).hom).hom) := by
  intro a b hab
  obtain ⟨U, hxU, a₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj a
  obtain ⟨V, hxV, b₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj E.I).obj b
  simp only [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hab
  change TopCat.Presheaf.germ (squareZero_extensionAdditiveSheaf E).obj U x hxU
      (E.ι (Opposite.op U) a₀) =
    TopCat.Presheaf.germ (squareZero_extensionAdditiveSheaf E).obj V x hxV
      (E.ι (Opposite.op V) b₀) at hab
  exact squareZero_kernel_germ_injective E x hxU hxV a₀ b₀ hab

def canonicalInclusionSheafedSpace
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    X.toSheafedSpace ⟶ thickenedSpace X E.A :=
  InducedCategory.homMk { base := 𝟙 (X : TopCat), c := E.π.hom }

theorem canonicalInclusionSheafedSpace_eq
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    canonicalInclusionSheafedSpace E = E.inclusion := by
  apply InducedCategory.hom_ext
  apply PresheafedSpace.hext
  · exact E.inclusion_base.symm
  · exact E.inclusion_sheaf.symm

theorem canonicalInclusionSheafedSpace_toBase
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    canonicalInclusionSheafedSpace E ≫ E.toBase = f.toLRSHom.toShHom := by
  rw [canonicalInclusionSheafedSpace_eq]
  exact E.over_base

private theorem canonicalInclusionSheafedSpace_stalkMap
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X) :
    (canonicalInclusionSheafedSpace E).hom.stalkMap x =
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom := by
  change (TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom ≫
      TopCat.Presheaf.stalkPushforward CommRingCat (𝟙 (X : TopCat)) X.presheaf x =
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom
  rw [TopCat.Presheaf.stalkPushforward.id]
  change (TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (TopCat.Presheaf.Pushforward.id X.presheaf).hom =
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom
  refine Eq.trans ((TopCat.Presheaf.stalkFunctor CommRingCat x).map_comp
    E.π.hom (TopCat.Presheaf.Pushforward.id X.presheaf).hom).symm ?_
  congr 1

theorem canonicalInclusionSheafedSpace_stalkMap_isLocalHom
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X) :
    IsLocalHom (((canonicalInclusionSheafedSpace E).hom.stalkMap x).hom) := by
  rw [canonicalInclusionSheafedSpace_stalkMap]
  exact squareZero_stalkMap_isLocalHom E x

noncomputable def thickenedLocallyRingedSpace
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    LocallyRingedSpace.{u} :=
  { toSheafedSpace := thickenedSpace X E.A
    isLocalRing := fun x => by
      let hsurj : Function.Surjective
          (((TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom).hom) :=
        squareZero_stalkMap_surjective E x
      let : IsLocalRing
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.sheaf.obj) :=
        X.toLocallyRingedSpace.isLocalRing x
      exact isLocalRing_of_surjective_squareZero
        (((TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom).hom) hsurj
        (squareZero_stalkMap_ker E x) }

noncomputable def canonicalInclusionLocallyRingedSpace
  {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    X.toLocallyRingedSpace ⟶ thickenedLocallyRingedSpace E :=
  LocallyRingedSpace.homMk (canonicalInclusionSheafedSpace E)
    (canonicalInclusionSheafedSpace_stalkMap_isLocalHom E)

theorem canonicalInclusionLocallyRingedSpace_stalkMap
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X) :
    (canonicalInclusionLocallyRingedSpace E).stalkMap x =
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom := by
  change (canonicalInclusionSheafedSpace E).hom.stalkMap x = _
  exact canonicalInclusionSheafedSpace_stalkMap E x

end Stacks.Thickenings
