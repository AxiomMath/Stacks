module

public import StacksFrontier.Topology.Sheaves.Modules.Differentials
import StacksCore.Tactic.StacksAttribute

/-!
# Sections of a square-zero extension and relative derivations

Let `π : A ⟶ O` be a surjection of sheaves of commutative rings over a base sheaf `B`, whose
kernel `I` has square zero, and fix one section `s` of `π` over `B`. Stacks 01UP says that the
other sections over `B` are then in bijection with the relative derivations `O ⟶ I` over `B`,
the bijection sending a section `t` to the derivation `t - s`.

Both directions are the computation the statement suggests. For a section `t`, the difference
`t - s` lands in the kernel of `π`, hence comes from a unique section of `I`; the Leibniz rule
for the resulting map follows from expanding `(t a - s a)(t b - s b) = 0`, which is the
square-zero hypothesis. Conversely, for a derivation `D` the map `a ↦ s a + D a` is a ring
homomorphism precisely because `D` satisfies the Leibniz rule and `I² = 0`, and it is a
section over `B` because `D` kills the image of `B`. The two constructions are inverse by
injectivity of the inclusion of the kernel.

## Main definitions

* `Stacks.Sheaves.SquareZeroExtension.AlgebraSection`: a section of a morphism of sheaves of
  rings, as a morphism over a fixed base sheaf.
* `Stacks.Sheaves.SquareZeroExtension.SquareZeroKernel`: the datum realizing a sheaf of
  `O`-modules as the square-zero kernel of such a morphism, with the module action induced by
  a chosen section.

## Main results

* `Stacks.Sheaves.SquareZeroExtension.sectionsEquivDerivations`: **Tag 01UP**, the sections
  are in bijection with the relative derivations into the kernel, and the derivation attached
  to `t` is the pointwise difference `t - s`.

## Implementation notes

The morphism of ringed spaces is represented on a fixed topological space by the map from the
pulled-back structure sheaf `B` to `O`. The kernel is supplied as a sheaf of `O`-modules
together with its pointwise identification with the kernel in `A`, which makes the module
structure and the square-zero hypothesis explicit rather than derived from a categorical
kernel. The displayed formula for the bijection expresses at once the construction `s + D`,
its uniqueness, and compatibility with restriction maps.

## References

* [Stacks Project, Tag 01UP](https://stacks.math.columbia.edu/tag/01UP)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM), relative derivations
  of sheaves.
-/

@[expose] public section

open CategoryTheory PresheafOfModules TopologicalSpace
open AlgebraicGeometry.SheafOfModules (underlyingRingSheaf SheafDerivation)

universe u v w

namespace Stacks.Sheaves.SquareZeroExtension

/-- A section of `π : A ⟶ O` as a morphism of sheaves of rings over the base sheaf `B`. -/
structure AlgebraSection {X : TopCat.{u}}
    {B O A : TopCat.Sheaf CommRingCat.{max u v} X}
    (α : B ⟶ O) (β : B ⟶ A) (π : A ⟶ O) where
  /-- The underlying morphism of sheaves of rings. -/
  hom : O ⟶ A
  /-- The morphism is a section of `π`. -/
  right_inv : hom ≫ π = 𝟙 O
  /-- The section is a morphism over the base sheaf `B`. -/
  over : α ≫ hom = β

/-- A realization of a sheaf of `O`-modules as the square-zero kernel of `π : A ⟶ O`. The
scalar action is the natural one induced by a section `s`: an element of `O` acts through its
lift under `s`. -/
structure SquareZeroKernel {X : TopCat.{u}}
    {B O A : TopCat.Sheaf CommRingCat.{max u v} X}
    (α : B ⟶ O) (β : B ⟶ A) (π : A ⟶ O)
    (s : AlgebraSection α β π)
    (I : SheafOfModules.{max u v w} (underlyingRingSheaf O)) where
  /-- The inclusion of the kernel on every open set. -/
  ι (U : (Opens X)ᵒᵖ) : I.val.obj U →+ A.obj.obj U
  /-- The inclusions commute with restriction maps. -/
  naturality {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (x : I.val.obj U) :
    ι V (I.val.map f x) = A.obj.map f (ι U x)
  /-- The `O`-module action on the kernel is multiplication by the lift under the chosen
  section. -/
  map_smul (U : (Opens X)ᵒᵖ) (a : (underlyingRingSheaf O).obj.obj U)
      (x : I.val.obj U) :
    ι U (a • x) = s.hom.hom.app U a * ι U x
  /-- Every element of `I` maps into the kernel of `π`. -/
  mem_kernel (U : (Opens X)ᵒᵖ) (x : I.val.obj U) :
    π.hom.app U (ι U x) = 0
  /-- Every element in the kernel of `π` comes from a unique element of `I`. -/
  existsUnique_of_mem_kernel (U : (Opens X)ᵒᵖ) (a : A.obj.obj U)
      (ha : π.hom.app U a = 0) :
    ∃! x, ι U x = a
  /-- The kernel ideal has square zero. -/
  mul_ι (U : (Opens X)ᵒᵖ) (x y : I.val.obj U) :
    ι U x * ι U y = 0

section

variable {X : TopCat.{u}} {B O A : TopCat.Sheaf CommRingCat.{max u v} X}
  {α : B ⟶ O} {β : B ⟶ A} {π : A ⟶ O} {s : AlgebraSection α β π}
  {I : SheafOfModules.{max u v w} (underlyingRingSheaf O)}

private lemma section_apply (t : AlgebraSection α β π) (U : (Opens X)ᵒᵖ)
    (a : O.obj.obj U) : π.hom.app U (t.hom.hom.app U a) = a :=
  congrArg (fun q ↦ q.hom.app U a) t.right_inv

private lemma section_over_apply (t : AlgebraSection α β π) (U : (Opens X)ᵒᵖ)
    (a : B.obj.obj U) : t.hom.hom.app U (α.hom.app U a) = β.hom.app U a :=
  congrArg (fun q ↦ q.hom.app U a) t.over

private lemma section_ext (t t' : AlgebraSection α β π) (h : t.hom = t'.hom) : t = t' := by
  cases t
  cases t'
  cases h
  rfl

variable (hI : SquareZeroKernel α β π s I)

private lemma kernel_injective (U : (Opens X)ᵒᵖ) : Function.Injective (hI.ι U) :=
  fun x _ hxy ↦ (hI.existsUnique_of_mem_kernel U (hI.ι U x) (hI.mem_kernel U x)).unique rfl hxy.symm

private lemma difference_mem_kernel (t : AlgebraSection α β π) (U : (Opens X)ᵒᵖ)
    (a : O.obj.obj U) :
    π.hom.app U (t.hom.hom.app U a - s.hom.hom.app U a) = 0 := by
  rw [map_sub, section_apply, section_apply, sub_self]

/-- The action of two elements of `O` on two elements of `I`, computed in `A`. -/
private lemma ι_smul_add_smul (U : (Opens X)ᵒᵖ) (a b : O.obj.obj U) (x y : I.val.obj U) :
    hI.ι U ((show (underlyingRingSheaf O).obj.obj U from a) • x +
      (show (underlyingRingSheaf O).obj.obj U from b) • y) =
      s.hom.hom.app U a * hI.ι U x + s.hom.hom.app U b * hI.ι U y := by
  rw [map_add, hI.map_smul, hI.map_smul]

/-- The unique section of `I` over `U` whose image in `A` is `t a - s a`. -/
private noncomputable def sectionDifference (t : AlgebraSection α β π) (U : (Opens X)ᵒᵖ)
    (a : O.obj.obj U) : I.val.obj U :=
  Classical.choose (hI.existsUnique_of_mem_kernel U
    (t.hom.hom.app U a - s.hom.hom.app U a) (difference_mem_kernel t U a))

private lemma sectionDifference_spec (t : AlgebraSection α β π) (U : (Opens X)ᵒᵖ)
    (a : O.obj.obj U) :
    hI.ι U (sectionDifference hI t U a) = t.hom.hom.app U a - s.hom.hom.app U a :=
  (Classical.choose_spec (hI.existsUnique_of_mem_kernel U
    (t.hom.hom.app U a - s.hom.hom.app U a) (difference_mem_kernel t U a))).1

/-- The derivation `t - s` attached to a section `t`. -/
private noncomputable def sectionDerivation (t : AlgebraSection α β π) : SheafDerivation α I :=
  { d :=
      { toFun := sectionDifference hI t _
        map_zero' := by
          apply kernel_injective hI
          simp [sectionDifference_spec]
        map_add' := by
          intro a b
          apply kernel_injective hI
          simp only [map_add, sectionDifference_spec]
          abel }
    d_mul := by
      intro U a b
      apply kernel_injective hI
      erw [ι_smul_add_smul, sectionDifference_spec, sectionDifference_spec,
        sectionDifference_spec]
      simp only [map_mul]
      have hz := hI.mul_ι U (sectionDifference hI t U a) (sectionDifference hI t U b)
      rw [sectionDifference_spec, sectionDifference_spec] at hz
      calc
        _ = s.hom.hom.app U a * (t.hom.hom.app U b - s.hom.hom.app U b) +
            s.hom.hom.app U b * (t.hom.hom.app U a - s.hom.hom.app U a) +
            (t.hom.hom.app U a - s.hom.hom.app U a) *
            (t.hom.hom.app U b - s.hom.hom.app U b) := by ring
        _ = _ := by rw [hz, add_zero]
    d_map := by
      intro U V f a
      apply kernel_injective hI
      change hI.ι V (sectionDifference hI t V (O.obj.map f a)) =
        hI.ι V (I.val.map f (sectionDifference hI t U a))
      rw [sectionDifference_spec, hI.naturality, sectionDifference_spec]
      simp
    d_app := by
      intro U a
      apply kernel_injective hI
      change hI.ι U (sectionDifference hI t U (α.hom.app U a)) = hI.ι U 0
      rw [sectionDifference_spec, section_over_apply, section_over_apply, sub_self, map_zero] }

/-- The ring homomorphism `a ↦ s a + D a` attached to a derivation `D`. -/
private def derivationRingHom (D : SheafDerivation α I) (U : (Opens X)ᵒᵖ) :
    O.obj.obj U →+* A.obj.obj U :=
  { toFun := fun a ↦ s.hom.hom.app U a + hI.ι U (D.d a)
    map_one' := by simp [D.d_one]
    map_zero' := by simp
    map_add' := by
      intro a b
      simp only [map_add]
      abel
    map_mul' := by
      intro a b
      change s.hom.hom.app U (a * b) + hI.ι U (D.d (a * b)) = _
      erw [D.d_mul, ι_smul_add_smul]
      simp only [map_mul]
      calc
        _ = _ + hI.ι U (D.d a) * hI.ι U (D.d b) := by
          rw [hI.mul_ι, add_zero]
        _ = _ := by ring }

/-- The section `s + D` attached to a derivation `D`. -/
private def derivationSection (D : SheafDerivation α I) : AlgebraSection α β π :=
  { hom := ObjectProperty.homMk
      { app := fun U ↦ CommRingCat.ofHom (derivationRingHom hI D U)
        naturality := by
          intro U V f
          ext a
          change s.hom.hom.app V (O.obj.map f a) + hI.ι V (D.d (O.obj.map f a)) =
            A.obj.map f (s.hom.hom.app U a + hI.ι U (D.d a))
          have hd : D.d (O.obj.map f a) = I.val.map f (D.d a) := D.d_map f a
          have hs : s.hom.hom.app V (O.obj.map f a) =
              A.obj.map f (s.hom.hom.app U a) :=
            congrArg (fun q ↦ q a) (s.hom.hom.naturality f)
          rw [hd, hI.naturality, map_add, hs] }
    right_inv := by
      apply ObjectProperty.hom_ext _
      ext U a
      change π.hom.app U (s.hom.hom.app U a + hI.ι U (D.d a)) = a
      rw [map_add, hI.mem_kernel, add_zero, section_apply]
    over := by
      apply ObjectProperty.hom_ext _
      ext U a
      change s.hom.hom.app U (α.hom.app U a) + hI.ι U (D.d (α.hom.app U a)) =
        β.hom.app U a
      rw [D.d_app, map_zero, add_zero, section_over_apply] }

private lemma derivationSection_sectionDerivation (t : AlgebraSection α β π) :
    derivationSection hI (sectionDerivation hI t) = t := by
  apply section_ext
  apply ObjectProperty.hom_ext _
  ext U a
  change s.hom.hom.app U a + hI.ι U (sectionDifference hI t U a) = t.hom.hom.app U a
  rw [sectionDifference_spec]
  abel

private lemma sectionDerivation_derivationSection (D : SheafDerivation α I) :
    sectionDerivation hI (derivationSection hI D) = D := by
  ext U a
  apply kernel_injective hI
  change hI.ι U (sectionDifference hI (derivationSection hI D) U a) = hI.ι U (D.d a)
  rw [sectionDifference_spec]
  change s.hom.hom.app U a + hI.ι U (D.d a) - s.hom.hom.app U a = hI.ι U (D.d a)
  abel

end

/-- **Stacks 01UP.** Relative derivations into the square-zero kernel act simply transitively
on the algebra sections of the extension. Under the resulting bijection, the derivation
corresponding to `t` is the pointwise difference `t - s`. -/
@[stacks 01UP]
theorem sectionsEquivDerivations {X : TopCat.{u}}
    {B O A : TopCat.Sheaf CommRingCat.{max u v} X}
    (α : B ⟶ O) (β : B ⟶ A) (π : A ⟶ O)
    (s : AlgebraSection α β π)
    (I : SheafOfModules.{max u v w} (underlyingRingSheaf O))
    (hI : SquareZeroKernel α β π s I) :
    ∃ e : AlgebraSection α β π ≃ SheafDerivation α I,
      ∀ (t : AlgebraSection α β π) (U : (Opens X)ᵒᵖ) (a : O.obj.obj U),
        hI.ι U ((e t).d a) = t.hom.hom.app U a - s.hom.hom.app U a :=
  ⟨{ toFun := sectionDerivation hI
     invFun := derivationSection hI
     left_inv := derivationSection_sectionDerivation hI
     right_inv := sectionDerivation_derivationSection hI },
    fun t U a ↦ sectionDifference_spec hI t U a⟩

end Stacks.Sheaves.SquareZeroExtension

end
