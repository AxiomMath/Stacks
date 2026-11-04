module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DistinguishedTriangle
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomShift
public import StacksCore.Tactic.StacksAttribute

/-! # The internal hom functor is exact

Let `A` and `B` be differential graded algebras over a commutative ring `R` and let `N` be a
right differential graded `B`-module with a compatible left differential graded `A`-action. The
internal hom functor `Hom^•_B(N, -)` of Tag 0FQQ is a functor of differential graded categories,
so it preserves all the data an admissible short exact sequence consists of: the splittings of
such a sequence are morphisms of the underlying *graded* category, which a differential graded
functor acts on just as it acts on the closed morphisms, and the identities they satisfy are
identities of composites. The image sequence is therefore again admissible short exact, with the
postcomposed splittings, and its connecting morphism is the image of the original one.

This is the general principle of Tag 0FQF in the case needed for Tag 09LH: it is exactly what
makes `Hom^•_B(N, -)` an exact functor of the homotopy categories, because the distinguished
triangles of `K(Mod_(B, d))` are the triangles attached to admissible short exact sequences
(Tag 09K8) and the connecting morphism is what their third arrow is built from.

## Main definitions

* `DifferentialGradedModule.GradedHom.toHomogeneousMap`: a graded homomorphism read as a
  degree-zero homogeneous map.
* `DifferentialGradedModule.homPostcompHom` and
  `DifferentialGradedModule.homPostcompGradedHom`: the action of the internal hom functor on a
  homomorphism and on a graded homomorphism, by postcomposition.

## Main results

* `DifferentialGradedModule.isAdmissibleShortExact_homPostcomp`: the image of an admissible
  short exact sequence is an admissible short exact sequence.
* `DifferentialGradedModule.compatibleSplittings_homPostcomp`: the postcomposed splittings are
  compatible splittings of the image sequence.

## Implementation notes

The whole proof is the five axioms of a differential graded functor applied to five identities
between composites of the four morphisms `f`, `g`, `s`, `π` of a split sequence, so it is
carried out on homogeneous maps rather than on homomorphisms: the key point, and the reason this
is cheap, is that the differential graded functor of Tag 0FQQ acts on the chosen presentations
of Tag 0FQR *by definition* as `DifferentialGradedModule.homPostcompHomogeneousMap`, so its
`map_comp`, `map_add`, `map_id` and `map_d` are available directly.

The splitting identity `f π + s g = 1` is not a field of
`DifferentialGradedModule.CompatibleSplittings` — which records `ker π = range s` instead — so it
is derived here as `DifferentialGradedModule.CompatibleSplittings.comp_add_comp`, by the same
argument that `DifferentialGradedModule.connectingHom` uses internally.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
* [Stacks Project, Tag 09LH](https://stacks.math.columbia.edu/tag/09LH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- A graded homomorphism of differential graded modules, read as a homogeneous map of
degree zero. -/
def GradedHom.toHomogeneousMap {X Y : DifferentialGradedModule B} (u : GradedHom X Y) :
    HomogeneousMap B X Y 0 :=
  ⟨u.toFun, fun i x hx => by simpa using u.map_grading i x hx, fun a x => u.map_smul x a⟩

/-- The homogeneous map of a graded homomorphism has the same underlying linear map. -/
@[simp] theorem GradedHom.toHomogeneousMap_val {X Y : DifferentialGradedModule B}
    (u : GradedHom X Y) : (u.toHomogeneousMap).1 = u.toFun := rfl

/-- In an admissible short exact sequence, the composite `g ∘ f` is zero. -/
private theorem comp_eq_zero_of_isAdmissibleShortExact {X Y Z : DifferentialGradedModule B}
    {f : Hom X Y} {g : Hom Y Z} (hfg : IsAdmissibleShortExact f g) (x : X.M) :
    g.toFun (f.toFun x) = 0 :=
  LinearMap.mem_ker.mp (hfg.exact ▸ (⟨x, rfl⟩ : f.toFun x ∈ LinearMap.range f.toFun))

namespace CompatibleSplittings

variable {X Y Z : DifferentialGradedModule B} {f : Hom X Y} {g : Hom Y Z}

/-- A compatible pair of graded splittings kills the section with the retraction. -/
theorem comp_eq_zero (c : CompatibleSplittings B f g) (x : Z.M) :
    c.π.toFun (c.s.toFun x) = 0 :=
  LinearMap.mem_ker.mp (c.hker ▸ (⟨x, rfl⟩ : c.s.toFun x ∈ LinearMap.range c.s.toFun))

/-- The splitting identity `f π + s g = 1`, which `CompatibleSplittings` records in the
equivalent form `ker π = range s`. -/
theorem comp_add_comp (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings B f g)
    (y : Y.M) : f.toFun (c.π.toFun y) + c.s.toFun (g.toFun y) = y := by
  have hmem : y - c.s.toFun (g.toFun y) ∈ LinearMap.range f.toFun := by
    rw [hfg.exact, LinearMap.mem_ker]
    simp [map_sub, c.hs]
  obtain ⟨z, hz⟩ := hmem
  have hzπ : z = c.π.toFun y := by
    rw [← c.hπ z, hz, map_sub, comp_eq_zero c, sub_zero]
  rw [← hzπ, hz]
  abel

end CompatibleSplittings

variable (A B) (N : DifferentialGradedModule B) (L : BimoduleStructure A B N)

/-- The internal hom functor of `N`, as a differential graded functor acting on the chosen
presentations. -/
abbrev homDGFunctor : DGCategory.DGFunctor (dgCategory B) (dgCategory A) :=
  (homDGFunctorData A B N L).functor

/-- Postcomposition with a homogeneous map, as a linear map between the chosen presentations.
This is the action of the internal hom functor on morphisms of the underlying graded
categories. -/
abbrev homPostcompMap {X Y : DifferentialGradedModule B} {n : ℤ} (u : HomogeneousMap B X Y n) :
    (homModulePresentation A B N L X).module.M →ₗ[R]
      (homModulePresentation A B N L Y).module.M :=
  ((homDGFunctor A B N L).map u).1

/-- Postcomposition with a composite is the composite of the postcompositions. -/
theorem homPostcompMap_comp {X Y Z : DifferentialGradedModule B} {m n k : ℤ}
    (h : m + n = k) (v : HomogeneousMap B Y Z m) (u : HomogeneousMap B X Y n) :
    homPostcompMap A B N L (homogeneousMapComp B h v u) =
      (homPostcompMap A B N L v).comp (homPostcompMap A B N L u) :=
  congrArg Subtype.val ((homDGFunctor A B N L).map_comp h v u)

/-- Postcomposition with the identity is the identity. -/
theorem homPostcompMap_id (X : DifferentialGradedModule B) :
    homPostcompMap A B N L (homogeneousMapId B X) = LinearMap.id :=
  congrArg Subtype.val ((homDGFunctor A B N L).map_id X)

/-- Postcomposition is additive in the homogeneous map. -/
theorem homPostcompMap_add {X Y : DifferentialGradedModule B} {n : ℤ}
    (u v : HomogeneousMap B X Y n) :
    homPostcompMap A B N L (u + v) =
      homPostcompMap A B N L u + homPostcompMap A B N L v :=
  congrArg Subtype.val ((homDGFunctor A B N L).map_add u v)

/-- Postcomposition with zero is zero. -/
theorem homPostcompMap_zero {X Y : DifferentialGradedModule B} {n : ℤ} :
    homPostcompMap A B N L (0 : HomogeneousMap B X Y n) = 0 :=
  congrArg Subtype.val (homDGFunctor A B N L).map_zero

/-- Equal homogeneous maps have equal postcompositions, pointwise. -/
private theorem homPostcompMap_apply_congr {X Y : DifferentialGradedModule B} {n : ℤ}
    {u v : HomogeneousMap B X Y n} (h : u = v)
    (x : (homModulePresentation A B N L X).module.M) :
    homPostcompMap A B N L u x = homPostcompMap A B N L v x :=
  h ▸ rfl

/-- The action of the internal hom functor on a homomorphism of differential graded modules. -/
def homPostcompHom {X Y : DifferentialGradedModule B} (u : Hom X Y) :
    (homModulePresentation A B N L X).module ⟶ (homModulePresentation A B N L Y).module :=
  homOfCocycle A ((homDGFunctor A B N L).mapCocycle (cocycleOfHom B u))

/-- The underlying linear map of `homPostcompHom` is postcomposition with the cocycle of the
homomorphism. -/
@[simp] theorem homPostcompHom_toFun {X Y : DifferentialGradedModule B} (u : Hom X Y) :
    (homPostcompHom A B N L u).toFun = homPostcompMap A B N L (cocycleOfHom B u).1 := rfl

/-- The action of the internal hom functor on a graded homomorphism of differential graded
modules. -/
def homPostcompGradedHom {X Y : DifferentialGradedModule B} (u : GradedHom X Y) :
    GradedHom (homModulePresentation A B N L X).module
      (homModulePresentation A B N L Y).module :=
  { toFun := homPostcompMap A B N L u.toHomogeneousMap
    map_smul := fun x a => ((homDGFunctor A B N L).map u.toHomogeneousMap).2.2 a x
    map_grading := fun i x hx => by
      have h : homPostcompMap A B N L u.toHomogeneousMap x ∈
          (homModulePresentation A B N L Y).module.grading (i + 0) :=
        ((homDGFunctor A B N L).map u.toHomogeneousMap).2.1 i x hx
      rwa [add_zero] at h }

/-- The underlying linear map of `homPostcompGradedHom` is postcomposition with the associated
homogeneous map. -/
@[simp] theorem homPostcompGradedHom_toFun {X Y : DifferentialGradedModule B}
    (u : GradedHom X Y) :
    (homPostcompGradedHom A B N L u).toFun = homPostcompMap A B N L u.toHomogeneousMap := rfl

section

variable {X Y Z : DifferentialGradedModule B} {f : Hom X Y} {g : Hom Y Z}
  (c : CompatibleSplittings B f g)

include c

/-- The postcomposed retraction is a retraction of the postcomposed inclusion. -/
theorem homPostcomp_retraction (x : (homModulePresentation A B N L X).module.M) :
    (homPostcompGradedHom A B N L c.π).toFun ((homPostcompHom A B N L f).toFun x) = x := by
  have key : homogeneousMapComp B (add_zero (0 : ℤ)) c.π.toHomogeneousMap
      (cocycleOfHom B f).1 = homogeneousMapId B X :=
    Subtype.ext (LinearMap.ext fun x => c.hπ x)
  simpa [homPostcompMap_comp, homPostcompMap_id] using
    homPostcompMap_apply_congr A B N L key x

/-- The postcomposed section is a section of the postcomposed projection. -/
theorem homPostcomp_section (x : (homModulePresentation A B N L Z).module.M) :
    (homPostcompHom A B N L g).toFun ((homPostcompGradedHom A B N L c.s).toFun x) = x := by
  have key : homogeneousMapComp B (add_zero (0 : ℤ)) (cocycleOfHom B g).1
      c.s.toHomogeneousMap = homogeneousMapId B Z :=
    Subtype.ext (LinearMap.ext fun x => c.hs x)
  simpa [homPostcompMap_comp, homPostcompMap_id] using
    homPostcompMap_apply_congr A B N L key x

/-- The postcomposed retraction kills the postcomposed section. -/
theorem homPostcomp_retraction_section (x : (homModulePresentation A B N L Z).module.M) :
    (homPostcompGradedHom A B N L c.π).toFun
      ((homPostcompGradedHom A B N L c.s).toFun x) = 0 := by
  have key : homogeneousMapComp B (add_zero (0 : ℤ)) c.π.toHomogeneousMap
      c.s.toHomogeneousMap = 0 :=
    Subtype.ext (LinearMap.ext fun x => c.comp_eq_zero x)
  simpa [homPostcompMap_comp, homPostcompMap_zero] using
    homPostcompMap_apply_congr A B N L key x

omit c in
/-- The postcomposed sequence is a complex. -/
theorem homPostcomp_comp_eq_zero (hfg : IsAdmissibleShortExact f g)
    (x : (homModulePresentation A B N L X).module.M) :
    (homPostcompHom A B N L g).toFun ((homPostcompHom A B N L f).toFun x) = 0 := by
  have key : homogeneousMapComp B (add_zero (0 : ℤ)) (cocycleOfHom B g).1
      (cocycleOfHom B f).1 = 0 :=
    Subtype.ext (LinearMap.ext (comp_eq_zero_of_isAdmissibleShortExact hfg))
  simpa [homPostcompMap_comp, homPostcompMap_zero] using
    homPostcompMap_apply_congr A B N L key x

/-- The splitting identity for the postcomposed sequence. -/
theorem homPostcomp_split (hfg : IsAdmissibleShortExact f g)
    (y : (homModulePresentation A B N L Y).module.M) :
    (homPostcompHom A B N L f).toFun ((homPostcompGradedHom A B N L c.π).toFun y) +
        (homPostcompGradedHom A B N L c.s).toFun
          ((homPostcompHom A B N L g).toFun y) = y := by
  have key : homogeneousMapComp B (add_zero (0 : ℤ)) (cocycleOfHom B f).1
        c.π.toHomogeneousMap +
      homogeneousMapComp B (add_zero (0 : ℤ)) c.s.toHomogeneousMap
        (cocycleOfHom B g).1 = homogeneousMapId B Y :=
    Subtype.ext (LinearMap.ext fun y => c.comp_add_comp hfg y)
  simpa [homPostcompMap_add, homPostcompMap_comp, homPostcompMap_id] using
    homPostcompMap_apply_congr A B N L key y

/-- **Stacks 0FQF**, for the internal hom functor of a differential graded bimodule. The functor
`Hom^•_B(N, -)` carries an admissible short exact sequence of right differential graded
`B`-modules to an admissible short exact sequence of right differential graded `A`-modules. -/
theorem isAdmissibleShortExact_homPostcomp (hfg : IsAdmissibleShortExact f g) :
    IsAdmissibleShortExact (homPostcompHom A B N L f) (homPostcompHom A B N L g) where
  injective := by
    intro x y hxy
    rw [← homPostcomp_retraction A B N L c x, ← homPostcomp_retraction A B N L c y]
    exact congrArg _ hxy
  surjective := fun z =>
    ⟨(homPostcompGradedHom A B N L c.s).toFun z, homPostcomp_section A B N L c z⟩
  exact := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact LinearMap.mem_ker.mpr (homPostcomp_comp_eq_zero A B N L hfg x)
    · intro y hy
      refine ⟨(homPostcompGradedHom A B N L c.π).toFun y, ?_⟩
      have h := homPostcomp_split A B N L c hfg y
      rwa [LinearMap.mem_ker.mp hy, map_zero, add_zero] at h
  admissibleMono :=
    ⟨homPostcompGradedHom A B N L c.π, homPostcomp_retraction A B N L c⟩
  admissibleEpi :=
    ⟨homPostcompGradedHom A B N L c.s, homPostcomp_section A B N L c⟩

/-- The postcomposed splittings are compatible splittings of the image sequence. -/
def compatibleSplittings_homPostcomp (hfg : IsAdmissibleShortExact f g) :
    CompatibleSplittings A (homPostcompHom A B N L f) (homPostcompHom A B N L g) where
  s := homPostcompGradedHom A B N L c.s
  π := homPostcompGradedHom A B N L c.π
  hs := homPostcomp_section A B N L c
  hπ := homPostcomp_retraction A B N L c
  hker := by
    apply le_antisymm
    · intro y hy
      refine ⟨(homPostcompHom A B N L g).toFun y, ?_⟩
      have h := homPostcomp_split A B N L c hfg y
      rwa [LinearMap.mem_ker.mp hy, map_zero, zero_add] at h
    · rintro y ⟨z, rfl⟩
      exact LinearMap.mem_ker.mpr (homPostcomp_retraction_section A B N L c z)

end

end DifferentialGradedModule

end
