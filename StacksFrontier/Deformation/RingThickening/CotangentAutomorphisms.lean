module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Preadditive.CompAddCompAssoc
public import StacksFrontier.Cotangent.Complex
public import StacksFrontier.Cotangent.HomologyZero
public import StacksFrontier.Deformation.RingThickening.FittingMapTorsor
public import StacksFrontier.Deformation.SquareZero.Torsor
import StacksCore.Tactic.StacksAttribute

/-!
# Automorphisms of a square-zero deformation and the cotangent complex

Let `A' → A` be a surjection of commutative rings with square-zero kernel `I`, let `A → B` be a
ring map, let `N` be a `B`-module and let `c : I → N` be `A`-linear; let `B'` be a solution of
the resulting extension problem. This file identifies the automorphisms of `B'` which induce the
identity on `B` and on `N` with `Ext⁰_B(L_{B/A}, N)`.

The identification is an isomorphism of groups, and it is pinned down on elements: the
automorphism `f` goes to the class whose associated differential map sends `d (b' mod N)` to
`f(b') - b'`, read through the identification `H⁰(L_{B/A}) = Ω_{B/A}` of Tag 08QF.

## Main definitions

* `Stacks.Deformation.SquareZeroExtensionProblem.liftedCotangentComplex`: `L_{B/A}` with
  its terms moved into a single module universe.
* `Stacks.Deformation.SquareZeroExtensionProblem.cotangentExt`: `Ext^i_B(L_{B/A}, N)`.
* `Stacks.Deformation.SquareZeroExtensionProblem.cotangentExtZeroToHom`: the comparison
  of `Ext⁰_B(L_{B/A}, N)` with `Hom_B(Ω_{B/A}, N)`, given by taking degree-zero homology.
* `Stacks.Deformation.SquareZeroExtensionProblem.cotangentExtZeroAddEquiv`: that
  comparison, which is an isomorphism of additive groups.
* `Stacks.Deformation.SquareZeroExtensionProblem.isoOfRingHom`: a ring endomorphism of a
  solution inducing the identity on `B` and on `N` is an automorphism of the solution.

## Main results

* `Stacks.Deformation.SquareZeroExtensionProblem.cotangentExtZeroToHom_bijective`: the
  comparison above is bijective.
* `Stacks.Deformation.SquareZeroExtensionProblem.isoFittingMapEquiv`: automorphisms of a
  solution are the maps filling the diagram comparing the problem with itself.
* `Stacks.Deformation.SquareZeroExtensionProblem.automorphismsExtEquiv`: **Stacks 08SP**,
  part (3) — the automorphisms of a solution fitting into the extension diagram are canonically
  `Ext⁰_B(L_{B/A}, N)`, compatibly with the group laws and with the explicit description of the
  associated differential map.

## Implementation notes

The group of automorphisms is `SquareZeroExtensionProblem.CompatibleExtension.Iso X X`, whose
group law is composition of isomorphisms; no second group structure is put on that type. The
main statement instead bundles the equivalence with the two equations saying that it carries the
identity to `0` and composition to addition, so the conclusion is an isomorphism of groups
without `Iso X X` having to carry a group instance.

An automorphism of `X` is the same thing as a map filling the diagram which compares the problem
with itself (`isoFittingMapEquiv`); those maps form a torsor under `Hom_B(Ω_{B/A}, N)` by Tag
08S5, with the identity automorphism as base point, and that is why the identity goes to `0`.

`Ext⁰` is formed in the derived category of `ModuleCat.{max u₂ v u₄} B`, so both `L_{B/A}`, whose
terms lie in the universe of `B`, and `N` are moved there by `ModuleCat.uliftFunctor`. The
comparison `cotangentExtZeroToHom` is bijective because `L_{B/A}` is concentrated in
non-positive degrees and `N` sits in degree `0`, which is the case `a = b = 0` of Tag 06XS.

## References

* [Stacks Project, Tag 08SP](https://stacks.math.columbia.edu/tag/08SP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ v w

namespace CategoryTheory

namespace Functor

/-- The morphism induced on shifted functors by a morphism into a shift is additive in that
morphism. -/
theorem shiftMap_add {C A M : Type*} [Category C] [Category A] [Preadditive C]
    [Preadditive A] [AddMonoid M] [HasShift C M] (F : C ⥤ A) [F.ShiftSequence M]
    [∀ a : M, (F.shift a).Additive] {X Y : C} {n : M} (f g : X ⟶ Y⟦n⟧) (a a' : M)
    (ha' : n + a = a') :
    F.shiftMap (f + g) a a' ha' = F.shiftMap f a a' ha' + F.shiftMap g a a' ha' := by
  simp only [Functor.shiftMap, Functor.map_add, Preadditive.add_comp]

end Functor

end CategoryTheory

namespace Stacks.Deformation

/-- Two maps filling a compatible square-zero deformation diagram agree as soon as their
underlying ring maps do: their remaining data are proofs. -/
theorem CompatibleSquareZeroDeformationDiagram.FittingMap.ext'
    {D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄, v₁, v₂, v₃, v₄, w₁, w₂}}
    {p q : D.FittingMap} (h : p.toRingHom = q.toRingHom) : p = q := by
  obtain ⟨p, hp₁, hp₂, hp₃⟩ := p
  obtain ⟨q, hq₁, hq₂, hq₃⟩ := q
  subst h
  rfl

namespace SquareZeroExtensionProblem

/-- Two isomorphisms of solutions of a square-zero extension problem agree as soon as their
underlying algebra equivalences agree pointwise: their remaining data are proofs. -/
theorem CompatibleExtension.Iso.ext' {S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄}}
    {X Y : S.CompatibleExtension.{w₁}} {f g : CompatibleExtension.Iso X Y}
    (h : ∀ x, f.toAlgEquiv x = g.toAlgEquiv x) : f = g := by
  obtain ⟨f, hf₁, hf₂⟩ := f
  obtain ⟨g, hg₁, hg₂⟩ := g
  obtain rfl : f = g := AlgEquiv.ext h
  rfl

attribute [local instance] HasDerivedCategory.standard

variable (S : SquareZeroExtensionProblem.{u₁, u₂, max u₂ v, u₄})

/-! ### The cotangent complex and the module `N` in a common universe -/

/-- The universe lift used to put `L_{B/A}` and `Ω_{B/A}` in the module category where `Ext` is
taken. -/
noncomputable abbrev liftModules : ModuleCat.{max u₂ v} S.B ⥤ ModuleCat.{max u₂ v u₄} S.B :=
  ModuleCat.uliftFunctor.{u₄} S.B

/-- The cotangent complex `L_{B/A}`, with its terms moved into the universe `max u₂ v u₄`. -/
noncomputable abbrev liftedCotangentComplex : CochainComplex (ModuleCat.{max u₂ v u₄} S.B) ℤ :=
  (S.liftModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (CommAlgCat.cotangentComplex S.A (CommAlgCat.of S.A S.B))

/-- The Kähler differentials `Ω_{B/A}`, in the universe `max u₂ v u₄`. -/
noncomputable abbrev liftedKaehlerDifferential : ModuleCat.{max u₂ v u₄} S.B :=
  ModuleCat.of S.B (ULift.{u₄} (KaehlerDifferential S.A S.B))

/-- The module `N` of the extension problem, in the universe `max u₂ v u₄`. -/
noncomputable abbrev liftedKernelModule : ModuleCat.{max u₂ v u₄} S.B :=
  ModuleCat.of S.B (ULift.{max u₂ v} S.N)

/-- The module `N`, viewed in `D(B)` as a complex concentrated in degree `0`. -/
noncomputable abbrev liftedKernelSingle : DerivedCategory (ModuleCat.{max u₂ v u₄} S.B) :=
  (DerivedCategory.singleFunctor (ModuleCat.{max u₂ v u₄} S.B) 0).obj S.liftedKernelModule

/-- `Ext^i_B(L_{B/A}, N)`, formed in the derived category of `B`-modules. -/
noncomputable abbrev cotangentExt (i : ℤ) : Type _ :=
  DerivedCategory.Ext (DerivedCategory.Q.obj S.liftedCotangentComplex) S.liftedKernelSingle i

/-- **Stacks 08QF**, after the universe lift: the degree-zero homology of `L_{B/A}` is
`Ω_{B/A}`. -/
noncomputable def liftedHomologyZeroIso :
    S.liftedCotangentComplex.homology 0 ≅ S.liftedKaehlerDifferential :=
  ((CommAlgCat.cotangentComplex S.A (CommAlgCat.of S.A S.B)).sc 0).mapHomologyIso
      S.liftModules ≪≫
    S.liftModules.mapIso (CommAlgCat.cotangentComplex_homologyZeroIso S.A (CommAlgCat.of S.A S.B))

/-- Degree-zero homology of the target returns `N`. -/
noncomputable def liftedKernelSingleHomologyIso :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u₂ v u₄} S.B) 0).obj S.liftedKernelSingle ≅
      S.liftedKernelModule :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u₂ v u₄} S.B) 0).app
    S.liftedKernelModule

/-! ### The comparison of `Ext⁰` with differential maps -/

/-- The degree-zero homology of `L_{B/A}`, computed in the derived category, is `Ω_{B/A}`. -/
noncomputable def liftedHomologyZeroDerivedIso :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u₂ v u₄} S.B) 0).obj
        (DerivedCategory.Q.obj S.liftedCotangentComplex) ≅ S.liftedKaehlerDifferential :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u₂ v u₄} S.B) 0).app
      S.liftedCotangentComplex ≪≫ S.liftedHomologyZeroIso

/-- Taking degree-zero homology sends a class in `Ext⁰_B(L_{B/A}, N)` to a map
`Ω_{B/A} → N` of lifted modules. -/
noncomputable def cotangentExtZeroMap :
    S.cotangentExt 0 →+ (S.liftedKaehlerDifferential ⟶ S.liftedKernelModule) :=
  AddMonoidHom.mk'
    (fun e => S.liftedHomologyZeroDerivedIso.inv ≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u₂ v u₄} S.B) 0).shiftMap e 0 0
          (zero_add 0) :
        (DerivedCategory.homologyFunctor (ModuleCat.{max u₂ v u₄} S.B) 0).obj
            (DerivedCategory.Q.obj S.liftedCotangentComplex) ⟶
          (DerivedCategory.homologyFunctor (ModuleCat.{max u₂ v u₄} S.B) 0).obj
            S.liftedKernelSingle) ≫ S.liftedKernelSingleHomologyIso.hom)
    fun a b => by
      rw [Functor.shiftMap_add]
      exact Preadditive.comp_add_comp_assoc S.liftedHomologyZeroDerivedIso.inv _ _
        S.liftedKernelSingleHomologyIso.hom

/-- Undoing the two universe lifts on a map between the lifted modules. -/
noncomputable def liftedHomAddEquiv :
    (S.liftedKaehlerDifferential ⟶ S.liftedKernelModule) ≃+
      (KaehlerDifferential S.A S.B →ₗ[S.B] S.N) :=
  (ModuleCat.homAddEquiv (M := S.liftedKaehlerDifferential)
      (N := S.liftedKernelModule)).trans
    (LinearEquiv.arrowCongrAddEquiv ULift.moduleEquiv ULift.moduleEquiv)

/-- The comparison of `Ext⁰_B(L_{B/A}, N)` with `Hom_B(Ω_{B/A}, N)`, obtained by taking homology
in degree `0` and using the identification `H⁰(L_{B/A}) = Ω_{B/A}`. -/
noncomputable def cotangentExtZeroToHom :
    S.cotangentExt 0 →+ (KaehlerDifferential S.A S.B →ₗ[S.B] S.N) :=
  S.liftedHomAddEquiv.toAddMonoidHom.comp S.cotangentExtZeroMap

/-- The map `cotangentExtZeroToHom e` sends `x` to the image of `x` under the degree-zero homology
map of `e`, with the universe lifts undone. -/
theorem cotangentExtZeroToHom_apply (e : S.cotangentExt 0) (x : KaehlerDifferential S.A S.B) :
    S.cotangentExtZeroToHom e x = ((S.cotangentExtZeroMap e).hom (ULift.up x)).down :=
  rfl

/-- The lifted cotangent complex is concentrated in non-positive degrees. -/
instance liftedCotangentComplex_isLE :
    (DerivedCategory.Q.obj S.liftedCotangentComplex).IsLE 0 :=
  (DerivedCategory.isLE_iff (DerivedCategory.Q.obj S.liftedCotangentComplex) 0).2 fun i hi => by
    have hterm : IsZero (S.liftedCotangentComplex.X i) :=
      S.liftModules.map_isZero
        (CommAlgCat.cotangentComplex_isZero_pos S.A (CommAlgCat.of S.A S.B) i hi)
    exact IsZero.of_iso (HomologicalComplex.ExactAt.of_isZero hterm).isZero_homology
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u₂ v u₄} S.B) i).app
        S.liftedCotangentComplex)

/-- **Stacks 06XS** in the case at hand: taking degree-zero homology identifies
`Ext⁰_B(L_{B/A}, N)` with `Hom_B(Ω_{B/A}, N)`. -/
theorem cotangentExtZeroToHom_bijective : Function.Bijective S.cotangentExtZeroToHom := by
  have hb := DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    (DerivedCategory.Q.obj S.liftedCotangentComplex) S.liftedKernelSingle 0 0 0 0
    (zero_add 0) le_rfl
  exact S.liftedHomAddEquiv.bijective.comp
    ((S.liftedHomologyZeroDerivedIso.homCongr S.liftedKernelSingleHomologyIso).bijective.comp hb)

/-- The comparison of `Ext⁰_B(L_{B/A}, N)` with `Hom_B(Ω_{B/A}, N)`, as an isomorphism of
additive groups. -/
noncomputable def cotangentExtZeroAddEquiv :
    S.cotangentExt 0 ≃+ (KaehlerDifferential S.A S.B →ₗ[S.B] S.N) :=
  AddEquiv.ofBijective S.cotangentExtZeroToHom S.cotangentExtZeroToHom_bijective

/-- The additive equivalence `cotangentExtZeroAddEquiv` acts as `cotangentExtZeroToHom`. -/
theorem cotangentExtZeroAddEquiv_apply (e : S.cotangentExt 0) :
    S.cotangentExtZeroAddEquiv e = S.cotangentExtZeroToHom e := rfl

/-! ### Automorphisms as maps filling the self-comparison diagram -/

/-- A ring endomorphism of a solution which fixes `A'` and induces the identity on `B` and on
`N` is an automorphism of the solution: it is the identity modulo an ideal of square zero, hence
bijective. -/
@[sga "3 III 0.7" "(a), special case"]
noncomputable def isoOfRingHom {X : S.CompatibleExtension.{w}} (φ : X.B' →+* X.B')
    (hA : ∀ a : S.A', φ (algebraMap S.A' X.B' a) = algebraMap S.A' X.B' a)
    (hB : ∀ x : X.B', X.toB (φ x) = X.toB x)
    (hK : ∀ n : S.N, φ ((X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B') =
      ((X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B')) :
    CompatibleExtension.Iso X X := by
  have hker (k : X.B') (hk : X.toB k = 0) : φ k = k := by
    have hz := hK (X.kernelEquiv.symm ⟨k, hk⟩)
    rwa [X.kernelEquiv.apply_symm_apply] at hz
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hk : X.toB (x - y) = 0 := by
      rw [map_sub, ← hB x, ← hB y, hxy, sub_self]
    have hid := hker (x - y) hk
    rw [map_sub, hxy, sub_self] at hid
    exact sub_eq_zero.mp hid.symm
  have hsurj : Function.Surjective φ := by
    intro y
    have hk : X.toB (y - φ y) = 0 := by rw [map_sub, hB y, sub_self]
    refine ⟨y + (y - φ y), ?_⟩
    rw [map_add, hker _ hk]
    abel
  exact
    { toAlgEquiv := AlgEquiv.ofBijective { toRingHom := φ, commutes' := hA } ⟨hinj, hsurj⟩
      toB_comm := by
        ext x
        exact hB x
      kernelEquiv_comm := hK }

/-- The underlying algebra automorphism of `isoOfRingHom φ hA hB hK` acts as `φ`. -/
theorem isoOfRingHom_toAlgEquiv_apply {X : S.CompatibleExtension.{w}} (φ : X.B' →+* X.B')
    (hA : ∀ a : S.A', φ (algebraMap S.A' X.B' a) = algebraMap S.A' X.B' a)
    (hB : ∀ x : X.B', X.toB (φ x) = X.toB x)
    (hK : ∀ n : S.N, φ ((X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B') =
      ((X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B'))
    (x : X.B') : (S.isoOfRingHom φ hA hB hK).toAlgEquiv x = φ x := rfl

/-- The automorphisms of a solution of a square-zero extension problem which induce the identity
on `B` and on `N` are exactly the maps filling the diagram comparing the problem with itself. -/
@[stacks 08SP "automorphisms are the fitting maps of the self-comparison diagram"]
noncomputable def isoFittingMapEquiv (X : S.CompatibleExtension.{w}) :
    CompatibleExtension.Iso X X ≃ (comparisonDiagram X X).FittingMap where
  toFun := fittingMapOfIso
  invFun := isoOfFittingMap
  left_inv _ := CompatibleExtension.Iso.ext' fun _ => rfl
  right_inv _ := CompatibleSquareZeroDeformationDiagram.FittingMap.ext' rfl

/-! ### The main result -/

/-- **Stacks 08SP**, part (3). For a solution `B'` of a square-zero extension problem, the
automorphisms of `B'` inducing the identity on `B` and on `N` are canonically
`Ext⁰_B(L_{B/A}, N)`.

The equivalence carries the identity automorphism to `0` and composition to addition, so it is
an isomorphism of groups, and the class attached to `f` is the one whose associated differential
map sends `d (b' mod N)` to `f(b') - b'`. -/
@[stacks 08SP "automorphisms",
  sga "7 VI 4.16" "(a), affine case",
  ega "0 20.1.4" "Commutative case"]
noncomputable def automorphismsExtEquiv (X : S.CompatibleExtension.{w}) :
    {e : CompatibleExtension.Iso X X ≃ S.cotangentExt 0 //
      e (CompatibleExtension.Iso.refl X) = 0 ∧
      (∀ f g : CompatibleExtension.Iso X X, e (f.trans g) = e f + e g) ∧
      ∀ (f : CompatibleExtension.Iso X X) (b' : X.B'),
        ((X.kernelEquiv (S.cotangentExtZeroToHom (e f)
            (KaehlerDifferential.D S.A S.B (X.toB b'))) :
          RingHom.ker X.toB.toRingHom) : X.B') = f.toAlgEquiv b' - b'} := by
  classical
  obtain ⟨t, htt⟩ := (Deformation.RingThickening.fittingMap_addTorsor_kaehlerDifferentialHom
      (comparisonDiagram X X)
    ⟨fittingMapOfIso (CompatibleExtension.Iso.refl X)⟩).some
  letI : AddTorsor (KaehlerDifferential S.A S.B →ₗ[S.B] S.N)
    (comparisonDiagram X X).FittingMap := t
  -- Subtracting the identity automorphism turns the torsor into a bijection.
  let torsorEquiv : (comparisonDiagram X X).FittingMap ≃
      (KaehlerDifferential S.A S.B →ₗ[S.B] S.N) :=
    { toFun := fun p => p -ᵥ fittingMapOfIso (CompatibleExtension.Iso.refl X)
      invFun := fun α => α +ᵥ fittingMapOfIso (CompatibleExtension.Iso.refl X)
      left_inv := fun p => vsub_vadd p _
      right_inv := fun α => vadd_vsub α _ }
  let autoToHom : CompatibleExtension.Iso X X ≃ (KaehlerDifferential S.A S.B →ₗ[S.B] S.N) :=
    (S.isoFittingMapEquiv X).trans torsorEquiv
  have autoToHom_apply (f : CompatibleExtension.Iso X X) :
      autoToHom f =
        fittingMapOfIso f -ᵥ fittingMapOfIso (CompatibleExtension.Iso.refl X) := rfl
  -- The torsor property of Tag 08S5, specialized to the identity base point and spelled in
  -- terms of `X` rather than of the self-comparison diagram.
  have ht : ∀ (f : CompatibleExtension.Iso X X) (b' : X.B'),
      ((X.kernelEquiv (autoToHom f (KaehlerDifferential.D S.A S.B (X.toB b'))) :
        RingHom.ker X.toB.toRingHom) : X.B') = f.toAlgEquiv b' - b' :=
    fun f b' => htt (fittingMapOfIso f)
      (fittingMapOfIso (CompatibleExtension.Iso.refl X)) b'
  have hzero : autoToHom (CompatibleExtension.Iso.refl X) = 0 := by
    rw [autoToHom_apply]
    exact vsub_self _
  have hderiv : ∀ (α : KaehlerDifferential S.A S.B →ₗ[S.B] S.N) (c : S.B),
      (KaehlerDifferential.linearMapEquivDerivation S.A S.B) α c =
        α (KaehlerDifferential.D S.A S.B c) := fun _ _ => rfl
  have hadd (f g : CompatibleExtension.Iso X X) :
      autoToHom (f.trans g) = autoToHom f + autoToHom g := by
    apply (KaehlerDifferential.linearMapEquivDerivation S.A S.B).injective
    ext b
    obtain ⟨b', rfl⟩ := X.surjective b
    rw [hderiv, hderiv]
    apply X.kernelEquiv.injective
    apply Subtype.ext
    have hg := ht g (f.toAlgEquiv b')
    rw [show X.toB (f.toAlgEquiv b') = X.toB b' from
      congrArg (fun q : X.B' →ₐ[S.A'] S.B => q b') f.toB_comm] at hg
    rw [LinearMap.add_apply, map_add, AddMemClass.coe_add, ht (f.trans g) b', ht f b', hg]
    change (g.toAlgEquiv (f.toAlgEquiv b') : X.B') - b' =
      (f.toAlgEquiv b' - b') + (g.toAlgEquiv (f.toAlgEquiv b') - f.toAlgEquiv b')
    abel
  refine ⟨autoToHom.trans S.cotangentExtZeroAddEquiv.toEquiv.symm, ?_, ?_, ?_⟩
  · change S.cotangentExtZeroAddEquiv.symm (autoToHom (CompatibleExtension.Iso.refl X)) = 0
    rw [hzero, map_zero]
  · intro f g
    change S.cotangentExtZeroAddEquiv.symm (autoToHom (f.trans g)) =
      S.cotangentExtZeroAddEquiv.symm (autoToHom f) +
        S.cotangentExtZeroAddEquiv.symm (autoToHom g)
    rw [hadd, map_add]
  · intro f b'
    have he : S.cotangentExtZeroToHom
        (S.cotangentExtZeroAddEquiv.symm (autoToHom f)) = autoToHom f := by
      rw [← cotangentExtZeroAddEquiv_apply, S.cotangentExtZeroAddEquiv.apply_symm_apply]
    change ((X.kernelEquiv (S.cotangentExtZeroToHom
      (S.cotangentExtZeroAddEquiv.symm (autoToHom f))
        (KaehlerDifferential.D S.A S.B (X.toB b'))) :
        RingHom.ker X.toB.toRingHom) : X.B') = _
    rw [he, ht f b']

end SquareZeroExtensionProblem

end Stacks.Deformation

end
