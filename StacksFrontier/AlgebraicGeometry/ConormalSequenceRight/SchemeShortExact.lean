module

public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.ConormalStalk
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.CoborderDifferentialsStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallySmooth
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.RingTheory.Smooth.Conormal
import StacksCore.Tactic.StacksAttribute

/-!
# Short exactness of the conormal sequence of a smooth immersion

Let `i : Z ⟶ X` be an immersion of schemes over `p : X ⟶ S` with `Z` smooth over `S`. This file
proves that the conormal sequence of [Stacks, Tag 01UZ],

```
0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0,
```

packaged as `Stacks.ConormalSequenceRight.conormalShortComplex`, is short exact. That is
[Stacks, Tag 06AA].

## Main results

* `Stacks.ConormalSequenceRight.conormalShortComplex_shortExact_of_formallySmooth`: the sequence
  is short exact as soon as `i ≫ p` is formally smooth.
* `Stacks.ConormalSequenceRight.conormalShortComplex_shortExact`: the same for a smooth `i ≫ p`,
  which is the hypothesis [Stacks, Tag 06AA] states it under.
* `Stacks.ConormalSequenceRight.exists_germ_eq_of_mem_ker`: an element of the kernel of a map of
  local rings along an immersion is the germ of a section of the defining ideal sheaf.
* `Stacks.ConormalSequenceRight.exists_germ_unit_eq`: every element of a stalk of the conormal
  sheaf is the conormal class of a local section of the defining ideal sheaf. This is what makes
  checking the two arrows on those classes enough.

## Route

Everything is checked on stalks. Write `W = i.coborderRange` for the coborder neighbourhood,
`j = i.liftCoborder : Z ⟶ W` for the closed factor and `q = ι ≫ p : W ⟶ S` for the restriction
of the base morphism, so that `j ≫ q = i ≫ p`. At a point `z` of `Z` put

* `A = 𝒪_{W, j z}`, `C = 𝒪_{Z, z}` and `R = 𝒪_{S, (i ≫ p) z}`, a tower `R ⟶ A ⟶ C` whose second
  map is surjective because `j` is a closed immersion, with `J = ker (A ⟶ C)`.

The three stalks of the sequence are then `J/J²`, `C ⊗_A Ω[A⁄R]` and `Ω[C⁄R]`, and the two arrows
become `KaehlerDifferential.kerCotangentToTensor` and `KaehlerDifferential.mapBaseChange`:

* the left stalk is `Stacks.ConormalSequenceRight.exists_conormalSheafStalkCotangentEquiv`,
  which sends the conormal class of a local section `f` of the defining ideal sheaf to the class
  of the germ of `f`;
* the middle and right stalks and the second arrow are
  `AlgebraicGeometry.Scheme.Hom.exists_relativeDifferentialsPullbackStalkEquiv` applied to `j`
  and `q`, which sends the germ of `1 ⊗ d f` to `1 ⊗ D (germ f)`;
* the first arrow carries the conormal class of `f` to `1 ⊗ d f`, which is
  `Stacks.ConormalSequenceRight.conormalComparison_comp_conormalDifferential`.

Since `kerCotangentToTensor` carries the class of `f` to `1 ⊗ D f`, the two arrows agree with the
algebraic ones on the classes of local sections of the ideal sheaf, and those exhaust the left
stalk. The algebraic input is then [Stacks, Tag 06A8],
`KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange`, whose first conclusion is
injectivity of `kerCotangentToTensor`; exactness in the middle and surjectivity on the right are
Mathlib's `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` and
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap` being an epimorphism for an immersion.

## Implementation notes

The middle term of the sequence is `i^*Ω_{X/S}`, whose stalk is naturally a base change along
`𝒪_{X, i z} ⟶ 𝒪_{Z, z}`, while the left term is a base change along `𝒪_{W, j z} ⟶ 𝒪_{Z, z}`.
Rather than compare the two local rings, the proof is run entirely over `W`, through the
comparison isomorphism `j^*Ω_{W/S} ≅ i^*Ω_{X/S}` of
`Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso`.

The three base points `(i ≫ p) z`, `(j ≫ q) z` and `q (j z)` of `S` are equal, but only
propositionally, and the local rings at them are therefore different terms. They are made
definitionally equal by proving the stalkwise statement for a variable `r : Z ⟶ S` together with
an equation `j ≫ q = r`, and substituting it; composition of morphisms of schemes is
definitionally associative and definitionally composition on base points, so after the
substitution the three stalks of `𝒪_S` are the same term. This is the device already used for
`Stacks.ConormalSequenceRight.facPullbackDifferentialsIso`.

The middle object and the two arrows out of the conormal sheaf are left abstract in the
stalkwise lemma, pinned only by how they act on the conormal class of a local section of the
ideal sheaf; the concrete ones are supplied when it is specialised.

## References

* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 06A8](https://stacks.math.columbia.edu/tag/06A8)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RelativeDifferentialStalkMap
open scoped TensorProduct

universe u

namespace Stacks.ConormalSequenceRight

/-- **An element of the kernel of a map of local rings along an immersion is the germ of a
section of the defining ideal sheaf.** The kernel is the stalk of that ideal sheaf. -/
theorem exists_germ_eq_of_mem_ker {Z X : Scheme.{u}} (j : Z ⟶ X) [IsImmersion j] (z : Z)
    (a : ToType (X.presheaf.stalk (j.base z))) (ha : a ∈ RingHom.ker (j.stalkMap z).hom) :
    ∃ (V : Opens X) (hz : j.base z ∈ V)
      (s : (idealPresheaf (definingIdealOfHom j)).obj (op V)),
      X.presheaf.germ V (j.base z) hz s.1 = a := by
  have hmem : a ∈ Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
      (definingIdealOfHom j) (j.base z) := by
    rw [stalkIdeal_definingIdealOfHom_eq_ker]
    exact ha
  obtain ⟨V, hz, t, ht, hgerm⟩ :=
    (Stacks.RingedSpace.mem_stalkIdeal_iff (definingIdealOfHom j)).mp hmem
  exact ⟨V, hz, ⟨t, ht⟩, hgerm⟩

/-- **Every element of a stalk of the conormal sheaf is the conormal class of a local section of
the defining ideal sheaf.** The stalk is `J/J²` for `J` the kernel on local rings, classes of
elements of `J` exhaust it, and every element of `J` is the germ of a section of the ideal
sheaf. -/
theorem exists_germ_unit_eq {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (z : Z)
    (x : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (conormalRetyped i).presheaf z)) :
    ∃ (V : Opens i.coborderRange.toScheme) (hz : i.liftCoborder.base z ∈ V)
      (s : (idealPresheaf (definingIdealOfHom i.liftCoborder)).obj (op V)),
      x = TopCat.Presheaf.germ (C := Ab.{u}) (conormalRetyped i).presheaf
        (i.liftCoborder ⁻¹ᵁ V) z hz
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          ((definingIdeal i).toSheafOfModules)).val.app (op V) s) := by
  let := (i.liftCoborder.stalkMap z).hom.toAlgebra
  obtain ⟨e, he⟩ := exists_conormalSheafStalkCotangentEquiv i z
  obtain ⟨a, ha⟩ := Ideal.toCotangent_surjective (RingHom.ker (i.liftCoborder.stalkMap z).hom) (e x)
  obtain ⟨V, hz, s, hgerm⟩ := exists_germ_eq_of_mem_ker i.liftCoborder z a.1 a.2
  refine ⟨V, hz, s, e.injective ?_⟩
  rw [he V hz s, ← ha]
  exact congrArg (Ideal.toCotangent _) (Subtype.ext hgerm.symm)

/-- The stalk at `z`, as a functor from sheaves of modules on `Z` to abelian groups. This is
`AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor` at the structure sheaf of `Z`. -/
noncomputable abbrev stalkAb (Z : Scheme.{u}) (z : Z) : Z.Modules ⥤ AddCommGrpCat.{u} :=
  AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor Z.ringCatSheaf z

section Stalkwise

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The stalk at `z` of a morphism of sheaves of modules on a scheme carries the germ of a
section to the germ of its image. -/
theorem stalkAb_map_germ {M N : Z.Modules} (φ : M ⟶ N) (z : Z)
    (U : Opens Z) (hz : z ∈ U) (m : M.val.obj (op U)) :
    (stalkAb Z z).map φ (TopCat.Presheaf.germ (C := Ab.{u}) M.val.presheaf U z hz m) =
      TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf U z hz (φ.val.app (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U z hz
    ((PresheafOfModules.toPresheaf Z.ringCatSheaf.obj).map φ.val) m

/-- **The conormal sequence of an immersion is exact at its middle term**, in the model in which
that term is presented through the closed factor `j = i.liftCoborder` into the coborder
neighbourhood.

The middle term `M` and the arrow `c` out of the conormal sheaf are abstract, pinned by `hc`:
`c` carries the conormal class of a local section `f` of the defining ideal sheaf to the image
of `1 ⊗ d f` under the given identification `e` of `j^*Ω_{W/S}` with `M`.

This is `Stacks.ConormalSequenceRight.shortExact_of_closedFactorModel` of
[Stacks, Tag 06AA] with the formal smoothness hypothesis dropped and the injectivity conclusion
given up with it. -/
theorem exact_of_closedFactorModel
    {q : i.coborderRange.toScheme ⟶ S} {r : Z ⟶ S} (hr : i.liftCoborder ≫ q = r)
    {M : Z.Modules}
    (e : (Scheme.Modules.pullback i.liftCoborder).obj (Scheme.Hom.relativeDifferentials q) ≅ M)
    (g : M ⟶ Scheme.Hom.relativeDifferentials r)
    (hg : e.hom ≫ g = Scheme.Hom.relativeDifferentialsMap i.liftCoborder q r (𝟙 S)
      (by rw [hr, Category.comp_id]))
    (c : (Scheme.Modules.pullback i.liftCoborder).obj
      ((definingIdeal i).toSheafOfModules) ⟶ M)
    (hc : ∀ (V : Opens i.coborderRange.toScheme)
        (s : (definingIdeal i).toSheafOfModules.val.obj (op V)),
      (c.val.app (op (i.liftCoborder ⁻¹ᵁ V))).hom
          (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            ((definingIdeal i).toSheafOfModules)).val.app (op V) s) =
        (e.hom.val.app (op (i.liftCoborder ⁻¹ᵁ V))).hom
          (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            (Scheme.Hom.relativeDifferentials q)).val.app (op V)
            ((Scheme.Hom.universalRelativeDerivation q).d s.1)))
    (hzero : c ≫ g = 0) :
    (ShortComplex.mk c g hzero).Exact := by
  classical
  subst hr
  have key : ∀ z : Z, ∀ m, (stalkAb Z z).map g m = 0 → ∃ l, (stalkAb Z z).map c l = m := by
    intro z
    -- the tower of local rings at `z`
    let A : Type u :=
      ToType ((i.coborderRange.toScheme).presheaf.stalk (i.liftCoborder.base z))
    let C : Type u := ToType (Z.presheaf.stalk z)
    let R : Type u := ToType (S.presheaf.stalk (q.base (i.liftCoborder.base z)))
    let : Algebra R A := algebraStalkMap q (i.liftCoborder.base z)
    let : Algebra A C := (i.liftCoborder.stalkMap z).hom.toAlgebra
    let : Algebra R C := algebraStalkMap (i.liftCoborder ≫ q) z
    let : IsScalarTower R A C := Scheme.Hom.isScalarTower_stalkMap i.liftCoborder q z
    have hsurj : Function.Surjective (algebraMap A C) :=
      i.liftCoborder.stalkMap_surjective z
    -- the identifications of the three stalks
    obtain ⟨eM, heMgerm, heMbridge⟩ :=
      Scheme.Hom.exists_relativeDifferentialsPullbackStalkEquiv i.liftCoborder q z
    have hψ : Function.Bijective ((stalkAb Z z).map e.hom) :=
      ConcreteCategory.bijective_of_isIso ((stalkAb Z z).mapIso e).hom
    -- the first arrow on the conormal class of a section of the ideal sheaf
    have hcgerm : ∀ (V : Opens i.coborderRange.toScheme)
        (hz : i.liftCoborder.base z ∈ V)
        (s : (idealPresheaf (definingIdealOfHom i.liftCoborder)).obj (op V)),
        (stalkAb Z z).map c (TopCat.Presheaf.germ (C := Ab.{u}) (conormalRetyped i).presheaf
            (i.liftCoborder ⁻¹ᵁ V) z hz
            (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
              ((definingIdeal i).toSheafOfModules)).val.app (op V) s)) =
          (stalkAb Z z).map e.hom (TopCat.Presheaf.germ (C := Ab.{u})
            ((Scheme.Modules.pullback i.liftCoborder).obj
              (Scheme.Hom.relativeDifferentials q)).val.presheaf (i.liftCoborder ⁻¹ᵁ V) z hz
            (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
              (Scheme.Hom.relativeDifferentials q)).val.app (op V)
              ((Scheme.Hom.universalRelativeDerivation q).d s.1))) := by
      intro V hz s
      refine Eq.trans (stalkAb_map_germ c z (i.liftCoborder ⁻¹ᵁ V) hz _) ?_
      refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := Ab.{u}) M.val.presheaf
        (i.liftCoborder ⁻¹ᵁ V) z hz) (hc V s)) ?_
      exact (stalkAb_map_germ e.hom z (i.liftCoborder ⁻¹ᵁ V) hz _).symm
    -- exactness: the image is the kernel by Mathlib's exact sequence
    intro m hm
    obtain ⟨n, rfl⟩ := hψ.2 m
    have h1 : Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom Z.sheaf.presheaf z
        (Scheme.Hom.relativeDifferentialsMap i.liftCoborder q (i.liftCoborder ≫ q) (𝟙 S)
          (Category.comp_id (i.liftCoborder ≫ q)).symm).val n = 0 := by
      have h0 : (stalkAb Z z).map (e.hom ≫ g) n = 0 :=
        (ConcreteCategory.congr_hom (Functor.map_comp (stalkAb Z z) e.hom g) n).trans hm
      rw [hg] at h0
      exact h0
    have hzeroM : KaehlerDifferential.mapBaseChange R A C (eM n) = 0 := by
      refine (heMbridge n).trans ?_
      rw [h1]
      exact (Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv
        (i.liftCoborder ≫ q) z).map_zero
    obtain ⟨u, hu⟩ :=
      (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A C hsurj _).mp hzeroM
    obtain ⟨w, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker (algebraMap A C)) u
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at hu
    obtain ⟨V, hz, s, hgerm⟩ := exists_germ_eq_of_mem_ker i.liftCoborder z w.1 w.2
    refine ⟨TopCat.Presheaf.germ (C := Ab.{u}) (conormalRetyped i).presheaf
      (i.liftCoborder ⁻¹ᵁ V) z hz
      (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
        ((definingIdeal i).toSheafOfModules)).val.app (op V) s), ?_⟩
    refine Eq.trans (hcgerm V hz s) (congrArg ((stalkAb Z z).map e.hom) (eM.injective ?_))
    refine (heMgerm V hz s.1).trans (Eq.trans ?_ hu)
    exact congrArg (fun y => (1 : C) ⊗ₜ[A] KaehlerDifferential.D R A y) hgerm
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact Z.ringCatSheaf
    (ShortComplex.mk c g hzero)).2 fun z => ?_
  exact (ShortComplex.ab_exact_iff _).2 fun m hm => key z m hm

/-- **The conormal sequence of an immersion is short exact when the source is formally smooth
over the base**, in the model in which the middle term is presented through the closed factor
`j = i.liftCoborder` into the coborder neighbourhood.

The middle term `M` and the arrow `c` out of the conormal sheaf are abstract, pinned by `hc`:
`c` carries the conormal class of a local section `f` of the defining ideal sheaf to the image
of `1 ⊗ d f` under the given identification `e` of `j^*Ω_{W/S}` with `M`. -/
private theorem shortExact_of_closedFactorModel
    {q : i.coborderRange.toScheme ⟶ S} {r : Z ⟶ S} (hr : i.liftCoborder ≫ q = r)
    (hsm : AlgebraicGeometry.FormallySmooth r) {M : Z.Modules}
    (e : (Scheme.Modules.pullback i.liftCoborder).obj (Scheme.Hom.relativeDifferentials q) ≅ M)
    (g : M ⟶ Scheme.Hom.relativeDifferentials r)
    (hg : e.hom ≫ g = Scheme.Hom.relativeDifferentialsMap i.liftCoborder q r (𝟙 S)
      (by rw [hr, Category.comp_id]))
    (hepi : Epi g)
    (c : (Scheme.Modules.pullback i.liftCoborder).obj
      ((definingIdeal i).toSheafOfModules) ⟶ M)
    (hc : ∀ (V : Opens i.coborderRange.toScheme)
        (s : (definingIdeal i).toSheafOfModules.val.obj (op V)),
      (c.val.app (op (i.liftCoborder ⁻¹ᵁ V))).hom
          (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            ((definingIdeal i).toSheafOfModules)).val.app (op V) s) =
        (e.hom.val.app (op (i.liftCoborder ⁻¹ᵁ V))).hom
          (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            (Scheme.Hom.relativeDifferentials q)).val.app (op V)
            ((Scheme.Hom.universalRelativeDerivation q).d s.1)))
    (hzero : c ≫ g = 0) :
    (ShortComplex.mk c g hzero).ShortExact := by
  classical
  subst hr
  have key : ∀ z : Z, Function.Injective ((stalkAb Z z).map c) := by
    intro z
    -- the tower of local rings at `z`
    let A : Type u :=
      ToType ((i.coborderRange.toScheme).presheaf.stalk (i.liftCoborder.base z))
    let C : Type u := ToType (Z.presheaf.stalk z)
    let R : Type u := ToType (S.presheaf.stalk (q.base (i.liftCoborder.base z)))
    let : Algebra R A := algebraStalkMap q (i.liftCoborder.base z)
    let : Algebra A C := (i.liftCoborder.stalkMap z).hom.toAlgebra
    let : Algebra R C := algebraStalkMap (i.liftCoborder ≫ q) z
    let : IsScalarTower R A C := Scheme.Hom.isScalarTower_stalkMap i.liftCoborder q z
    let : Algebra.FormallySmooth R C :=
      Scheme.Hom.formallySmooth_stalkMap_of_formallySmooth hsm z
    have hsurj : Function.Surjective (algebraMap A C) :=
      i.liftCoborder.stalkMap_surjective z
    -- the identifications of the three stalks
    obtain ⟨eL, heL⟩ := exists_conormalSheafStalkCotangentEquiv i z
    obtain ⟨eM, heMgerm, -⟩ :=
      Scheme.Hom.exists_relativeDifferentialsPullbackStalkEquiv i.liftCoborder q z
    have hψ : Function.Bijective ((stalkAb Z z).map e.hom) :=
      ConcreteCategory.bijective_of_isIso ((stalkAb Z z).mapIso e).hom
    -- the first arrow on the conormal class of a section of the ideal sheaf
    have hcgerm : ∀ (V : Opens i.coborderRange.toScheme)
        (hz : i.liftCoborder.base z ∈ V)
        (s : (idealPresheaf (definingIdealOfHom i.liftCoborder)).obj (op V)),
        (stalkAb Z z).map c (TopCat.Presheaf.germ (C := Ab.{u}) (conormalRetyped i).presheaf
            (i.liftCoborder ⁻¹ᵁ V) z hz
            (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
              ((definingIdeal i).toSheafOfModules)).val.app (op V) s)) =
          (stalkAb Z z).map e.hom (TopCat.Presheaf.germ (C := Ab.{u})
            ((Scheme.Modules.pullback i.liftCoborder).obj
              (Scheme.Hom.relativeDifferentials q)).val.presheaf (i.liftCoborder ⁻¹ᵁ V) z hz
            (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
              (Scheme.Hom.relativeDifferentials q)).val.app (op V)
              ((Scheme.Hom.universalRelativeDerivation q).d s.1))) := by
      intro V hz s
      refine Eq.trans (stalkAb_map_germ c z (i.liftCoborder ⁻¹ᵁ V) hz _) ?_
      refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := Ab.{u}) M.val.presheaf
        (i.liftCoborder ⁻¹ᵁ V) z hz) (hc V s)) ?_
      exact (stalkAb_map_germ e.hom z (i.liftCoborder ⁻¹ᵁ V) hz _).symm
    have hinj : Function.Injective (KaehlerDifferential.kerCotangentToTensor R A C) :=
      (KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange R A C hsurj).1
    intro x₁ x₂ hx
    obtain ⟨V₁, hz₁, s₁, rfl⟩ := exists_germ_unit_eq i z x₁
    obtain ⟨V₂, hz₂, s₂, rfl⟩ := exists_germ_unit_eq i z x₂
    have hx' := (hcgerm V₁ hz₁ s₁).symm.trans (hx.trans (hcgerm V₂ hz₂ s₂))
    have h2 := congrArg eM (hψ.1 hx')
    refine eL.injective (Eq.trans (heL V₁ hz₁ s₁) (Eq.trans (hinj ?_) (heL V₂ hz₂ s₂).symm))
    refine Eq.trans (KaehlerDifferential.kerCotangentToTensor_toCotangent R A C _)
      (Eq.trans ?_ (KaehlerDifferential.kerCotangentToTensor_toCotangent R A C _).symm)
    exact (heMgerm V₁ hz₁ s₁.1).symm.trans (h2.trans (heMgerm V₂ hz₂ s₂.1))
  refine ShortComplex.ShortExact.mk' (exact_of_closedFactorModel i rfl e g hg c hc hzero)
    ?_ hepi
  -- a morphism of sheaves of modules injective on every stalk is a monomorphism
  exact (SheafOfModules.toSheaf Z.ringCatSheaf).mono_of_mono_map
    ((TopCat.Presheaf.mono_iff_stalk_mono _).2 fun z =>
      (AddCommGrpCat.mono_iff_injective _).2 (key z))

/-- **[Stacks, Tag 01UZ], exactness at the middle term of the conormal sequence,
unconditionally.** For an immersion of schemes `i : Z ⟶ X` over `p : X ⟶ S` the conormal
sequence `𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` is exact at `i^*Ω_{X/S}`: the image of the
conormal differential is the kernel of the canonical map of [Stacks, Tag 01UV].

No hypothesis beyond `IsImmersion i` is used, and the sequence is the canonical one rather than
a presentation by equations. Injectivity of the first arrow, which would make the sequence short
exact, is false in general and holds under the smoothness hypothesis of [Stacks, Tag 06AA]; see
`Stacks.ConormalSequenceRight.conormalShortComplex_shortExact`. -/
@[stacks 01UZ "exactness at the middle term of the sequence 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S},
for an arbitrary immersion and with the conormal sheaf itself at the left-hand end",
  sga "7 XI 1.3" "partial"]
theorem conormalShortComplex_exact (p : X ⟶ S) : (conormalShortComplex i p).Exact := by
  refine exact_of_closedFactorModel i (q := i.coborderRange.ι ≫ p) (r := i ≫ p)
    (by rw [← Category.assoc, i.liftCoborder_ι])
    (coborderPullbackDifferentialsIso i p) _
    (coborderPullbackDifferentialsIso_hom_comp i p)
    (conormalDifferential i p) (fun V s => ?_)
    (conormalDifferential_comp_relativeDifferentialsMap i p)
  exact congrArg (fun m => (m.val.app (op V)).hom s)
    (conormalComparison_comp_conormalDifferential i p)

end Stalkwise

/-- **[Stacks, Tag 06AA] under the hypothesis the proof uses.** For an immersion `i : Z ⟶ X` of
schemes over `p : X ⟶ S` with `i ≫ p` formally smooth, the conormal sequence
`0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` of [Stacks, Tag 01UZ] is short exact.

Only formal smoothness of the stalk maps of `i ≫ p` is used, which is what a smooth morphism
supplies through
`AlgebraicGeometry.Scheme.Hom.formallySmooth_stalkMap_of_formallySmooth`; nothing is asked of
`X`, exactly as in [Stacks, Tag 06A8]. -/
@[ega "0 22.4.4.2" "Case p·1 = 0 in Λ", sga "7 XI 1.3" "partial"]
theorem conormalShortComplex_shortExact_of_formallySmooth {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (p : X ⟶ S) (hsm : AlgebraicGeometry.FormallySmooth (i ≫ p)) :
    (conormalShortComplex i p).ShortExact := by
  refine shortExact_of_closedFactorModel i (q := i.coborderRange.ι ≫ p) (r := i ≫ p)
    (by rw [← Category.assoc, i.liftCoborder_ι]) hsm
    (coborderPullbackDifferentialsIso i p) _
    (coborderPullbackDifferentialsIso_hom_comp i p) (differentialsMapOver_epi i p)
    (conormalDifferential i p) (fun V s => ?_)
    (conormalDifferential_comp_relativeDifferentialsMap i p)
  exact congrArg (fun m => (m.val.app (op V)).hom s)
    (conormalComparison_comp_conormalDifferential i p)

/-- **[Stacks, Tag 06AA].** For an immersion of schemes `i : Z ⟶ X` over `p : X ⟶ S` with `Z`
smooth over `S`, the conormal sequence `0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` of
[Stacks, Tag 01UZ] is short exact.

A smooth morphism is formally smooth by [Stacks, Tag 02H6], and formal smoothness is all the
proof uses. -/
@[stacks 06AA, sga "7 XI 1.3" "partial"]
theorem conormalShortComplex_shortExact {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (p : X ⟶ S) (hZ : AlgebraicGeometry.Smooth (i ≫ p)) :
    (conormalShortComplex i p).ShortExact :=
  conormalShortComplex_shortExact_of_formallySmooth i p
    ((Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth (i ≫ p)).mp hZ).2

end Stacks.ConormalSequenceRight

end
