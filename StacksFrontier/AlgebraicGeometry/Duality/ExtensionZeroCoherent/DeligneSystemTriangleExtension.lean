module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.BoundedCoherentTriangulated
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Coherence

/-!
# Extending a distinguished triangle of `D^b_Coh(𝒪_U)` to a system of Deligne systems

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and let `K ⟶ L ⟶ M ⟶ K[1]` be a
distinguished triangle of `D^b_{Coh}(𝒪_U)`. [Stacks, Tag 0G4M] produces an inverse system of
distinguished triangles `K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]` of `D^b_{Coh}(𝒪_X)` whose three vertex
systems are Deligne systems and whose restriction to `U` is isomorphic to the triangle one
started with.

This file carries out the construction, from the one input the source's proof takes before it
starts: a *coherent complex model over `X`* for the morphism `K ⟶ L`, that is a morphism
`α^• : 𝓕^• ⟶ 𝓖^•` of bounded complexes of coherent `𝒪_X`-modules whose image in `D(𝒪_U)` under
restriction is the given `K ⟶ L`. That input is
`AlgebraicGeometry.DeligneTriangle.CoherentComplexModel`; see the implementation notes for
exactly which parts of the source it packages and which tags supply them.

## The construction

Choose a quasi-coherent sheaf of ideals `𝓘` cutting out `X ∖ U` — the vanishing ideal of the
closed complement of the range of `j` serves. The Deligne system attached to a bounded complex
`𝓕^•` of coherent modules is the system `(𝓘^n𝓕^•)` of its termwise ideal-power subcomplexes; what
has to be checked is that each `𝓘^n𝓕^•` defines an object of `D^b_{Coh}(𝒪_X)`, which is
`AlgebraicGeometry.DeligneTriangle.mem_boundedCoherentDerived_Q_obj` applied to
`AlgebraicGeometry.DeligneTriangle.idealPowerComplex_bounds` and
`AlgebraicGeometry.DeligneTriangle.isCoherent_idealPowerComplex_X`.

The third system is the one the source's identity

`C(α_n)^• = 𝓘^n C(α^•)`

provides: ideal powers are computed termwise, so they are the image of a complex under the
*functor* `AlgebraicGeometry.DeligneTriangle.idealPowerFunctor`, and that functor is additive, so
Mathlib's comparison `CochainComplex.mappingCone.mapHomologicalComplexXIso` for an additive
functor applied to a mapping cone is exactly the displayed identity, in each degree. This is what
makes `𝓘^n C(α^•)` carry an `AlgebraicGeometry.IdealPowerComplexSystem` whose terms are the cones
`C(α_n)^•`, hence what makes the third system a Deligne system rather than merely an inverse
system of cones: the `AlgebraicGeometry.DeligneSystem` structure demands the ideal-power
presentation, and the cone has to be taken at the level of complexes for it to have one.

The inverse system of distinguished triangles is then the system of the cone triangles of the
`α_n`, which is `AlgebraicGeometry.DeligneTriangle.mappingConeTriangleFunctor`; each is
distinguished by `DerivedCategory.mappingCone_triangle_distinguished`. Its restriction to `U` is
the constant system at the cone triangle of `α^•`, because the inclusion `𝓘^n𝓕^• ⟶ 𝓕^•` becomes
an isomorphism on `U` (the ideal is the unit ideal away from its support,
`AlgebraicGeometry.DeligneTriangle.isIso_restrict_idealPowerComplex_inclusion`) and then the
third vertex follows by the five lemma. Finally the restricted triangle is identified with the
given one by `TR3` and the fact that a morphism of distinguished triangles which is invertible on
two vertices is invertible on the third,
`AlgebraicGeometry.DeligneTriangle.nonempty_triangle_iso_of_mor₁`.

## Main definitions

* `AlgebraicGeometry.DeligneTriangle.idealPowerFunctor`: `M ↦ 𝓘^nM`, as an additive functor.
* `AlgebraicGeometry.DeligneTriangle.deligneSystemOfComplex`: the Deligne system `(𝓘^n𝓕^•)` of a
  bounded complex of coherent modules.
* `AlgebraicGeometry.DeligneTriangle.conePowerSystem`: the ideal-power presentation of `C(α^•)`
  whose `n`-th complex is `C(α_n)^•`.
* `AlgebraicGeometry.DeligneTriangle.deligneSystemOfMappingCone`: the Deligne system of the cone.
* `AlgebraicGeometry.DeligneTriangle.CoherentComplexModel`: the input described above.

## Main results

* `AlgebraicGeometry.DeligneTriangle.exists_deligneSystem_distTriang_boundedCoherent`:
  **Stacks 0G4M**, proved from this construction in the companion file
  `DeligneSystemTriangleExtensionCoherent`.

## Implementation notes

**What `CoherentComplexModel` assumes, and what it does not.** Its fields are a morphism of
bounded complexes of coherent `𝒪_X`-modules together with an identification, in `D(𝒪_U)`, of its
restriction with the given morphism `K ⟶ L` of `D^b_{Coh}(𝒪_U)`. In the source this is the
conclusion of the first two paragraphs of the proof of [Stacks, Tag 0G4M]: `K` and `L` are
extended to `X` by [Stacks, Tag 0G4L] (2) — which rests on [Stacks, Tag 0G48] — the morphism
`K ⟶ L` is extended by [Stacks, Tag 0G2H], and the resulting morphism of `D^b_{Coh}(𝒪_X)` is
represented by a morphism of bounded complexes of coherent modules by [Stacks, Tag 0FDB]. So the
three tags `0G48`, `0G2H` and `0FDB` are what supply this one input. Nothing else is assumed: the
ideal-power subcomplexes, the three Deligne systems, the cone identity, the inverse system of
distinguished triangles and the restriction isomorphism are all proved here. In particular
`AlgebraicGeometry.DeligneSystem.Value.isIso_restrictionNatTrans`, which carries [Stacks, Tag
0G2H] as data, is never used, and the third vertex of the triangle is not assumed to be of any
particular shape — the triangle `K ⟶ L ⟶ M ⟶ K[1]` enters only through `TR3`.

**Which derived category.** There are two `HasDerivedCategory` instances available for
`X.Modules`: the global `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, whose morphisms
live in universe `u`, and `CategoryTheory.HasDerivedCategory.standard`, whose morphisms live in
universe `u + 1`. They are *different* categories, and `AlgebraicGeometry.boundedCoherentDerived`
denotes different things depending on which is ambient. This file is about the second one: it
installs `CategoryTheory.HasDerivedCategory.standard` as a local instance **at priority 10000**,
which beats the global instance's default priority, so that the choice does not depend on whether
the global one happens to be in scope through some import. That is the model of
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemHom`, where
`AlgebraicGeometry.DeligneSystem` and `AlgebraicGeometry.BoundedCoherentDerived` are declared,
and of
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.BoundedCoherentTriangulated`, whose
triangulatedness instance for `D^b_{Coh}(𝒪_X)` is what this file consumes; a mismatch would be a
type error at every use of `AlgebraicGeometry.DeligneSystem` below rather than a silent change of
statement, because the Deligne systems this file builds are built field by field.

## References

* [Stacks Project, Tag 0G4M](https://stacks.math.columbia.edu/tag/0G4M)
* [Stacks Project, Tag 0G4L](https://stacks.math.columbia.edu/tag/0G4L)
* [Stacks Project, Tag 0G48](https://stacks.math.columbia.edu/tag/0G48)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.AlgebraicGeometry.IdealPower

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.DeligneTriangle

variable {U X : Scheme.{u}}

/-! ### Ideal powers as an additive functor -/

/-- `𝓘^nM`, read as an object of the category of `𝒪_X`-modules. -/
public abbrev idealPowerObj (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) : X.Modules :=
  (idealPowerMultiple I n M).toSheafOfModules

/-- The inclusion `𝓘^nM ⟶ M`, read in the category of `𝒪_X`-modules. -/
public abbrev idealPowerIota (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) :
    idealPowerObj I n M ⟶ M :=
  (idealPowerMultiple I n M).ι

/-- The morphism `𝓘^nM ⟶ 𝓘^nN` induced by a morphism `M ⟶ N` of sheaves of modules. -/
public def idealPowerTermMap (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules} (f : M ⟶ N) :
    idealPowerObj I n M ⟶ idealPowerObj I n N :=
  sheafSubmoduleMap f (idealPowerMultiple I n M) (idealPowerMultiple I n N)
    (idealPowerMultiple_le_comap I n f _ le_rfl)

/-- The induced morphism on ideal powers is the restriction of the given one. -/
public lemma idealPowerTermMap_comp_ι (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules}
    (f : M ⟶ N) :
    idealPowerTermMap I n f ≫ idealPowerIota I n N = idealPowerIota I n M ≫ f :=
  sheafSubmoduleMap_comp_ι f (idealPowerMultiple I n M) (idealPowerMultiple I n N)
    (idealPowerMultiple_le_comap I n f _ le_rfl)

/-- Taking ideal powers is compatible with composition. -/
public lemma idealPowerTermMap_comp (I : X.IdealSheafData) (n : ℕ) {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) :
    idealPowerTermMap I n (f ≫ g) = idealPowerTermMap I n f ≫ idealPowerTermMap I n g := by
  refine cancel_sheafSubmodule_ι (idealPowerMultiple I n P) _ _ ?_
  refine Eq.trans (idealPowerTermMap_comp_ι I n (f ≫ g)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ g) (idealPowerTermMap_comp_ι I n f).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => idealPowerTermMap I n f ≫ z)
    (idealPowerTermMap_comp_ι I n g).symm) ?_
  exact (Category.assoc _ _ _).symm

/-- **The `n`-th ideal power of a quasi-coherent ideal sheaf, as a functor** `M ↦ 𝓘^nM` on
sheaves of modules. Its value on a complex is the ideal-power subcomplex, so the identity
`C(α_n)^• = 𝓘^nC(α^•)` of [Stacks, Tag 0G4M] is an instance of the comparison between an
additive functor and a mapping cone. -/
public def idealPowerFunctor (I : X.IdealSheafData) (n : ℕ) : X.Modules ⥤ X.Modules where
  obj M := idealPowerObj I n M
  map f := idealPowerTermMap I n f
  map_id M := cancel_sheafSubmodule_ι (idealPowerMultiple I n M) _ _
    ((idealPowerTermMap_comp_ι I n (𝟙 M)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  map_comp f g := idealPowerTermMap_comp I n f g

/-- **Taking ideal powers is additive.** Both sides of `𝓘^n(f + g) = 𝓘^nf + 𝓘^ng` restrict to
`f + g` on the subsheaf, and a morphism into a subsheaf is determined by its restriction. -/
public instance idealPowerFunctor_additive (I : X.IdealSheafData) (n : ℕ) :
    (idealPowerFunctor I n).Additive where
  map_add {M N} f g := by
    refine cancel_sheafSubmodule_ι (idealPowerMultiple I n N) _ _ ?_
    refine Eq.trans (idealPowerTermMap_comp_ι I n (f + g)) ?_
    refine Eq.trans (Preadditive.comp_add _ _ _ _ _ _) ?_
    refine Eq.trans (congrArg₂ (· + ·) (idealPowerTermMap_comp_ι I n f).symm
      (idealPowerTermMap_comp_ι I n g).symm) ?_
    exact (Preadditive.add_comp _ _ _ _ _ _).symm

/-! ### The ideal-power subcomplexes as the image of that functor -/

/-- The inclusion `𝓘^n𝓕^i ⟶ 𝓕^i` is the `i`-th component of the inclusion of the ideal-power
subcomplex. -/
public lemma idealPowerComplexSystem_inclusion_f (I : X.IdealSheafData)
    (F : CochainComplex X.Modules ℤ) (n : ℕ) (i : ℤ) :
    ((idealPowerComplexSystem I F).inclusion n).f i = (idealPowerMultiple I n (F.X i)).ι := rfl

/-- The transition `𝓘^{n+1}𝓕^• ⟶ 𝓘^n𝓕^•` is, in each degree, the inclusion of ideal powers. -/
public lemma idealPowerComplexSystem_transition_f_comp_ι (I : X.IdealSheafData)
    (F : CochainComplex X.Modules ℤ) (n : ℕ) (i : ℤ) :
    ((idealPowerComplexSystem I F).transition n).f i ≫ (idealPowerMultiple I n (F.X i)).ι =
      (idealPowerMultiple I (n + 1) (F.X i)).ι :=
  idealPowerMultipleMap_comp_ι I (F.X i) (Nat.le_succ n)

/-- **The ideal-power subcomplex is the image of the complex under the ideal-power functor.** -/
public lemma idealPowerComplexSystem_complex_eq (I : X.IdealSheafData)
    (F : CochainComplex X.Modules ℤ) (n : ℕ) :
    (idealPowerComplexSystem I F).complex n =
      ((idealPowerFunctor I n).mapHomologicalComplex (ComplexShape.up ℤ)).obj F := rfl

/-- The morphism `𝓘^n𝓕^• ⟶ 𝓘^n𝓖^•` of ideal-power subcomplexes induced by a morphism
`𝓕^• ⟶ 𝓖^•` of complexes. It is the image of the morphism under the ideal-power functor, which
is what makes the cone comparison available. -/
public def idealPowerComplexMap (I : X.IdealSheafData) {F G : CochainComplex X.Modules ℤ}
    (f : F ⟶ G) (n : ℕ) :
    (idealPowerComplexSystem I F).complex n ⟶ (idealPowerComplexSystem I G).complex n :=
  ((idealPowerFunctor I n).mapHomologicalComplex (ComplexShape.up ℤ)).map f

/-- In each degree the induced morphism of ideal-power subcomplexes is the restriction of the
given morphism of complexes. -/
public lemma idealPowerComplexMap_f (I : X.IdealSheafData) {F G : CochainComplex X.Modules ℤ}
    (f : F ⟶ G) (n : ℕ) (i : ℤ) :
    (idealPowerComplexMap I f n).f i = idealPowerTermMap I n (f.f i) := rfl

/-- The induced morphism of ideal-power subcomplexes commutes with the inclusions into the
original complexes. -/
public lemma idealPowerComplexMap_comp_inclusion (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) (n : ℕ) :
    idealPowerComplexMap I f n ≫ (idealPowerComplexSystem I G).inclusion n =
      (idealPowerComplexSystem I F).inclusion n ≫ f :=
  HomologicalComplex.hom_ext _ _ fun i ↦ idealPowerTermMap_comp_ι I n (f.f i)

/-- The induced morphisms of ideal-power subcomplexes are compatible with the transitions. -/
public lemma idealPowerComplexMap_transition (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) (n : ℕ) :
    (idealPowerComplexSystem I F).transition n ≫ idealPowerComplexMap I f n =
      idealPowerComplexMap I f (n + 1) ≫ (idealPowerComplexSystem I G).transition n := by
  apply HomologicalComplex.hom_ext
  intro i
  change ((idealPowerComplexSystem I F).transition n).f i ≫ idealPowerTermMap I n (f.f i) =
    idealPowerTermMap I (n + 1) (f.f i) ≫ ((idealPowerComplexSystem I G).transition n).f i
  refine cancel_sheafSubmodule_ι (idealPowerMultiple I n (G.X i)) _ _ ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => ((idealPowerComplexSystem I F).transition n).f i ≫ z)
    (idealPowerTermMap_comp_ι I n (f.f i))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ f.f i)
    (idealPowerComplexSystem_transition_f_comp_ι I F n i)) ?_
  refine Eq.trans (idealPowerTermMap_comp_ι I (n + 1) (f.f i)).symm ?_
  refine Eq.trans (congrArg (fun z => idealPowerTermMap I (n + 1) (f.f i) ≫ z)
    (idealPowerComplexSystem_transition_f_comp_ι I G n i).symm) ?_
  exact (Category.assoc _ _ _).symm

/-- The inverse system `(𝓘^n𝓕^•)` of ideal-power subcomplexes. -/
public abbrev idealPowerComplexFunctor (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) :
    ℕᵒᵖ ⥤ CochainComplex X.Modules ℤ :=
  Functor.ofOpSequence (fun n => (idealPowerComplexSystem I F).transition n)

/-- The morphism of inverse systems `(𝓘^n𝓕^•) ⟶ (𝓘^n𝓖^•)` induced by `𝓕^• ⟶ 𝓖^•`. -/
public def idealPowerComplexMapNatTrans (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) :
    idealPowerComplexFunctor I F ⟶ idealPowerComplexFunctor I G :=
  NatTrans.ofOpSequence (fun n => idealPowerComplexMap I f n) (fun n => by
    rw [Functor.ofOpSequence_map_homOfLE_succ
        (fun m => (idealPowerComplexSystem I F).transition m) n,
      Functor.ofOpSequence_map_homOfLE_succ
        (fun m => (idealPowerComplexSystem I G).transition m) n]
    exact idealPowerComplexMap_transition I f n)

/-- The system of inclusions `(𝓘^n𝓕^•) ⟶ 𝓕^•`. -/
public def idealPowerInclusionNatTrans (I : X.IdealSheafData)
    (F : CochainComplex X.Modules ℤ) :
    idealPowerComplexFunctor I F ⟶ (Functor.const ℕᵒᵖ).obj F :=
  NatTrans.ofOpSequence (fun n => (idealPowerComplexSystem I F).inclusion n) (fun n => by
    rw [Functor.ofOpSequence_map_homOfLE_succ
        (fun m => (idealPowerComplexSystem I F).transition m) n]
    exact ((idealPowerComplexSystem I F).transition_include n).trans
      (Category.comp_id _).symm)
/-! ### `𝓘^n` of a bounded complex of coherent modules is an object of `D^b_Coh(𝒪_X)` -/

/-- An ideal-power subsheaf of a zero sheaf is zero: it is a subsheaf, so its inclusion is a
monomorphism into a zero object. -/
public lemma isZero_idealPowerComplex_X (I : X.IdealSheafData)
    (F : CochainComplex X.Modules ℤ) (n : ℕ) (i : ℤ) (h : IsZero (F.X i)) :
    IsZero (((idealPowerComplexSystem I F).complex n).X i) :=
  ((idealPowerComplexSystem I F).termIso n i).isZero_iff.mpr
    (@IsZero.of_mono _ _ _ _ _ (idealPowerMultiple I n (F.X i)).ι
      (SheafOfModules.Submodule.instMonoι _) h)

/-- **The ideal-power subcomplexes inherit the degree bounds of the complex.** -/
public lemma idealPowerComplex_bounds (I : X.IdealSheafData)
    (F : CochainComplex X.Modules ℤ) (a b : ℤ) (ha : F.IsStrictlyGE a) (hb : F.IsStrictlyLE b)
    (n : ℕ) :
    ((idealPowerComplexSystem I F).complex n).IsStrictlyGE a ∧
      ((idealPowerComplexSystem I F).complex n).IsStrictlyLE b := by
  refine ⟨?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have := ha
    exact isZero_idealPowerComplex_X I F n i (F.isZero_of_isStrictlyGE a i hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have := hb
    exact isZero_idealPowerComplex_X I F n i (F.isZero_of_isStrictlyLE b i hi)

/-- **The ideal-power subcomplexes of a complex of coherent modules have coherent terms.** Each
term is a quasi-coherent submodule of a coherent module on a locally Noetherian scheme. -/
public lemma isCoherent_idealPowerComplex_X [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : CochainComplex X.Modules ℤ) (hF : ∀ i : ℤ, (F.X i).IsCoherent) (n : ℕ) (i : ℤ) :
    (((idealPowerComplexSystem I F).complex n).X i).IsCoherent := by
  have hc : (F.X i).IsCoherent := hF i
  have hq : (F.X i).IsQuasicoherent := isQuasicoherent_of_isCoherent (F.X i)
  exact Stacks.AlgebraicGeometry.IdealPowerSmul.isCoherent_of_isQuasicoherent_submodule
    (F.X i) (idealPowerMultiple I n (F.X i))
    (Stacks.AlgebraicGeometry.IdealPowerComparison.isQuasicoherent_idealPowerMultiple I n
      (F.X i))

/-- **A bounded complex with coherent terms defines an object of `D^b_{Coh}(𝒪_X)`.** The degree
bounds give the cohomological boundedness, and the cohomology sheaves are coherent because
coherence is a weak Serre class, [Stacks, Tag 01BY]. -/
public lemma mem_boundedCoherentDerived_Q_obj (F : CochainComplex X.Modules ℤ)
    (hFge : ∃ a : ℤ, F.IsStrictlyGE a) (hFle : ∃ b : ℤ, F.IsStrictlyLE b)
    (hFcoh : ∀ i : ℤ, (F.X i).IsCoherent) :
    boundedCoherentDerived X (DerivedCategory.Q.obj F) := by
  let P : ObjectProperty X.Modules := fun N => N.IsCoherent
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨a, ha⟩ := hFge
    have := ha
    have : (DerivedCategory.Q.obj F).IsGE a := inferInstance
    exact ⟨a, fun i hi => (DerivedCategory.Q.obj F).isZero_of_isGE a i hi⟩
  · obtain ⟨b, hb⟩ := hFle
    have := hb
    have : (DerivedCategory.Q.obj F).IsLE b := inferInstance
    exact ⟨b, fun i hi => (DerivedCategory.Q.obj F).isZero_of_isLE b i hi⟩
  · intro i
    have hCoker : P (cokernel (F.sc i).f) :=
      P.prop_cokernel (F.sc i).f (hFcoh _) (hFcoh _)
    have hKer : P (kernel (cokernel.desc (F.sc i).f (F.sc i).g (F.sc i).zero)) :=
      P.prop_kernel _ hCoker (hFcoh _)
    have hHom : P (F.homology i) :=
      P.prop_of_iso ((F.sc i).homologyIsoKernelDesc).symm hKer
    exact P.prop_of_iso ((DerivedCategory.homologyFunctorFactors X.Modules i).app F).symm hHom

/-! ### The Deligne system of a bounded complex of coherent modules -/

/-- **The Deligne system `(𝓘^n𝓕^•)` of a bounded complex `𝓕^•` of coherent `𝒪_X`-modules**, for a
quasi-coherent sheaf of ideals `𝓘` cutting out `X ∖ U`. This is the construction of
[Stacks, Tag 0G4L] (2) once the complex has been chosen. -/
public def deligneSystemOfComplex (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X]
    (I : X.IdealSheafData) (hI : (I.support : Set X) = (Set.range j.base)ᶜ)
    (F : CochainComplex X.Modules ℤ)
    (hFge : ∃ a : ℤ, F.IsStrictlyGE a) (hFle : ∃ b : ℤ, F.IsStrictlyLE b)
    (hFcoh : ∀ i : ℤ, (F.X i).IsCoherent) :
    DeligneSystem j where
  idealSheaf := I
  support_idealSheaf := hI
  complex := F
  isCoherent_complex := hFcoh
  exists_isStrictlyGE := hFge
  exists_isStrictlyLE := hFle
  powers := idealPowerComplexSystem I F
  system := (boundedCoherentDerived X).lift (idealPowerComplexFunctor I F ⋙ DerivedCategory.Q)
    (by
      intro n
      obtain ⟨a, ha⟩ := hFge
      obtain ⟨b, hb⟩ := hFle
      exact mem_boundedCoherentDerived_Q_obj _
        ⟨a, (idealPowerComplex_bounds I F a b ha hb n.unop).1⟩
        ⟨b, (idealPowerComplex_bounds I F a b ha hb n.unop).2⟩
        (isCoherent_idealPowerComplex_X I F hFcoh n.unop))
  representation := Iso.refl _
/-! ### The inverse system of cone triangles -/

/-- **The cone triangles of a morphism of inverse systems of complexes**, as an inverse system of
triangles. -/
public def mappingConeTriangleFunctor {C J : Type*} [Category C] [Category J] [Preadditive C]
    [HasBinaryBiproducts C] (P Q : J ⥤ CochainComplex C ℤ) (α : P ⟶ Q) :
    J ⥤ Triangle (CochainComplex C ℤ) where
  obj n := CochainComplex.mappingCone.triangle (α.app n)
  map {n m} t := CochainComplex.mappingCone.triangleMap
    (α.app n) (α.app m) (P.map t) (Q.map t) (α.naturality t).symm
  map_id n := by
    refine Triangle.hom_ext _ _ (P.map_id n) (Q.map_id n) ?_
    change CochainComplex.mappingCone.map (α.app n) (α.app n)
      (P.map (𝟙 n)) (Q.map (𝟙 n)) (α.naturality (𝟙 n)).symm = 𝟙 _
    convert CochainComplex.mappingCone.map_id (α.app n) using 1
    all_goals simp only [P.map_id, Q.map_id]
  map_comp {n m k} t t' := by
    refine Triangle.hom_ext _ _ (P.map_comp t t') (Q.map_comp t t') ?_
    change CochainComplex.mappingCone.map (α.app n) (α.app k)
        (P.map (t ≫ t')) (Q.map (t ≫ t')) (α.naturality (t ≫ t')).symm =
      CochainComplex.mappingCone.map (α.app n) (α.app m)
          (P.map t) (Q.map t) (α.naturality t).symm ≫
        CochainComplex.mappingCone.map (α.app m) (α.app k)
          (P.map t') (Q.map t') (α.naturality t').symm
    simpa only [Functor.map_comp] using
      CochainComplex.mappingCone.map_comp (α.app n) (α.app m) (α.app k)
        (P.map t) (Q.map t) (α.naturality t).symm
        (P.map t') (Q.map t') (α.naturality t').symm

/-- Every triangle of the system of cone triangles is distinguished in the derived category. -/
public lemma mappingConeTriangleFunctor_distinguished {C J : Type*} [Category C] [Category J]
    [Abelian C] [HasDerivedCategory C] (P Q : J ⥤ CochainComplex C ℤ) (α : P ⟶ Q) (n : J) :
    (mappingConeTriangleFunctor P Q α ⋙ DerivedCategory.Q.mapTriangle).obj n ∈
      distTriang (DerivedCategory C) :=
  DerivedCategory.mappingCone_triangle_distinguished (α.app n)

/-- The first vertex of the system of cone triangles is the source system. -/
public def mappingConeTriangleFunctor_π₁Iso {C J : Type*} [Category C] [Category J] [Abelian C]
    [HasDerivedCategory C] (P Q : J ⥤ CochainComplex C ℤ) (α : P ⟶ Q) :
    P ⋙ DerivedCategory.Q ≅
      (mappingConeTriangleFunctor P Q α ⋙ DerivedCategory.Q.mapTriangle) ⋙ Triangle.π₁ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m t
    change DerivedCategory.Q.map (P.map t) ≫ 𝟙 _ = 𝟙 _ ≫ DerivedCategory.Q.map (P.map t)
    simp)

/-- The second vertex of the system of cone triangles is the target system. -/
public def mappingConeTriangleFunctor_π₂Iso {C J : Type*} [Category C] [Category J] [Abelian C]
    [HasDerivedCategory C] (P Q : J ⥤ CochainComplex C ℤ) (α : P ⟶ Q) :
    Q ⋙ DerivedCategory.Q ≅
      (mappingConeTriangleFunctor P Q α ⋙ DerivedCategory.Q.mapTriangle) ⋙ Triangle.π₂ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m t
    change DerivedCategory.Q.map (Q.map t) ≫ 𝟙 _ = 𝟙 _ ≫ DerivedCategory.Q.map (Q.map t)
    simp)

/-- The system of cone triangles of the ideal-power subcomplexes, which is the inverse system of
distinguished triangles of [Stacks, Tag 0G4M]. -/
public abbrev idealPowerConeTriangleFunctor (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) : ℕᵒᵖ ⥤ Triangle (CochainComplex X.Modules ℤ) :=
  mappingConeTriangleFunctor (idealPowerComplexFunctor I F) (idealPowerComplexFunctor I G)
    (idealPowerComplexMapNatTrans I f)

/-! ### The cone of a morphism of ideal-power subcomplexes -/

/-- The morphism `C(α_n)^• ⟶ C(α^•)` of mapping cones induced by the inclusions of the
ideal-power subcomplexes. -/
public def mappingConePowerInclusion (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) (n : ℕ) :
    CochainComplex.mappingCone (idealPowerComplexMap I f n) ⟶ CochainComplex.mappingCone f :=
  CochainComplex.mappingCone.map (idealPowerComplexMap I f n) f
    ((idealPowerComplexSystem I F).inclusion n) ((idealPowerComplexSystem I G).inclusion n)
    (idealPowerComplexMap_comp_inclusion I f n)

/-- The inclusion `C(α_n)^• ⟶ C(α^•)` on the `𝓕`-summand. -/
public lemma mappingConePowerInclusion_inl (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) (n : ℕ) (i : ℤ) :
    (CochainComplex.mappingCone.inl (idealPowerComplexMap I f n)).v (i + 1) i (by lia) ≫
        (mappingConePowerInclusion I f n).f i =
      idealPowerIota I n (F.X (i + 1)) ≫
        (CochainComplex.mappingCone.inl f).v (i + 1) i (by lia) := by
  simp [mappingConePowerInclusion, CochainComplex.mappingCone.map]
  rfl

/-- The inclusion `C(α_n)^• ⟶ C(α^•)` on the `𝓖`-summand. -/
public lemma mappingConePowerInclusion_inr (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) (n : ℕ) (i : ℤ) :
    (CochainComplex.mappingCone.inr (idealPowerComplexMap I f n)).f i ≫
        (mappingConePowerInclusion I f n).f i =
      idealPowerIota I n (G.X i) ≫ (CochainComplex.mappingCone.inr f).f i := by
  simp [mappingConePowerInclusion, CochainComplex.mappingCone.map]
  rfl

/-- The inclusion of the system of cone triangles of the ideal-power subcomplexes into the
constant system at the cone triangle of `α^•`. -/
public def conePowerTriangleInclusion (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) :
    idealPowerConeTriangleFunctor I f ⟶
      (Functor.const ℕᵒᵖ).obj (CochainComplex.mappingCone.triangle f) where
  app n := CochainComplex.mappingCone.triangleMap (idealPowerComplexMap I f n.unop) f
    ((idealPowerComplexSystem I F).inclusion n.unop)
    ((idealPowerComplexSystem I G).inclusion n.unop)
    (idealPowerComplexMap_comp_inclusion I f n.unop)
  naturality {n m} t := by
    apply Triangle.hom_ext
    · exact (idealPowerInclusionNatTrans I F).naturality t
    · exact (idealPowerInclusionNatTrans I G).naturality t
    · refine Eq.trans ?_ (Category.comp_id _).symm
      refine (CochainComplex.mappingCone.map_comp
        (idealPowerComplexMap I f n.unop) (idealPowerComplexMap I f m.unop) f
        ((idealPowerComplexFunctor I F).map t) ((idealPowerComplexFunctor I G).map t)
        ((idealPowerComplexMapNatTrans I f).naturality t).symm
        ((idealPowerComplexSystem I F).inclusion m.unop)
        ((idealPowerComplexSystem I G).inclusion m.unop)
        (idealPowerComplexMap_comp_inclusion I f m.unop)).symm.trans ?_
      congr 1
      · exact ((idealPowerInclusionNatTrans I F).naturality t).trans (Category.comp_id _)
      · exact ((idealPowerInclusionNatTrans I G).naturality t).trans (Category.comp_id _)

/-- The transition `C(α_{n+1})^• ⟶ C(α_n)^•` of the system of cones: the third vertex of the
transition of the system of cone triangles. -/
public def conePowerTransition (I : X.IdealSheafData) {F G : CochainComplex X.Modules ℤ}
    (f : F ⟶ G) (n : ℕ) :
    CochainComplex.mappingCone (idealPowerComplexMap I f (n + 1)) ⟶
      CochainComplex.mappingCone (idealPowerComplexMap I f n) :=
  ((idealPowerConeTriangleFunctor I f).map (homOfLE (n.le_add_right 1)).op).hom₃

/-- The transitions of the system of cones are compatible with the inclusions into `C(α^•)`:
the third-vertex component of the naturality of
`AlgebraicGeometry.DeligneTriangle.conePowerTriangleInclusion`. -/
public lemma conePowerTransition_comp_inclusion (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) (n : ℕ) :
    conePowerTransition I f n ≫ mappingConePowerInclusion I f n =
      mappingConePowerInclusion I f (n + 1) :=
  Eq.trans (congrArg (fun φ => TriangleMorphism.hom₃ φ)
    ((conePowerTriangleInclusion I f).naturality (homOfLE (n.le_add_right 1)).op))
    (Category.comp_id _)

/-- **The identity `C(α_n)^• = 𝓘^nC(α^•)` of [Stacks, Tag 0G4M], in each degree.** Ideal powers
are the values of the additive functor `AlgebraicGeometry.DeligneTriangle.idealPowerFunctor`, so
this is Mathlib's comparison between an additive functor and a mapping cone. -/
public def conePowerTermIso (I : X.IdealSheafData) {F G : CochainComplex X.Modules ℤ}
    (f : F ⟶ G) (n : ℕ) (i : ℤ) :
    (CochainComplex.mappingCone (idealPowerComplexMap I f n)).X i ≅
      idealPowerObj I n ((CochainComplex.mappingCone f).X i) :=
  (CochainComplex.mappingCone.mapHomologicalComplexXIso f (idealPowerFunctor I n) i).symm

/-- The identification `C(α_n)^i ≅ 𝓘^nC(α^•)^i` on the `𝓕`-summand. -/
public lemma conePowerTermIso_hom_inl (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) (n : ℕ) (i : ℤ) :
    (CochainComplex.mappingCone.inl (idealPowerComplexMap I f n)).v (i + 1) i (by lia) ≫
        (conePowerTermIso I f n i).hom =
      (idealPowerFunctor I n).map
        ((CochainComplex.mappingCone.inl f).v (i + 1) i (by lia)) := by
  refine Eq.trans (Preadditive.comp_add _ _ _ _ _ _) ?_
  refine Eq.trans (congrArg₂ (· + ·)
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (fun z => z ≫ (idealPowerFunctor I n).map
          ((CochainComplex.mappingCone.inl f).v (i + 1) i (by lia)))
        (CochainComplex.mappingCone.inl_v_fst_v (idealPowerComplexMap I f n) (i + 1) i rfl))
        (Category.id_comp _)))
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (fun z => z ≫ (idealPowerFunctor I n).map
          ((CochainComplex.mappingCone.inr f).f i))
        (CochainComplex.mappingCone.inl_v_snd_v (idealPowerComplexMap I f n) (i + 1) i (by lia)))
        zero_comp))) ?_
  exact add_zero _

/-- The identification `C(α_n)^i ≅ 𝓘^nC(α^•)^i` on the `𝓖`-summand. -/
public lemma conePowerTermIso_hom_inr (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) (n : ℕ) (i : ℤ) :
    (CochainComplex.mappingCone.inr (idealPowerComplexMap I f n)).f i ≫
        (conePowerTermIso I f n i).hom =
      (idealPowerFunctor I n).map ((CochainComplex.mappingCone.inr f).f i) := by
  refine Eq.trans (Preadditive.comp_add _ _ _ _ _ _) ?_
  refine Eq.trans (congrArg₂ (· + ·)
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (fun z => z ≫ (idealPowerFunctor I n).map
          ((CochainComplex.mappingCone.inl f).v (i + 1) i (by lia)))
        (CochainComplex.mappingCone.inr_f_fst_v (idealPowerComplexMap I f n) i (i + 1) rfl))
        zero_comp))
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (fun z => z ≫ (idealPowerFunctor I n).map
          ((CochainComplex.mappingCone.inr f).f i))
        (CochainComplex.mappingCone.inr_f_snd_v (idealPowerComplexMap I f n) i))
        (Category.id_comp _)))) ?_
  exact zero_add _

/-- The identification of `C(α_n)^•` with `𝓘^nC(α^•)` is compatible with the inclusions into
`C(α^•)`: this is what makes the system of cones the ideal-power system of the single complex
`C(α^•)`. -/
public lemma conePowerTermIso_hom_ι (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) (n : ℕ) (i : ℤ) :
    (conePowerTermIso I f n i).hom ≫
        idealPowerIota I n ((CochainComplex.mappingCone f).X i) =
      (mappingConePowerInclusion I f n).f i := by
  refine CochainComplex.mappingCone.ext_from (idealPowerComplexMap I f n) (i + 1) i rfl ?_ ?_
  · rw [← Category.assoc, conePowerTermIso_hom_inl]
    exact (idealPowerTermMap_comp_ι I n _).trans (mappingConePowerInclusion_inl I f n i).symm
  · rw [← Category.assoc, conePowerTermIso_hom_inr]
    exact (idealPowerTermMap_comp_ι I n _).trans (mappingConePowerInclusion_inr I f n i).symm

/-- The zeroth ideal-power multiple is everything, so its inclusion is invertible. -/
public lemma isIso_idealPowerMultiple_zero_ι (I : X.IdealSheafData) (M : X.Modules) :
    IsIso (idealPowerMultiple I 0 M).ι := by
  rw [idealPowerMultiple_zero I M]
  exact (sheafTopIso M).isIso_hom

/-- Each component of the inclusion `C(α_0)^• ⟶ C(α^•)` is invertible. -/
public lemma isIso_mappingConePowerInclusion_zero_f (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) (i : ℤ) :
    IsIso ((mappingConePowerInclusion I f 0).f i) := by
  have h1 : IsIso (idealPowerMultiple I 0 ((CochainComplex.mappingCone f).X i)).ι :=
    isIso_idealPowerMultiple_zero_ι I _
  exact conePowerTermIso_hom_ι I f 0 i ▸
    (conePowerTermIso I f 0 i ≪≫ @asIso _ _ _ _ _ h1).isIso_hom

/-- The zeroth cone of the system is canonically `C(α^•)` itself. -/
public def conePowerZeroIso (I : X.IdealSheafData) {F G : CochainComplex X.Modules ℤ}
    (f : F ⟶ G) :
    CochainComplex.mappingCone (idealPowerComplexMap I f 0) ≅ CochainComplex.mappingCone f :=
  have := isIso_mappingConePowerInclusion_zero_f I f
  HomologicalComplex.Hom.isoOfComponents
    (fun i => asIso ((mappingConePowerInclusion I f 0).f i))
    (fun i j _ => (mappingConePowerInclusion I f 0).comm i j)

/-- The identification of the zeroth cone with `C(α^•)` is the inclusion. -/
public lemma conePowerZeroIso_hom (I : X.IdealSheafData) {F G : CochainComplex X.Modules ℤ}
    (f : F ⟶ G) : (conePowerZeroIso I f).hom = mappingConePowerInclusion I f 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  rfl

/-- **The ideal-power presentation of the mapping cone whose `n`-th complex is the cone
`C(α_n)^•`.** This is the identity `C(α_n)^• = 𝓘^nC(α^•)` of [Stacks, Tag 0G4M], packaged as the
datum which the `AlgebraicGeometry.DeligneSystem` structure demands: the system of cones *is* the
system of ideal-power subcomplexes of the single complex `C(α^•)`. -/
public def conePowerSystem (I : X.IdealSheafData) {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) :
    IdealPowerComplexSystem I (CochainComplex.mappingCone f) where
  complex n := CochainComplex.mappingCone (idealPowerComplexMap I f n)
  inclusion n := mappingConePowerInclusion I f n
  termIso n i := conePowerTermIso I f n i
  include_f n i := conePowerTermIso_hom_ι I f n i
  transition n := conePowerTransition I f n
  transition_include n := conePowerTransition_comp_inclusion I f n
  zeroIso := conePowerZeroIso I f
  zeroIso_hom := conePowerZeroIso_hom I f

/-- **The third vertex of the system of cone triangles is the system of the cones.** Both are the
inverse sequence of the `C(α_n)^•` with the transitions
`AlgebraicGeometry.DeligneTriangle.conePowerTransition`, which is by definition the third vertex
of the transition of the system of cone triangles, so the comparison is the identity in each
degree and the successor squares hold by definition. -/
public def idealPowerConeTriangle_π₃Iso (I : X.IdealSheafData)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G) :
    Functor.ofOpSequence
        (X := fun m => CochainComplex.mappingCone (idealPowerComplexMap I f m))
        (fun m => conePowerTransition I f m) ≅
      idealPowerConeTriangleFunctor I f ⋙ Triangle.π₃ := by
  have hsucc : ∀ n : ℕ,
      (Functor.ofOpSequence
            (X := fun m => CochainComplex.mappingCone (idealPowerComplexMap I f m))
            (fun m => conePowerTransition I f m)).map
          (homOfLE (n.le_add_right 1)).op ≫ 𝟙 _ =
        𝟙 _ ≫ (idealPowerConeTriangleFunctor I f ⋙ Triangle.π₃).map
          (homOfLE (n.le_add_right 1)).op := by
    intro n
    refine Eq.trans (Category.comp_id _) (Eq.trans ?_ (Category.id_comp _).symm)
    exact Functor.ofOpSequence_map_homOfLE_succ
      (X := fun m => CochainComplex.mappingCone (idealPowerComplexMap I f m))
      (fun m => conePowerTransition I f m) n
  have hsucc' : ∀ n : ℕ,
      (idealPowerConeTriangleFunctor I f ⋙ Triangle.π₃).map
          (homOfLE (n.le_add_right 1)).op ≫ 𝟙 _ =
        𝟙 _ ≫ (Functor.ofOpSequence
            (X := fun m => CochainComplex.mappingCone (idealPowerComplexMap I f m))
            (fun m => conePowerTransition I f m)).map
          (homOfLE (n.le_add_right 1)).op := by
    intro n
    refine Eq.trans (Category.comp_id _) (Eq.trans ?_ (Category.id_comp _).symm)
    exact (Functor.ofOpSequence_map_homOfLE_succ
      (X := fun m => CochainComplex.mappingCone (idealPowerComplexMap I f m))
      (fun m => conePowerTransition I f m) n).symm
  exact
    { hom := NatTrans.ofOpSequence
        (F := Functor.ofOpSequence
          (X := fun m => CochainComplex.mappingCone (idealPowerComplexMap I f m))
          (fun m => conePowerTransition I f m))
        (G := idealPowerConeTriangleFunctor I f ⋙ Triangle.π₃) (fun _ => 𝟙 _) hsucc
      inv := NatTrans.ofOpSequence
        (F := idealPowerConeTriangleFunctor I f ⋙ Triangle.π₃)
        (G := Functor.ofOpSequence
          (X := fun m => CochainComplex.mappingCone (idealPowerComplexMap I f m))
          (fun m => conePowerTransition I f m)) (fun _ => 𝟙 _) hsucc'
      hom_inv_id := NatTrans.ext <| funext fun _ ↦ Category.comp_id _
      inv_hom_id := NatTrans.ext <| funext fun _ ↦ Category.comp_id _ }

/-! ### The Deligne system of the cone -/

/-- **The cone of a morphism of bounded complexes of coherent modules has coherent terms.** In
each degree it is a biproduct of two coherent modules, and coherence is a weak Serre class. -/
public lemma isCoherent_mappingCone_X {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G)
    (hF : ∀ i, (F.X i).IsCoherent) (hG : ∀ i, (G.X i).IsCoherent) (i : ℤ) :
    ((CochainComplex.mappingCone f).X i).IsCoherent := by
  let P : ObjectProperty X.Modules := fun M => M.IsCoherent
  exact P.prop_of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl).symm
    (P.prop_biprod (hF _) (hG _))

/-- **The cone of a morphism of bounded complexes is bounded.** -/
public lemma mappingCone_bounded {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {F G : CochainComplex C ℤ} (f : F ⟶ G)
    (hFge : ∃ a : ℤ, F.IsStrictlyGE a) (hFle : ∃ b : ℤ, F.IsStrictlyLE b)
    (hGge : ∃ a : ℤ, G.IsStrictlyGE a) (hGle : ∃ b : ℤ, G.IsStrictlyLE b) :
    (∃ a : ℤ, (CochainComplex.mappingCone f).IsStrictlyGE a) ∧
      (∃ b : ℤ, (CochainComplex.mappingCone f).IsStrictlyLE b) := by
  obtain ⟨aF, hFge⟩ := hFge
  obtain ⟨bF, hFle⟩ := hFle
  obtain ⟨aG, hGge⟩ := hGge
  obtain ⟨bG, hGle⟩ := hGle
  have := hFge
  have := hGge
  refine ⟨⟨min (aF - 1) aG,
    CochainComplex.isStrictlyGE_mappingCone f aF aG _ (by lia) (by lia)⟩, ?_⟩
  refine ⟨max (bF - 1) bG, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  refine ⟨?_, ?_⟩
  · have := hFle
    exact F.isZero_of_isStrictlyLE bF (i + 1) (by lia)
  · have := hGle
    exact G.isZero_of_isStrictlyLE bG i (by lia)

/-- **The Deligne system of the cone**: the inverse system `(C(α_n)^•)`, which by the identity
`C(α_n)^• = 𝓘^nC(α^•)` is the system of ideal-power subcomplexes of the single bounded complex
`C(α^•)` of coherent modules. -/
public def deligneSystemOfMappingCone (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X]
    (I : X.IdealSheafData) (hI : (I.support : Set X) = (Set.range j.base)ᶜ)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G)
    (hFge : ∃ a : ℤ, F.IsStrictlyGE a) (hFle : ∃ b : ℤ, F.IsStrictlyLE b)
    (hGge : ∃ a : ℤ, G.IsStrictlyGE a) (hGle : ∃ b : ℤ, G.IsStrictlyLE b)
    (hF : ∀ i, (F.X i).IsCoherent) (hG : ∀ i, (G.X i).IsCoherent) :
    DeligneSystem j where
  idealSheaf := I
  support_idealSheaf := hI
  complex := CochainComplex.mappingCone f
  isCoherent_complex := isCoherent_mappingCone_X f hF hG
  exists_isStrictlyGE := (mappingCone_bounded f hFge hFle hGge hGle).1
  exists_isStrictlyLE := (mappingCone_bounded f hFge hFle hGge hGle).2
  powers := conePowerSystem I f
  system := (boundedCoherentDerived X).lift
    (Functor.ofOpSequence (conePowerSystem I f).transition ⋙ DerivedCategory.Q)
    (by
      intro n
      obtain ⟨aF, haF⟩ := hFge
      obtain ⟨bF, hbF⟩ := hFle
      obtain ⟨aG, haG⟩ := hGge
      obtain ⟨bG, hbG⟩ := hGle
      have hFn := idealPowerComplex_bounds I F aF bF haF hbF n.unop
      have hGn := idealPowerComplex_bounds I G aG bG haG hbG n.unop
      have hb := mappingCone_bounded (idealPowerComplexMap I f n.unop)
        ⟨aF, hFn.1⟩ ⟨bF, hFn.2⟩ ⟨aG, hGn.1⟩ ⟨bG, hGn.2⟩
      exact mem_boundedCoherentDerived_Q_obj _ hb.1 hb.2
        (isCoherent_mappingCone_X (idealPowerComplexMap I f n.unop)
          (isCoherent_idealPowerComplex_X I F hF n.unop)
          (isCoherent_idealPowerComplex_X I G hG n.unop)))
  representation := Iso.refl _

/-! ### Restriction to `U` -/

/-- **Away from the support of `𝓘` the inclusion `𝓘^nM ⟶ M` restricts to an isomorphism.** The
ideal is the unit ideal on every affine open disjoint from its support, so `𝓘^nM` has all the
sections of `M` over any open inside the range of `j`. -/
public lemma isIso_restrict_idealPowerMultiple_ι (j : U ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : (I.support : Set X) = (Set.range j.base)ᶜ)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor j).map (idealPowerMultiple I n M).ι) := by
  have htop : ∀ V : U.Opens,
      (idealPowerMultiple I n M).toSubmodule.obj (op (j ''ᵁ V)) = ⊤ := by
    intro V
    refine Stacks.AlgebraicGeometry.IdealPowerComparison.obj_idealPowerMultiple_eq_top I n M ?_
    intro x hx
    rcases hx with ⟨y, -, rfl⟩
    change j.base y ∈ ((I.support : Set X)ᶜ)
    rw [hI]
    exact fun h => h ⟨y, rfl⟩
  set q := (Scheme.Modules.restrictFunctor j).map (idealPowerMultiple I n M).ι with hq
  have happ : ∀ V, IsIso (((Scheme.Modules.toPresheaf U).map q).app V) := by
    intro V
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective
      (fun x : (idealPowerMultiple I n M).toSubmodule.obj (op (j ''ᵁ V.unop)) => x.val)
    refine ⟨Subtype.val_injective, fun x => ⟨⟨x, ?_⟩, rfl⟩⟩
    rw [htop V.unop]
    exact Submodule.mem_top
  have := NatIso.isIso_of_isIso_app ((Scheme.Modules.toPresheaf U).map q)
  exact isIso_of_reflects_iso q (Scheme.Modules.toPresheaf U)

/-- **The inclusion `𝓘^n𝓕^• ⟶ 𝓕^•` becomes an isomorphism of `D(𝒪_U)` after restriction.** -/
public lemma isIso_restrict_idealPowerComplex_inclusion [IsLocallyNoetherian X] (j : U ⟶ X)
    [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : (I.support : Set X) = (Set.range j.base)ᶜ)
    (F : CochainComplex X.Modules ℤ) (hFcoh : ∀ i : ℤ, (F.X i).IsCoherent) (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.map
      (DerivedCategory.Q.map ((idealPowerComplexSystem I F).inclusion n))) := by
  set R := Scheme.Modules.restrictFunctor j with hR
  set i := (idealPowerComplexSystem I F).inclusion n with hi
  have hcomp : ∀ k, IsIso (((R.mapHomologicalComplex (ComplexShape.up ℤ)).map i).f k) := by
    intro k
    have hc : (F.X k).IsCoherent := hFcoh k
    have hq : (F.X k).IsQuasicoherent := isQuasicoherent_of_isCoherent (F.X k)
    exact isIso_restrict_idealPowerMultiple_ι j I hI (F.X k) n
  set q := (R.mapHomologicalComplex (ComplexShape.up ℤ)).map i with hqdef
  have hqiso : IsIso q := by
    have := hcomp
    exact (HomologicalComplex.Hom.isoOfComponents (fun k => asIso (q.f k))
      (fun k l _ => q.comm k l)).isIso_hom
  have he := R.mapDerivedCategoryFactors.hom.naturality i
  have hf : R.mapDerivedCategory.map (DerivedCategory.Q.map i) =
      R.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map q ≫
        R.mapDerivedCategoryFactors.inv.app _ := by
    simpa using congrArg (fun p => p ≫ R.mapDerivedCategoryFactors.inv.app _) he
  rw [hf]
  have := hqiso
  infer_instance

/-- **The restriction of the system of cone triangles to `U` is constant.** The two outer
vertices restrict to the cone triangle of `α^•` because the inclusions of the ideal-power
subcomplexes become isomorphisms, and the third follows by the five lemma. -/
public lemma nonempty_conePowerRestrictIsoConst [IsLocallyNoetherian X] (j : U ⟶ X)
    [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : (I.support : Set X) = (Set.range j.base)ᶜ)
    {F G : CochainComplex X.Modules ℤ} (f : F ⟶ G)
    (hF : ∀ i : ℤ, (F.X i).IsCoherent) (hG : ∀ i : ℤ, (G.X i).IsCoherent) :
    Nonempty ((idealPowerConeTriangleFunctor I f ⋙ DerivedCategory.Q.mapTriangle ⋙
        (Scheme.Modules.restrictFunctor j).mapDerivedCategory.mapTriangle) ≅
      (Functor.const ℕᵒᵖ).obj
        ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.mapTriangle.obj
          (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)))) := by
  set R := (Scheme.Modules.restrictFunctor j).mapDerivedCategory with hR
  set H := DerivedCategory.Q.mapTriangle ⋙ R.mapTriangle with hH
  set inc := conePowerTriangleInclusion I f with hinc
  have hi : ∀ n : ℕᵒᵖ, IsIso (H.map (inc.app n)) := by
    intro n
    have h₁ : IsIso (H.map (inc.app n)).hom₁ :=
      isIso_restrict_idealPowerComplex_inclusion j I hI F hF n.unop
    have h₂ : IsIso (H.map (inc.app n)).hom₂ :=
      isIso_restrict_idealPowerComplex_inclusion j I hI G hG n.unop
    have h₃ := isIso₃_of_isIso₁₂ (H.map (inc.app n))
      (R.map_distinguished _
        (mappingConeTriangleFunctor_distinguished _ _ (idealPowerComplexMapNatTrans I f) n))
      (R.map_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished f)) h₁ h₂
    exact Triangle.isIso_of_isIsos _ h₁ h₂ h₃
  have := hi
  refine ⟨NatIso.ofComponents (fun n => asIso (H.map (inc.app n))) ?_⟩
  intro n m t
  change H.map ((idealPowerConeTriangleFunctor I f).map t) ≫ H.map (inc.app m) =
    H.map (inc.app n) ≫ 𝟙 _
  rw [← H.map_comp, Category.comp_id]
  exact congrArg H.map ((inc.naturality t).trans (Category.comp_id _))

/-- **Two distinguished triangles with isomorphic first morphisms are isomorphic.** This is
`TR3` followed by the fact that a morphism of distinguished triangles which is invertible on the
first two vertices is invertible on the third. -/
public lemma nonempty_triangle_iso_of_mor₁ {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S T : Triangle C) (hS : S ∈ distTriang C) (hT : T ∈ distTriang C)
    (e₁ : S.obj₁ ≅ T.obj₁) (e₂ : S.obj₂ ≅ T.obj₂)
    (h : S.mor₁ ≫ e₂.hom = e₁.hom ≫ T.mor₁) : Nonempty (S ≅ T) := by
  obtain ⟨c, hc₂, hc₃⟩ :=
    complete_distinguished_triangle_morphism S T hS hT e₁.hom e₂.hom h
  set q : S ⟶ T := Triangle.homMk _ _ e₁.hom e₂.hom c h hc₂ hc₃ with hqdef
  have hq₁ : IsIso q.hom₁ := by
    change IsIso e₁.hom
    infer_instance
  have hq₂ : IsIso q.hom₂ := by
    change IsIso e₂.hom
    infer_instance
  have hq₃ : IsIso q.hom₃ := isIso₃_of_isIso₁₂ q hS hT hq₁ hq₂
  have : IsIso q := Triangle.isIso_of_isIsos q hq₁ hq₂ hq₃
  exact ⟨asIso q⟩

/-! ### The input of the construction -/

/-- A **coherent complex model over `X`** for a morphism `α : K ⟶ L` of `D^b_{Coh}(𝒪_U)` along an
open immersion `j : U ⟶ X`: a morphism `α^• : 𝓕^• ⟶ 𝓖^•` of bounded complexes of coherent
`𝒪_X`-modules together with an identification, in `D(𝒪_U)`, of its restriction to `U` with `α`.

This is what the first two paragraphs of the proof of [Stacks, Tag 0G4M] produce before the
construction begins: `K` and `L` are extended to objects of `D^b_{Coh}(𝒪_X)` by
[Stacks, Tag 0G4L] (2), resting on [Stacks, Tag 0G48]; the morphism `α` is the restriction of a
morphism of `D^b_{Coh}(𝒪_X)` by [Stacks, Tag 0G2H]; and that morphism is represented by a
morphism of bounded complexes of coherent modules by [Stacks, Tag 0FDB]. -/
public structure CoherentComplexModel (j : U ⟶ X) [IsOpenImmersion j]
    {K L : BoundedCoherentDerived U} (α : K ⟶ L) where
  /-- A complex of `𝒪_X`-modules restricting to `K`. -/
  source : CochainComplex X.Modules ℤ
  /-- A complex of `𝒪_X`-modules restricting to `L`. -/
  target : CochainComplex X.Modules ℤ
  /-- A morphism of complexes restricting to `α`. -/
  map : source ⟶ target
  /-- The source vanishes in low degrees. -/
  exists_isStrictlyGE_source : ∃ a : ℤ, source.IsStrictlyGE a
  /-- The source vanishes in high degrees. -/
  exists_isStrictlyLE_source : ∃ b : ℤ, source.IsStrictlyLE b
  /-- The target vanishes in low degrees. -/
  exists_isStrictlyGE_target : ∃ a : ℤ, target.IsStrictlyGE a
  /-- The target vanishes in high degrees. -/
  exists_isStrictlyLE_target : ∃ b : ℤ, target.IsStrictlyLE b
  /-- The terms of the source are coherent. -/
  isCoherent_source : ∀ i : ℤ, (source.X i).IsCoherent
  /-- The terms of the target are coherent. -/
  isCoherent_target : ∀ i : ℤ, (target.X i).IsCoherent
  /-- The restriction of the source to `U` is `K`. -/
  sourceIso : (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj
    (DerivedCategory.Q.obj source) ≅ (boundedCoherentDerived U).ι.obj K
  /-- The restriction of the target to `U` is `L`. -/
  targetIso : (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj
    (DerivedCategory.Q.obj target) ≅ (boundedCoherentDerived U).ι.obj L
  /-- Under those identifications the restriction of the morphism of complexes is `α`. -/
  restrict_map : (Scheme.Modules.restrictFunctor j).mapDerivedCategory.map
      (DerivedCategory.Q.map map) ≫ targetIso.hom =
    sourceIso.hom ≫ (boundedCoherentDerived U).ι.map α

end AlgebraicGeometry.DeligneTriangle

end
