module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.HypercohomologyBound07QA

/-!
# The two hypotheses of the [Stacks, Tag 07QA] bounds, reduced

`SmallSite/HypercohomologyBound07QA.lean` proves the kernel and the cokernel bounds of
[Stacks, Tag 07QA] on Zariski hypercohomology groups, carrying two hypotheses:

* `hann : ...SmallSite.Annihilation07Q9 S' q (derivedZariskiComparison ...)`, the conclusion of
  [Stacks, Tag 07Q9], whose content is [Stacks, Proposition 07LG];
* `hmono`, for the cokernel half only, that `ℋ^0` of the comparison map of [Stacks, Tag 07Q9] is
  a monomorphism.

This file reduces both to statements that are smaller than what they stood in for, and in the
first case proves that the reduction loses nothing by stating it as an **iff**.

## What is reduced, and to what

**The annihilation.**  `Annihilation07Q9` quantifies over *every* distinguished triangle on the
comparison map, which is how the source's "the distinguished triangle" must be read.
`annihilation07Q9_iff_of_distTriang` shows that this quantification is free: for one chosen
distinguished triangle on the map, the annihilation of the cohomology sheaves of *its* third term
already implies the annihilation for every other one.  The two triangles are isomorphic by
`CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂` applied with the identity on the first two
terms, and "annihilated by `q`" is invariant under isomorphism.  So a proof of
[Stacks, Tag 07Q9] has only to produce one cone and bound it, and a consumer of `hann` has the
statement for all of them; the hypothesis block is machine-checked to agree with the weaker
single-triangle form.

**The monomorphism.**  This one is reduced all the way to a statement about a map of *sheaves* on
the crystalline site, namely to

`Mono (...SmallSite.crisUnit S S' fS fX hf F)`,

injectivity of the adjunction unit `ℱ ⟶ f_{cris, *}f_cris^{-1}ℱ`.  That is exactly the input the
module documentation of `SmallSite/AlphaPCoverTriangle.lean` names as the one the geometry
supplies — it holds for an iterated `α_p`-cover because `D ⟶ D'` of [Stacks, Tag 07N1] is a split
injection of `D`-modules — and it is the only thing the cokernel half of [Stacks, Tag 07QA] now
owes besides the annihilation.  **This is a reduction and not a discharge**, and no tag attribute
is placed anywhere in this file.

What the library has towards that injectivity, so that it is not looked for twice: the homotopy
inverse of [Stacks, Tag 07N1] for a single `p`-th root extension is proved, as
`Crystalline.exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/PthRootFormsDecomposition.lean`, which
carries `@[stacks 07N1 "the uncompleted extension B → B[z]⟨ξ⟩/(ξ - (z^p - λ)), with the
decomposition (07Q1) of its divided power one-forms and the identity dξ^[n] = ξ^[n-1] dξ both
proved"]`.
That is a statement about the de Rham complexes of a pair over the *uncompleted* extension
`B → B[z]⟨ξ⟩/(ξ - (z^p - λ))`, with the maps composing to multiplication by `p` up to homotopy;
it is not the splitness of `D ⟶ D'` as a map of `D`-modules.  That splitness *is* proved, for a
single `p`-th root extension and over the `p`-adic completions, as
`Crystalline.PthRootExtension.injective_completedToPrimeRing` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/CompletedPthRootExtension.lean`,
which also carries the homotopy inverse across the completion as
`Crystalline.exists_completedHomotopyInverse_pthRootExtension_dividedPowerDifferentials`.  The
passage from the splitness to the sheaf and the globalisation over the chain of `α_p`-covers is
done for the module unit of a crystal in quasi-coherent modules, the form [Stacks, Tag 07QA]
uses: `...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover` of
`SmallSite/ModuleUnitMonoRings07QA.lean`.  This file does not derive the abelian
`Mono (...SmallSite.crisUnit ...)` for an arbitrary abelian sheaf.  The injectivity also appears
as the field `unit_mono_of_isIteratedAlphaPCover` of the comparison structure of
the statement of record for Stacks 07Q9, i.e. as data and not as a theorem.

The reduction is in three steps, each of them unconditional:

1. `mono_homologyMap_derivedZariskiComparison_iff` strips the carried commutation `sq` of the
   square of topoi off the hypothesis: `derivedZariskiComparison` is `Ru_{X/S, *}` of the derived
   unit followed by a component of the *natural isomorphism* `derivedZariskiSquare sq`, and
   composing with an isomorphism neither creates nor destroys a monomorphism.  So the hypothesis
   does not depend on which commutation is used, and in particular not on
   `...SmallSite.crisZariskiSquare` being the canonical one.
2. `mono_homologyFunctor_derivedZariskiDirectImage_map_iff` identifies `ℋ^0 ∘ Ru_{X/S, *}` on a
   sheaf placed in degree zero with the underived `u_{X/S, *}`, by
   `...SmallSite.higherZariskiDirectImageZeroIso` (`R^0u_{X/S, *} ≅ u_{X/S, *}`, which holds
   because `u_{X/S, *}` is a right adjoint, hence left exact).  Combined with left exactness
   again, which makes `u_{X/S, *}` preserve monomorphisms, this turns `Mono (crisUnit)` into the
   first half of what step 3 needs.
3. `Stacks.Cohomology.isIso_homologyFunctor_rightDerivedFunctorPlus_map_singleRightDerivedUnit_app`
   disposes of the second half, the degree-zero comparison `f_{cris, *}ℱ'[0] ⟶ Rf_{cris, *}ℱ'[0]`
   that `...SmallSite.derivedCrisUnit` is built from.  It is **not** an isomorphism, since
   `Rf_{cris, *}` has higher cohomology, but it is an isomorphism on `ℋ^0`, and this file proves
   that applying another right derived functor first does not change that.  The argument is
   pure homological algebra: the cone of the comparison is concentrated in degrees `≥ 1`, because
   the comparison is an isomorphism on `ℋ^0` for a left exact functor ([Stacks, Tag 05TD]
   part (3), available here as
   `CategoryTheory.Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits`)
   and its source is concentrated in degree `0`; a right derived functor moves cohomology to the
   right, so the cone stays in degrees `≥ 1`, and a triangle whose third term is concentrated in
   degrees `≥ a + 1` has `ℋ^a` of its first map invertible.

## Main results

* `Stacks.Triangulated.isGE_obj₃_of_isIso_homologyMap` — the cone of a map which is invertible on
  `ℋ^a`, out of an object concentrated in degrees `≤ a`, is concentrated in degrees `≥ a + 1`.
* `Stacks.Triangulated.isIso_homologyMap_mor₁_of_isGE_obj₃` — conversely, if the third term of a
  distinguished triangle is concentrated in degrees `≥ a + 1` then `ℋ^a` of its first map is
  invertible.
* `Stacks.Cohomology.isIso_homologyFunctor_singleRightDerivedUnit_app` — for a left exact `Φ` the
  canonical map `Φ(M)[0] ⟶ RΦ(M[0])` is invertible on `ℋ^0`.
* `Stacks.Cohomology.isIso_homologyFunctor_rightDerivedFunctorPlus_map_singleRightDerivedUnit_app`
  — and it stays invertible on `ℋ^0` after another right derived functor is applied.
* `annihilation07Q9_iff_of_distTriang` — **the annihilation of [Stacks, Tag 07Q9] for every
  distinguished triangle is implied by its annihilation for one.**
* `mono_homologyMap_derivedZariskiComparison_iff` — the `hmono` hypothesis does not see the
  carried commutation of the square of topoi.
* `mono_homologyMap_derivedZariskiComparison_of_mono_crisUnit` — **`hmono` follows from
  `Mono (crisUnit)`**.
* `exists_hypercohomologyMap_eq_pow_smul_07QA_of_mono_crisUnit` — the cokernel bound of
  [Stacks, Tag 07QA] with `hmono` replaced by `Mono (crisUnit)`.  Together with
  `annihilation07Q9_iff_of_distTriang` this is the whole hypothesis block of that bound reduced to
  [Stacks, Proposition 07LG] for one cone and to [Stacks, Tag 07N1].

## No tag is placed

No tag attribute is placed here.  Every statement about the comparison map of
[Stacks, Tag 07Q9] below is either an unconditional reduction of a hypothesis or takes
`Annihilation07Q9` as an input, for an arbitrary abelian sheaf.  The tags are proved for a crystal
in quasi-coherent modules: [Stacks, Tag 07Q9] is
`...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` of `SmallSite/AlphaPCover07Q9Main.lean`
(resting on [Stacks, Proposition 07LG]), and [Stacks, Tag 07QA] is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover` of
`SmallSite/CrisCohomologyBound07QAMain.lean`, whose cokernel half uses [Stacks, Tag 07N1] through
`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover`.

## References

* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.22.1, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

universe v w w' u

noncomputable section

namespace Stacks.Triangulated

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- **The cone of a map which is invertible on `ℋ^a` is concentrated in degrees `≥ a + 1`.**  Let
`A ⟶ B ⟶ E ⟶ A⟦1⟧` be distinguished in `D(𝒜)` with `A` concentrated in degrees `≤ a`, `B` in
degrees `≥ a` and `E` in degrees `≥ a - 1`, and suppose `ℋ^a(A) ⟶ ℋ^a(B)` is an isomorphism.
Then `E` is concentrated in degrees `≥ a + 1`.

Injectivity already gives degrees `≥ a` (`isGE_obj₃_of_mono_homologyMap`); surjectivity kills
`ℋ^a(E)` as well, since `ℋ^a(B) ⟶ ℋ^a(E)` is then zero by exactness and the connecting map
`ℋ^a(E) ⟶ ℋ^{a + 1}(A)` lands in a zero object because `A` is concentrated in degrees `≤ a`. -/
theorem isGE_obj₃_of_isIso_homologyMap (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang (DerivedCategory 𝒜)) (a b : ℤ) (hb : a + 1 = b)
    [T.obj₁.IsLE a] [T.obj₂.IsGE a] [T.obj₃.IsGE (a - 1)]
    (hiso : IsIso ((DerivedCategory.homologyFunctor 𝒜 a).map T.mor₁)) :
    T.obj₃.IsGE b := by
  have := hiso
  have : T.obj₃.IsGE a := isGE_obj₃_of_mono_homologyMap T hT a inferInstance
  rw [DerivedCategory.isGE_iff]
  intro j hj
  by_cases hja : j < a
  · exact DerivedCategory.isZero_of_isGE T.obj₃ a j hja
  · have hja' : j = a := by omega
    rw [hja']
    exact (DerivedCategory.HomologySequence.exact₃ T hT a (a + 1) rfl).isZero_X₂
      ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT a).1 inferInstance)
      ((DerivedCategory.isZero_of_isLE T.obj₁ a (a + 1) (by omega)).eq_of_tgt _ _)

/-- **A triangle whose third term is concentrated in degrees `≥ a + 1` has `ℋ^a` of its first map
invertible.**  Both the kernel and the cokernel of `ℋ^a(A) ⟶ ℋ^a(B)` are measured by the
cohomology of `E` in degrees `a - 1` and `a`, and both of those vanish. -/
theorem isIso_homologyMap_mor₁_of_isGE_obj₃ (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang (DerivedCategory 𝒜)) (a b : ℤ) (hb : a + 1 = b) [T.obj₃.IsGE b] :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 a).map T.mor₁) := by
  have : Mono ((DerivedCategory.homologyFunctor 𝒜 a).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (a - 1) a (by omega)).2
      ((DerivedCategory.isZero_of_isGE T.obj₃ b (a - 1) (by omega)).eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor 𝒜 a).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT a).2
      ((DerivedCategory.isZero_of_isGE T.obj₃ b a (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end

end Stacks.Triangulated

namespace Stacks.Cohomology

section SingleUnit

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (Φ : A ⥤ B) [Φ.Additive] [EnoughInjectives A]

/-- **The canonical map `Φ(M)[0] ⟶ RΦ(M[0])` is invertible on `ℋ^0` for a left exact `Φ`.**  This
is [Stacks, Tag 05TD] part (3), the statement that `Φ ⟶ R^0Φ` is an isomorphism exactly for a left
exact `Φ`, read through the two coherence isomorphisms out of which
`Stacks.Cohomology.singleRightDerivedUnit` is assembled. -/
theorem isIso_homologyFunctor_singleRightDerivedUnit_app [PreservesFiniteLimits Φ] (M : A) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map ((singleRightDerivedUnit Φ).app M)) := by
  have := (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
    Φ Φ.rightDerivedFunctorPlus Φ.rightDerivedFunctorPlusUnith).2.2.2 ‹_› M
  rw [singleRightDerivedUnit_app, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **It stays invertible on `ℋ^0` after a further right derived functor.**  For `Φ : 𝒜 ⥤ ℬ`
additive and left exact with `𝒜` having enough injectives, and `Ψ : ℬ ⥤ 𝒞` additive with `ℬ`
having enough injectives, `ℋ^0(RΨ(Φ(M)[0] ⟶ RΦ(M[0])))` is an isomorphism.

The cone of `Φ(M)[0] ⟶ RΦ(M[0])` is concentrated in degrees `≥ 1`: both ends are concentrated in
degrees `≥ 0`, so it is concentrated in degrees `≥ -1`, and
`Stacks.Triangulated.isGE_obj₃_of_isIso_homologyMap` improves that to `≥ 1` using
`isIso_homologyFunctor_singleRightDerivedUnit_app` and the concentration of `Φ(M)[0]` in degrees
`≤ 0`.  Then `RΨ` of the cone is still concentrated in degrees `≥ 1`
(`CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`), and
`Stacks.Triangulated.isIso_homologyMap_mor₁_of_isGE_obj₃` concludes.

Note that no compatibility of `RΨ ∘ RΦ` with `R(Ψ ∘ Φ)` is used, and `Φ` is not asked to preserve
injective objects. -/
theorem isIso_homologyFunctor_rightDerivedFunctorPlus_map_singleRightDerivedUnit_app
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [PreservesFiniteLimits Φ]
    [EnoughInjectives B] (Ψ : B ⥤ C) [Ψ.Additive] (M : A) :
    IsIso ((DerivedCategory.Plus.homologyFunctor C 0).map
      (Ψ.rightDerivedFunctorPlus.map ((singleRightDerivedUnit Φ).app M))) := by
  obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle ((singleRightDerivedUnit Φ).app M)
  have hT' : (DerivedCategory.Plus.ι (C := B)).mapTriangle.obj
      (Triangle.mk ((singleRightDerivedUnit Φ).app M) v w) ∈ distTriang (DerivedCategory B) :=
    DerivedCategory.Plus.ι.map_distinguished _ hT
  have : (Φ.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor A 0).obj M)).IsGE 0 :=
    Functor.isGE_rightDerivedFunctorPlus_obj Φ _ 0
  have : ((DerivedCategory.Plus.ι (C := B)).mapTriangle.obj
      (Triangle.mk ((singleRightDerivedUnit Φ).app M) v w)).obj₁.IsLE 0 := inferInstanceAs
    ((DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor B 0).obj (Φ.obj M))).IsLE 0)
  have : ((DerivedCategory.Plus.ι (C := B)).mapTriangle.obj
      (Triangle.mk ((singleRightDerivedUnit Φ).app M) v w)).obj₁.IsGE 0 := inferInstanceAs
    ((DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor B 0).obj (Φ.obj M))).IsGE 0)
  have : ((DerivedCategory.Plus.ι (C := B)).mapTriangle.obj
      (Triangle.mk ((singleRightDerivedUnit Φ).app M) v w)).obj₂.IsGE 0 := inferInstanceAs
    ((DerivedCategory.Plus.ι.obj (Φ.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor A 0).obj M))).IsGE 0)
  have := Stacks.Triangulated.isGE_obj₃_sub_one _ hT' 0
  have : ((DerivedCategory.Plus.ι (C := B)).mapTriangle.obj
      (Triangle.mk ((singleRightDerivedUnit Φ).app M) v w)).obj₃.IsGE 1 :=
    Stacks.Triangulated.isGE_obj₃_of_isIso_homologyMap _ hT' 0 1 (by omega)
      (isIso_homologyFunctor_singleRightDerivedUnit_app Φ M)
  have : Z.IsGE 1 := (DerivedCategory.Plus.isGE_ι_obj_iff Z 1).1 ‹_›
  have hU : (DerivedCategory.Plus.ι (C := C)).mapTriangle.obj
      (Ψ.rightDerivedFunctorPlus.mapTriangle.obj
        (Triangle.mk ((singleRightDerivedUnit Φ).app M) v w)) ∈ distTriang (DerivedCategory C) :=
    DerivedCategory.Plus.ι.map_distinguished _
      (Ψ.rightDerivedFunctorPlus.map_distinguished _ hT)
  have : (Ψ.rightDerivedFunctorPlus.obj Z).IsGE 1 :=
    Functor.isGE_rightDerivedFunctorPlus_obj Ψ Z 1
  have : ((DerivedCategory.Plus.ι (C := C)).mapTriangle.obj
      (Ψ.rightDerivedFunctorPlus.mapTriangle.obj
        (Triangle.mk ((singleRightDerivedUnit Φ).app M) v w))).obj₃.IsGE 1 := inferInstanceAs
    ((DerivedCategory.Plus.ι.obj (Ψ.rightDerivedFunctorPlus.obj Z)).IsGE 1)
  exact Stacks.Triangulated.isIso_homologyMap_mor₁_of_isGE_obj₃ _ hU 0 1 (by omega)

end SingleUnit

end Stacks.Cohomology

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-- Composing with an isomorphism on the right neither creates nor destroys a monomorphism.  The
invertibility is an explicit argument rather than an instance, so that a caller may hand it over
in a context where instance search would not find it. -/
theorem mono_comp_iff_of_isIso_snd {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hg : IsIso g) : Mono (f ≫ g) ↔ Mono f :=
  have := hg
  ⟨fun _ => mono_of_mono f g, fun _ => inferInstance⟩

open Stacks.Cohomology

/-! ### The annihilation of [Stacks, Tag 07Q9] has to be checked for one cone only -/

section Annihilation

variable (S' : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

/-- **One distinguished triangle suffices for `Annihilation07Q9`.**  Fix a distinguished triangle
`A ⟶ B ⟶ E₀ ⟶ A⟦1⟧` on `α`.  Then `α` satisfies the conclusion of [Stacks, Tag 07Q9] — the
cohomology sheaves of the third term of *every* distinguished triangle on `α` are annihilated by
`q` — if and only if the cohomology sheaves of `E₀` are.

So the quantification over all triangles in `...SmallSite.Annihilation07Q9` costs nothing: a proof
of [Stacks, Tag 07Q9] has only to produce one cone and bound it.  Two distinguished triangles on
the same morphism are isomorphic by `CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂` applied
with the identity on the first two terms — this is the five lemma of [Stacks, Tag 014A] — and
`q • 𝟙` vanishing is invariant under isomorphism. -/
theorem annihilation07Q9_iff_of_distTriang (q : ℕ)
    {A B E₀ : DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})}
    (α : A ⟶ B) (v₀ : B ⟶ E₀) (w₀ : E₀ ⟶ A⟦(1 : ℤ)⟧)
    (hT₀ : Triangle.mk α v₀ w₀ ∈
      distTriang (DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}))) :
    Annihilation07Q9 S' q α ↔
      ∀ j : ℤ, (q : ℤ) • 𝟙 ((DerivedCategory.Plus.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).obj E₀) = 0 :=
  ⟨fun h j => h E₀ v₀ w₀ hT₀ j, fun h E v wE hT j =>
    Stacks.Algebraization.smul_id_eq_zero_of_iso (q : ℤ)
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).mapIso
          (Triangle.π₃.mapIso (isoTriangleOfIso₁₂ (Triangle.mk α v wE) (Triangle.mk α v₀ w₀)
            hT hT₀ (Iso.refl A) (Iso.refl B) (by simp)))) (h j)⟩

/-- **`Annihilation07Q9` is implied by the existence of one cone with `q`-annihilated cohomology
sheaves.**  The form in which a proof of [Stacks, Tag 07Q9] would supply it. -/
theorem annihilation07Q9_of_exists (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})} (α : A ⟶ B)
    (h : ∃ (E₀ : DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}))
      (v₀ : B ⟶ E₀) (w₀ : E₀ ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk α v₀ w₀ ∈
          distTriang (DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})) ∧
        ∀ j : ℤ, (q : ℤ) • 𝟙 ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).obj E₀) = 0) :
    Annihilation07Q9 S' q α := by
  obtain ⟨E₀, v₀, w₀, hT₀, hE₀⟩ := h
  exact (annihilation07Q9_iff_of_distTriang S' q α v₀ w₀ hT₀).2 hE₀

end Annihilation

/-! ### The monomorphism hypothesis of the cokernel half, reduced to the crystalline unit -/

section Mono

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

/-- **`ℋ^0 ∘ Ru_{X/S, *}` on a sheaf placed in degree zero is the underived `u_{X/S, *}`**, in the
form a monomorphism hypothesis consumes it.  This is `R^0u_{X/S, *} ≅ u_{X/S, *}`
(`...SmallSite.higherZariskiDirectImageZeroIso`), which holds because `u_{X/S, *}` is a right
adjoint and hence left exact. -/
theorem mono_homologyFunctor_derivedZariskiDirectImage_map_iff
    {F G : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}} (g : F ⟶ G) :
    Mono ((DerivedCategory.Plus.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
      ((derivedZariskiDirectImage S').map g)) ↔ Mono ((zariskiDirectImage S').map g) := by
  have e : higherZariskiDirectImage S' 0 ≅ zariskiDirectImage S' :=
    higherZariskiDirectImageZeroIso S'
  refine ⟨fun h => ?_, fun _ => ?_⟩
  · have : Mono ((higherZariskiDirectImage S' 0).map g) := h
    rw [← NatIso.naturality_1 e g]
    exact @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ (e.app F).isIso_inv) _
      (@mono_comp _ _ _ _ _ _ this _ (@IsIso.mono_of_iso _ _ _ _ _ (e.app G).isIso_hom))
  · change Mono ((higherZariskiDirectImage S' 0).map g)
    rw [← NatIso.naturality_1 e.symm g]
    exact @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ (e.symm.app F).isIso_inv) _
      (@mono_comp _ _ _ _ _ _ ‹Mono ((zariskiDirectImage S').map g)› _
        (@IsIso.mono_of_iso _ _ _ _ _ (e.symm.app G).isIso_hom))

include hf

/-- **The monomorphism hypothesis of the cokernel half does not see the commutation of the square
of topoi.**  `...SmallSite.derivedZariskiComparison sq` is `Ru_{X/S, *}` of
`...SmallSite.derivedCrisUnit` followed by a component of the natural *isomorphism*
`...SmallSite.derivedZariskiSquare sq`, so composing with it neither creates nor destroys a
monomorphism on `ℋ^0`.  In particular the hypothesis is the same for every commutation `sq`, and
nothing is gained or lost by forming the comparison with the canonical
`...SmallSite.crisZariskiSquare`. -/
theorem mono_homologyMap_derivedZariskiComparison_iff
    (sq : CrisZariskiSquare S S' fS fX hf)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :
    Mono ((DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map (DerivedCategory.Plus.ι.map
      (derivedZariskiComparison S S' fS fX hf sq F))) ↔
      Mono ((DerivedCategory.Plus.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
          ((derivedZariskiDirectImageFunctor S').map (derivedCrisUnit S S' fS fX hf F))) := by
  have heq : (DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map (DerivedCategory.Plus.ι.map
          (derivedZariskiComparison S S' fS fX hf sq F)) =
      (DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
            ((derivedZariskiDirectImageFunctor S').map (derivedCrisUnit S S' fS fX hf F)) ≫
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
            ((derivedZariskiSquare S S' fS fX hf sq).hom.app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
                  (crisPullback S S' fS fX hf F))) := by
    conv_rhs => rw [← Functor.map_comp]
    rfl
  rw [heq]
  exact mono_comp_iff_of_isIso_snd _ _ ((DerivedCategory.Plus.homologyFunctor
    (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).mapIso
      ((derivedZariskiSquare S S' fS fX hf sq).app _)).isIso_hom

/-- **The monomorphism hypothesis of the cokernel half of [Stacks, Tag 07QA] follows from
injectivity of the crystalline adjunction unit.**  If `ℱ ⟶ f_{cris, *}f_cris^{-1}ℱ` is a
monomorphism then so is `ℋ^0` of the comparison map `Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}ℱ'` of
[Stacks, Tag 07Q9].

Unconditional apart from `hmono`: the square of topoi drops out by
`mono_homologyMap_derivedZariskiComparison_iff`, the derived unit splits as `u_{X/S, *}` of the
underived unit followed by the degree-zero comparison `f_{cris, *}ℱ'[0] ⟶ Rf_{cris, *}ℱ'[0]`, the
first of those is a monomorphism because `u_{X/S, *}` is left exact (so `R^0u_{X/S, *}` is
`u_{X/S, *}` and monomorphisms are preserved) and the second is an *isomorphism* on `ℋ^0` by
`Stacks.Cohomology.isIso_homologyFunctor_rightDerivedFunctorPlus_map_singleRightDerivedUnit_app`.

**`hmono` is not discharged here, only reduced**: the injectivity of the crystalline unit for an
iterated `α_p`-cover is the splitness of `D ⟶ D'` of [Stacks, Tag 07N1].  That splitness is proved,
for a single `p`-th root extension and over the `p`-adic completions, as
`Crystalline.PthRootExtension.injective_completedToPrimeRing`, and the passage from it to the
injectivity of `u_{X/S, *}` of the module unit of a crystal in quasi-coherent modules is
`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover`. -/
theorem mono_homologyMap_derivedZariskiComparison_of_mono_crisUnit
    (sq : CrisZariskiSquare S S' fS fX hf)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hmono : Mono (crisUnit S S' fS fX hf F)) :
    Mono ((DerivedCategory.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map (DerivedCategory.Plus.ι.map
        (derivedZariskiComparison S S' fS fX hf sq F))) := by
  rw [mono_homologyMap_derivedZariskiComparison_iff S S' fS fX hf sq F]
  have := hmono
  have hmono' : Mono ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
        ((derivedZariskiDirectImageFunctor S').map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) 0).map
              (crisUnit S S' fS fX hf F)))) :=
    (mono_homologyFunctor_derivedZariskiDirectImage_map_iff S'
      (crisUnit S S' fS fX hf F)).2 inferInstance
  have hiso : IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
        ((derivedZariskiDirectImageFunctor S').map
          ((singleRightDerivedUnit (crisDirectImage S S' fS fX hf)).app
            (crisPullback S S' fS fX hf F)))) :=
    isIso_homologyFunctor_rightDerivedFunctorPlus_map_singleRightDerivedUnit_app
      (crisDirectImage S S' fS fX hf) (zariskiDirectImage S') (crisPullback S S' fS fX hf F)
  have heq : (DerivedCategory.Plus.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
          ((derivedZariskiDirectImageFunctor S').map (derivedCrisUnit S S' fS fX hf F)) =
      (DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
            ((derivedZariskiDirectImageFunctor S').map
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) 0).map
                  (crisUnit S S' fS fX hf F))) ≫
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
            ((derivedZariskiDirectImageFunctor S').map
              ((Stacks.Cohomology.singleRightDerivedUnit
                (crisDirectImage S S' fS fX hf)).app (crisPullback S S' fS fX hf F))) := by
    conv_rhs => rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  rw [heq]
  exact (mono_comp_iff_of_isIso_snd _ _ hiso).2 hmono'

end Mono

/-! ### The cokernel bound of [Stacks, Tag 07QA] with the reduced hypothesis -/

section Bound

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

include hf

/-- **The cokernel half of [Stacks, Tag 07QA] on Zariski hypercohomology groups, with the
monomorphism hypothesis replaced by injectivity of the crystalline unit.**  Given the
conclusion of [Stacks, Tag 07Q9] and that `ℱ ⟶ f_{cris, *}f_cris^{-1}ℱ` is a monomorphism,
`q^{i + 1}` times any class in `H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')` is in the image of

`H^i(X_Zar, Ru_{X/S, *}ℱ) ⟶ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`.

This is `...SmallSite.exists_hypercohomologyMap_eq_pow_smul_07QA` with its second hypothesis
supplied by `mono_homologyMap_derivedZariskiComparison_of_mono_crisUnit`, so its two inputs are
the annihilation of [Stacks, Tag 07Q9] (`Annihilation07Q9`, for a single cone by
`annihilation07Q9_of_exists`) and the injectivity of the abelian unit.  No tag attribute is placed
on this lemma; [Stacks, Tag 07QA] is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover`. -/
theorem exists_hypercohomologyMap_eq_pow_smul_07QA_of_mono_crisUnit (q i : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hann : Annihilation07Q9 S' q
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))
    (hmono : Mono (crisUnit S S' fS fX hf F))
    (y : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedZariskiGlobalSectionsFunctor S').obj
        ((derivedZariskiPushforwardFunctor S S' fX).obj
          ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F))))) :
    ∃ x, ((q : ℤ) ^ (i + 1)) • y =
      zariskiHypercohomologyComparisonMap S S' fS fX hf F i x :=
  exists_hypercohomologyMap_eq_pow_smul_07QA S S' fS fX hf q i F hann
    (mono_homologyMap_derivedZariskiComparison_of_mono_crisUnit S S' fS fX hf
      (crisZariskiSquare S S' fS fX hf) F hmono) y

end Bound

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
