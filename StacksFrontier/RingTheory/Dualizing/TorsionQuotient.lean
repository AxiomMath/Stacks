module

public import StacksFrontier.AlgebraicGeometry.Duality.DivideByTorsion
public import StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessIsLocal

/-!
# Local cohomology of a module modulo its ideal-power torsion

Let `A` be a commutative ring, let `I ⊆ A` be a finitely generated ideal, let `M` be an
`A`-module and let `Z = V(I)` be the closed subset of `Spec(A)` cut out by `I`. Two local
cohomology theories are attached to this data: `H^p_I`, the cohomology of derived `I`-power
torsion `RΓ_I`, and `H^p_Z`, the cohomology of `RΓ_Z`, the right adjoint of the inclusion of
the objects of `D(A)` with `I`-power-torsion cohomology.

In degree zero the two agree, both being the `I`-power-torsion submodule `N = M[I^∞]`, and the
identification is compatible with the canonical maps down to `M`. Writing `M' = M/N`, the
quotient has no zeroth local cohomology of either kind, the submodule `N` has no higher local
cohomology of either kind, and the quotient map `M ⟶ M'` induces an isomorphism on both
theories in every positive degree.

## Main results

* `Stacks.Duality.idealLocalCohomology_zero_iso_torsion` — `H^0_I(M)` is `M[I^∞]`.
* `Stacks.Duality.idealLocalCohomology_zero_iso_supportLocalCohomology_zero` — `H^0_I(M)` and
  `H^0_Z(M)` agree, compatibly with their canonical maps to `M`.
* `Stacks.Duality.idealLocalCohomology_quotient_zero`,
  `Stacks.Duality.idealLocalCohomology_torsion_higher`,
  `Stacks.Duality.idealLocalCohomology_quotient_map_higher` — the three assertions of part (1).
* `Stacks.Duality.isZero_supportLocalCohomology_primaryComponent`,
  `Stacks.Duality.supportLocalCohomology_quotient_map_higher` — two of the three assertions of
  part (2); the first is an alias of `Stacks.Duality.supportLocalCohomology_torsion_higher`,
  which carries the tag for that clause. The remaining one, the degree-zero vanishing, is
  `Stacks.Duality.supportLocalCohomology_quotient_zero`.
* `Stacks.Duality.localCohomology_divide_by_torsion` — **the whole of Stacks 0AW0**: the
  conjunction of the preamble with the three assertions of part (1) and the three of part (2),
  carrying the Noetherian hypothesis discussed below. The eight declarations it conjoins are
  the seven above and `Stacks.Duality.supportLocalCohomology_quotient_zero`; the tag for each
  clause is carried by that declaration (for the alias, by the theorem it names), and the five
  that do not need the Noetherian hypothesis continue to be stated without it.

## Implementation notes

The source states the equalities `H^p_I(M) = H^p_I(M')` and `H^p_Z(M) = H^p_Z(M')`; these are
recorded as the statement that the map induced by the quotient map `M ⟶ M'` is an isomorphism,
which is the content of the long exact sequence argument the source gives.

The two degree-zero statements and all of part (2) hold over an arbitrary ring with `I`
finitely generated. The two higher-degree statements of part (1) carry the additional
hypothesis that `A` is Noetherian, which the source does not have.

**This is an error in the Stacks Project** (entry 0AW0(1) of `errata.md`). The hypothesis
cannot be dropped: without it the source's assertion is false, by the argument below, which
reduces it to a statement that part (3) of [Stacks, Tag 0A6P] refutes. The counterexample is
formalized in `StacksFrontier.RingTheory.Dualizing.TorsionQuotientCounterexample`, as
`Stacks.Duality.exists_not_isZero_idealLocalCohomology_primaryComponent` and
`Stacks.Duality.exists_not_isIso_idealLocalCohomology_map_mkQ`; the corrected statement together
with the counterexample is
`Stacks.Duality.localCohomology_divide_by_torsion_corrected_and_counterexample` there.

`RΓ_I` is the right adjoint of the inclusion `D(I^∞-torsion) ⟶ D(A)` of [Stacks, Tag 0A6L], so
`H^p_I(N) = 0` for all `p > 0` and an `I`-power-torsion module `N` says exactly that the counit
`RΓ_I(N) ⟶ N` is invertible — the degree-zero clause below already identifies `H^0_I(N)` with
`N` compatibly with the map to `N`. This is the module case of part (1) of [Stacks, Tag 0955],
stated there for Noetherian rings only and in the library — tagged, and for every object with
`I`-power-torsion cohomology — as
`Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app`, which is what the proofs below
appeal to. Invertibility of that counit forces the unit
`N ⟶ RΓ_I(N)` of `D(I^∞-torsion)` to be invertible as well — the triangle identity exhibits it
as the inverse of the counit, and the inclusion is conservative — and hence forces
`Ext²_{D(I^∞-torsion)}(M, N) ⟶ Ext²_A(M, N)` to be bijective for every `I`-power-torsion `M`,
since the triangle identity identifies that composite of the unit with the adjunction
isomorphism as the map induced by the inclusion. Part (3) of [Stacks, Tag 0A6P] says that this
map is not surjective in general: it fails for `A = ℤ[f, x, xₙ]/(f x, fⁿ xₙ - x)`, `I = (f)`,
`M = A/fA` and `N = A[f]`. Every `I`-power-torsion module is its own `I`-primary component, so
the clauses below, quantified over all `M`, would cover that `N`. The second higher-degree
clause of part (1) is no weaker: for an `I`-power-torsion `M` the quotient `M'` is zero, so it
asserts the same vanishing.

The gap is in the source's **proof**, not in any statement it relies on: that proof of part (1)
cites Tag 0A6L — the bare adjunction, which carries no vanishing — for `RΓ_I(N) = N`, and
Tag 0A6P, three lemmas earlier in the same section, refutes that step for a finitely generated
ideal of a non-Noetherian ring. 0A6P(3) is formalized in this library, as
`Dualizing.exists_not_surjective_mapExt_two_powerTorsionModule` of
`StacksFrontier.RingTheory.Dualizing.TorsionExtCounterexample`, and the deduction of the failure
of Tag 0AW0 from it is `Stacks.Duality.bijective_mapExt_of_isZero_idealLocalCohomology`. The
0A6P(3) declaration is existential, and its witness is the square-zero extension `ℤ ⋉ (ℚ/ℤ)`
with `f = 2` rather than the source's `ℤ[f, x, xₙ]/(f x, fⁿ xₙ - x)`; either serves, the only
input being a nonzero `x` with `f x = 0` lying in every `fⁿ A`.

Both theories are read off the functors `Stacks.Duality.idealLocalCohomology` and
`Stacks.Duality.supportLocalCohomology`, and `N` is Mathlib's `Ideal.primaryComponent M I`.

## References

* [Stacks Project, Tag 0AW0](https://stacks.math.columbia.edu/tag/0AW0)
* [Stacks Project, Tag 05EB](https://stacks.math.columbia.edu/tag/05EB)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 0A6L](https://stacks.math.columbia.edu/tag/0A6L)
* [Stacks Project, Tag 0A6N](https://stacks.math.columbia.edu/tag/0A6N)
* [Stacks Project, Tag 0A6P](https://stacks.math.columbia.edu/tag/0A6P)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.Duality

/-! ### Generalities on derived categories -/

/-- An exact functor does not raise the amplitude of an object of the derived category. -/
lemma exactFunctor_isLE
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (n : ℤ) [X.IsLE n] :
    (F.mapDerivedCategory.obj X).IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact (F.map_isZero (X.isZero_of_isLE n i hi)).of_iso
    ((Dualizing.mapDerivedCategoryHomologyIso F i).app X)

/-- A right adjoint of the derived functor of an exact functor does not lower connectivity. -/
lemma derived_rightAdjoint_isGE
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {G : DerivedCategory D ⥤ DerivedCategory C} (adj : F.mapDerivedCategory ⊣ G)
    (X : DerivedCategory D) (n : ℤ) [X.IsGE n] : (G.obj X).IsGE n := by
  apply (DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - 1) n (by omega) (G.obj X)).2
  intro Y f hY
  have := exactFunctor_isLE F Y (n - 1)
  have hz : (adj.homEquiv Y X).symm f = 0 :=
    DerivedCategory.TStructure.t.zero _ (n - 1) n (by omega)
  apply (adj.homEquiv Y X).symm.injective
  rw [hz, adj.homEquiv_counit]
  simp

/-- A morphism out of the image of the left adjoint which corepresents the maps out of that
image identifies its source with the value of the right adjoint. -/
private lemma iso_of_universal_counit
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {B : C} {M : D} (f : F.obj B ⟶ M)
    (hf : ∀ T, Function.Bijective (fun g : T ⟶ B => F.map g ≫ f)) :
    ∃ e : B ≅ G.obj M, F.map e.hom ≫ adj.counit.app M = f := by
  let φ := (adj.homEquiv B M) f
  have hφ : F.map φ ≫ adj.counit.app M = f := (adj.homEquiv B M).symm_apply_apply f
  obtain ⟨ψ, hψ⟩ := (hf (G.obj M)).2 (adj.counit.app M)
  have h₁ : φ ≫ ψ = 𝟙 B := (hf B).1 (by simp [Functor.map_comp, Category.assoc, hψ, hφ])
  have h₂ : ψ ≫ φ = 𝟙 (G.obj M) := by
    apply (adj.homEquiv (G.obj M) M).symm.injective
    simp only [adj.homEquiv_counit, Functor.map_comp, Category.assoc, hφ, hψ]
    simp
  exact ⟨⟨φ, ψ, h₁, h₂⟩, hφ⟩

/-- **Degree zero of a derived adjunction along an exact functor.** If an exact functor `F` has
a right adjoint `G`, and its derived functor has a right adjoint `RG`, then `H^0` of
`F(RG(M))`, for `M` placed in degree zero, is `F(G(M))`, compatibly with the counits. -/
private lemma exactAdjunction_zero_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {G : D ⥤ C} (adj : F ⊣ G)
    {RG : DerivedCategory D ⥤ DerivedCategory C} (radj : F.mapDerivedCategory ⊣ RG)
    (M : D) :
    ∃ e : (DerivedCategory.homologyFunctor D 0).obj
        (F.mapDerivedCategory.obj (RG.obj ((DerivedCategory.singleFunctor D 0).obj M))) ≅
        F.obj (G.obj M),
      e.hom ≫ adj.counit.app M =
        (DerivedCategory.homologyFunctor D 0).map
          (radj.counit.app ((DerivedCategory.singleFunctor D 0).obj M)) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).hom.app M := by
  let SC := DerivedCategory.singleFunctor C 0
  let SD := DerivedCategory.singleFunctor D 0
  let HD := DerivedCategory.homologyFunctor D 0
  let X := SD.obj M
  have : (RG.obj X).IsGE 0 := derived_rightAdjoint_isGE F radj X 0
  obtain ⟨B, b, hb, hb'⟩ :=
    Stacks.LocalCohomology.exists_single_approximation (RG.obj X)
  let σ := F.mapDerivedCategorySingleFunctor 0
  let a : SD.obj (F.obj B) ⟶ F.mapDerivedCategory.obj (RG.obj X) :=
    σ.inv.app B ≫ F.mapDerivedCategory.map b
  have hbF : IsIso (HD.map (F.mapDerivedCategory.map b)) := by
    have := hb
    exact (NatIso.isIso_map_iff (Dualizing.mapDerivedCategoryHomologyIso F 0) b).2
      (by dsimp; infer_instance)
  have ha : IsIso (HD.map a) := by
    dsimp [a]
    rw [Functor.map_comp]
    infer_instance
  let f : F.obj B ⟶ M := SD.preimage (a ≫ radj.counit.app X)
  have hf : SD.map f = a ≫ radj.counit.app X := SD.map_preimage _
  have huniv (T : C) : Function.Bijective (fun g : T ⟶ B => F.map g ≫ f) := by
    have hc : Function.Bijective (fun k : F.mapDerivedCategory.obj (SC.obj T) ⟶ X =>
        σ.inv.app T ≫ k) := ⟨fun x y h => (cancel_epi (σ.inv.app T)).1 h,
          fun k => ⟨σ.hom.app T ≫ k, by simp⟩⟩
    have hbij : Function.Bijective (fun g : T ⟶ B =>
        σ.inv.app T ≫ (radj.homEquiv (SC.obj T) X).symm (SC.map g ≫ b)) :=
      hc.comp ((radj.homEquiv (SC.obj T) X).symm.bijective.comp (hb' T))
    have heq (g : T ⟶ B) :
        σ.inv.app T ≫ (radj.homEquiv (SC.obj T) X).symm (SC.map g ≫ b) =
          SD.map (F.map g ≫ f) := by
      simp only [radj.homEquiv_counit, Functor.map_comp, hf, a, Category.assoc]
      have h := σ.inv.naturality g
      dsimp [SC, SD] at h ⊢
      rw [← Category.assoc, ← h, Category.assoc]
    have hbij' : Function.Bijective (fun g : T ⟶ B => SD.map (F.map g ≫ f)) := by
      simpa only [heq] using hbij
    exact ⟨fun g h hh => hbij'.1 (congrArg SD.map hh), fun k => by
      obtain ⟨g, hg⟩ := hbij'.2 (SD.map k)
      exact ⟨g, SD.map_injective hg⟩⟩
  obtain ⟨eB, heB⟩ := iso_of_universal_counit adj f huniv
  let s := DerivedCategory.singleFunctorCompHomologyFunctorIso D 0
  let e := (asIso (HD.map a)).symm ≪≫ s.app (F.obj B) ≪≫ F.mapIso eB
  refine ⟨e, ?_⟩
  apply (cancel_epi (HD.map a)).1
  simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    asIso_inv, IsIso.hom_inv_id_assoc, heB]
  have hn := s.hom.naturality f
  dsimp at hn
  change s.hom.app (F.obj B) ≫ f = _
  rw [← hn]
  dsimp [SD, HD] at hf ⊢
  rw [hf, Functor.map_comp, Category.assoc]

/-- For a triangulated left adjoint `L` into `D(A)` with right adjoint `G`, the functor `G ⋙ L`
turns the quotient map `M ⟶ M/N` into an isomorphism in cohomological degree `p` as soon as it
kills `N` in degrees `p` and `p + 1`. -/
private lemma isIso_homologyMap_mkQ
    {A : Type u} [CommRing A] (M : ModuleCat.{v} A) (N : Submodule A M)
    {T : Type*} [Category T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
    (L : T ⥤ DerivedCategory (ModuleCat.{v} A)) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
    {G : DerivedCategory (ModuleCat.{v} A) ⥤ T} (adj : L ⊣ G) (p : ℤ)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor _ p).obj
      (L.obj (G.obj ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A N))))))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor _ (p + 1)).obj
      (L.obj (G.obj ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A N)))))) :
    IsIso ((DerivedCategory.singleFunctor _ 0 ⋙ G ⋙ L ⋙
      DerivedCategory.homologyFunctor _ p).map (ModuleCat.ofHom N.mkQ)) := by
  let : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  let : G.Additive := adj.right_adjoint_additive
  let F := G ⋙ L
  let : F.CommShift ℤ := Functor.CommShift.comp _ _
  let : F.IsTriangulated := inferInstance
  let S : ShortComplex (ModuleCat.{v} A) :=
    ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ) (by ext; simp)
  have hS : S.ShortExact :=
    ModuleCat.shortComplex_shortExact S (LinearMap.exact_subtype_mkQ N)
      N.subtype_injective N.mkQ_surjective
  let : PreservesFiniteLimits (CochainComplex.singleFunctor (ModuleCat.{v} A) 0) :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single _ (.up ℤ) 0))
  let : PreservesFiniteColimits (CochainComplex.singleFunctor (ModuleCat.{v} A) 0) :=
    inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single _ (.up ℤ) 0))
  let T := DerivedCategory.triangleOfSES (hS.map (CochainComplex.singleFunctor _ 0))
  have hT := F.map_distinguished T (DerivedCategory.triangleOfSES_distinguished _)
  have hm : Mono ((DerivedCategory.homologyFunctor _ p).map (F.mapTriangle.obj T).mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff _ hT p).2 (h₀.eq_of_src _ _)
  have he : Epi ((DerivedCategory.homologyFunctor _ p).map (F.mapTriangle.obj T).mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT p (p + 1)).2
      (h₁.eq_of_tgt _ _)
  change IsIso ((DerivedCategory.homologyFunctor _ p).map (F.mapTriangle.obj T).mor₂)
  exact isIso_of_mono_of_epi _

/-! ### The torsion submodule and the quotient -/

/-- The `I`-power-torsion submodule of `M` really is `I`-power torsion. -/
private lemma isIPowerTorsion_primaryComponent
    (A : Type u) [CommRing A] (I : Ideal A) (M : ModuleCat.{max u v} A) :
    IsIPowerTorsion A (Ideal.primaryComponent M I) I :=
  ((Dualizing.powerTorsionFunctor.{u, v} A I).obj M).property

/-- For a finitely generated ideal, the quotient of `M` by its `I`-primary component has
trivial `I`-primary component. -/
private lemma primaryComponent_quotient_eq_bot
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (M : Type*)
    [AddCommGroup M] [Module A M] :
    Ideal.primaryComponent (M ⧸ Ideal.primaryComponent M I) I = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem _ I x).mp hx
  exact eq_zero_of_pow_smul_eq_zero I _
    (torsionBySet_quotient_primaryComponent_eq_bot I hI M) n x
    fun a ha => (Submodule.mem_torsionBySet_iff _ _).mp hn ⟨a, ha⟩

/-! ### Part (1): the `I`-power torsion theory -/

/-- **Stacks 0AW0.** The zeroth local cohomology `H^0_I(M)` of `M` for the `I`-power torsion
theory is the `I`-power-torsion submodule `M[I^∞]` of `M`, by an isomorphism compatible with
the canonical map of `H^0_I(M)` into `M`. -/
@[stacks 0AW0 "H^0_I is the torsion submodule"]
theorem idealLocalCohomology_zero_iso_torsion
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) :
    ∃ e : (idealLocalCohomology.{u, v} A I hI 0).obj M ≅
        ModuleCat.of A (Ideal.primaryComponent M I),
      e.hom ≫ ModuleCat.ofHom (Submodule.subtype (Ideal.primaryComponent M I)) =
        idealLocalCohomologyToModule.{u, v} A I hI M := by
  let P : ObjectProperty (ModuleCat.{max u v} A) := fun M => IsIPowerTorsion A M I
  let : P.IsSerreClass := Dualizing.powerTorsionModuleProperty_isSerreClass A I hI
  let : P.ι.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteLimits P.ι := ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
  let : PreservesFiniteColimits P.ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
  obtain ⟨e, he⟩ := exactAdjunction_zero_iso P.ι
    (Dualizing.powerTorsionAdjunction.{u, v} A I)
    (Dualizing.derivedPowerTorsionAdjunction.{u, v} A I hI) M
  refine ⟨e, ?_⟩
  change e.hom ≫ _ =
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map
      (𝟙 _ ≫ (Dualizing.derivedPowerTorsionCounit.{u, v} A I hI).app
        ((DerivedCategory.singleFunctor _ 0).obj M)) ≫ _
  rw [Category.id_comp]
  rwa [Dualizing.powerTorsionAdjunction_counit] at he

/-- **Stacks 0AW0, part (1).** Quotienting by the `I`-power-torsion submodule kills the zeroth
local cohomology for the `I`-power torsion theory: `H^0_I(M/M[I^∞]) = 0`. -/
@[stacks 0AW0 "part (1), degree zero"]
theorem idealLocalCohomology_quotient_zero
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) :
    IsZero ((idealLocalCohomology.{u, v} A I hI 0).obj
      (ModuleCat.of A (M ⧸ Ideal.primaryComponent M I))) := by
  obtain ⟨e, -⟩ := idealLocalCohomology_zero_iso_torsion.{u, v} A I hI
    (ModuleCat.of A (M ⧸ Ideal.primaryComponent M I))
  refine IsZero.of_iso ?_ e
  rw [primaryComponent_quotient_eq_bot A I hI M]
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- **Stacks 0AW0, part (1).** Over a Noetherian ring the higher local cohomology of the
`I`-power-torsion submodule vanishes for the `I`-power torsion theory:
`H^p_I(M[I^∞]) = 0` for `p > 0`.

The source states this for an arbitrary ring. The Noetherian hypothesis added here cannot be
removed: for a finitely generated ideal of a non-Noetherian ring the assertion is false, by
part (3) of [Stacks, Tag 0A6P]; the counterexample is
`Stacks.Duality.exists_not_isZero_idealLocalCohomology_primaryComponent`. -/
@[stacks 0AW0 "part (1), higher cohomology of the torsion submodule"]
theorem idealLocalCohomology_torsion_higher
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A)
    (p : ℤ) (hp : 0 < p) :
    IsZero ((idealLocalCohomology.{u, v} A I hI p).obj
      (ModuleCat.of A (Ideal.primaryComponent M I))) := by
  let N := ModuleCat.of A (Ideal.primaryComponent M I)
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N
  let K : Dualizing.PowerTorsionDerivedCategory.{u, max u v} A I hI :=
    ⟨X, Dualizing.PowerTorsionBaseChange.derivedPowerTorsionProperty_singleFunctor I hI N
      (isIPowerTorsion_primaryComponent.{u, v} A I M)⟩
  have hε : IsIso ((Dualizing.derivedPowerTorsionCounit.{u, v} A I hI).app X) :=
    Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app.{u, v} A I hI K
  have hz := DerivedCategory.isZero_of_isLE X 0 p hp
  change IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) p).obj
    ((Dualizing.powerTorsionComparison A I hI ⋙
      (Dualizing.derivedPowerTorsionProperty A I hI).ι).obj
        ((Dualizing.derivedPowerTorsion.{u, v} A I hI).obj X)))
  exact IsZero.of_iso hz ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) p).mapIso
    (@asIso _ _ _ _ _ hε))

/-- **Stacks 0AW0, part (1).** Over a Noetherian ring the quotient map `M ⟶ M/M[I^∞]` induces
an isomorphism `H^p_I(M) ≅ H^p_I(M/M[I^∞])` in every positive degree.

The source states this for an arbitrary ring. The Noetherian hypothesis added here cannot be
removed: taking an `I`-power-torsion `M`, so that `M/M[I^∞] = 0`, turns the assertion into the
vanishing of `Stacks.Duality.idealLocalCohomology_torsion_higher`, which part (3) of
[Stacks, Tag 0A6P] refutes over a non-Noetherian ring; the counterexample is
`Stacks.Duality.exists_not_isIso_idealLocalCohomology_map_mkQ`. -/
@[stacks 0AW0 "part (1), higher cohomology of the quotient"]
theorem idealLocalCohomology_quotient_map_higher
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A)
    (p : ℤ) (hp : 0 < p) :
    IsIso ((idealLocalCohomology.{u, v} A I hI p).map
      (ModuleCat.ofHom (Ideal.primaryComponent M I).mkQ)) := by
  let P := Dualizing.powerTorsionModuleProperty.{u, max u v} A I hI
  exact isIso_homologyMap_mkQ M (Ideal.primaryComponent M I) P.ι.mapDerivedCategory
    (Dualizing.derivedPowerTorsionAdjunction.{u, v} A I hI) p
    (idealLocalCohomology_torsion_higher.{u, v} A I hI M p hp)
    (idealLocalCohomology_torsion_higher.{u, v} A I hI M (p + 1) (by omega))

/-! ### Part (2): the theory with support in `V(I)` -/

/-- **Stacks 0AW0, part (2).** The higher local cohomology with support in `Z = V(I)` of the
`I`-power-torsion submodule vanishes: `H^p_Z(M[I^∞]) = 0` for `p > 0`. This is
`Stacks.Duality.supportLocalCohomology_torsion_higher`, which carries the tag for this clause. -/
alias isZero_supportLocalCohomology_primaryComponent :=
  Stacks.Duality.supportLocalCohomology_torsion_higher

/-- Having `I`-power-torsion cohomology is invariant under isomorphism in `D(A)`. -/
private lemma derivedPowerTorsionProperty_closedUnderIso
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI).IsClosedUnderIsomorphisms where
  of_iso e h i := (Dualizing.powerTorsionModuleProperty A I hI).prop_of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso e) (h i)

/-- The objects of `D(A)` with `I`-power-torsion cohomology form a triangulated
subcategory. -/
private lemma derivedPowerTorsionProperty_triangulated
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI).IsTriangulated := by
  let P := Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI
  let S := Dualizing.powerTorsionModuleProperty.{u, max u v} A I hI
  let : P.IsClosedUnderIsomorphisms := derivedPowerTorsionProperty_closedUnderIso.{u, v} A I hI
  let : P.ContainsZero := ⟨⟨0, isZero_zero _, fun i =>
    S.prop_of_isZero ((DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _))⟩⟩
  let : P.IsStableUnderShift ℤ := ⟨fun n => ⟨fun X hX i =>
    S.prop_of_iso (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).shiftIso
      n i (n + i) rfl).app X).symm (hX (n + i))⟩⟩
  let : P.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ i =>
    S.prop_X₂_of_exact (DerivedCategory.HomologySequence.exact₂ T hT i) (h₁ i) (h₃ i))
  exact {}

/-- **Stacks 0AW0, part (2).** The quotient map `M ⟶ M/M[I^∞]` induces an isomorphism
`H^p_Z(M) ≅ H^p_Z(M/M[I^∞])` in every positive degree. -/
@[stacks 0AW0 "part (2), higher cohomology of the quotient"]
theorem supportLocalCohomology_quotient_map_higher
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) (p : ℤ) (hp : 0 < p) :
    IsIso ((supportLocalCohomology.{u, v} A I hI p).map
      (ModuleCat.ofHom (Ideal.primaryComponent M I).mkQ)) := by
  let P := Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI
  let : P.IsClosedUnderIsomorphisms := derivedPowerTorsionProperty_closedUnderIso.{u, v} A I hI
  let : P.IsTriangulated := derivedPowerTorsionProperty_triangulated.{u, v} A I hI
  exact isIso_homologyMap_mkQ M (Ideal.primaryComponent M I) P.ι
    (Dualizing.localCohomologyAdjunction.{u, max u v} A I hI) p
    (isZero_supportLocalCohomology_primaryComponent.{u, v} A I hI M p hp)
    (isZero_supportLocalCohomology_primaryComponent.{u, v} A I hI M (p + 1) (by omega))

/-! ### The two theories agree in degree zero -/

/-- **Stacks 0AW0.** For a finitely generated ideal `I` and `Z = V(I)` the two zeroth local
cohomology modules agree, `H^0_I(M) = H^0_Z(M)`, compatibly with their canonical maps down
to `M`; the common value is the `I`-power-torsion submodule `M[I^∞]`. -/
@[stacks 0AW0 "H^0_I = H^0_Z"]
theorem idealLocalCohomology_zero_iso_supportLocalCohomology_zero
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) :
    ∃ e : (idealLocalCohomology.{u, v} A I hI 0).obj M ≅
        (supportLocalCohomology.{u, v} A I hI 0).obj M,
      e.hom ≫ supportLocalCohomologyToModule.{u, v} A I hI M =
        idealLocalCohomologyToModule.{u, v} A I hI M := by
  obtain ⟨e₁, h₁⟩ := idealLocalCohomology_zero_iso_torsion.{u, v} A I hI M
  obtain ⟨e₂, h₂⟩ := supportLocalCohomology_zero_iso_torsion.{u, v} A I hI M
  refine ⟨e₁ ≪≫ e₂.symm, ?_⟩
  rw [← h₂, ← h₁]
  simp

/-! ### The whole of Stacks 0AW0 -/

/-- **Stacks 0AW0, the preamble and both parts.** Let `A` be a ring, let `I ⊆ A` be a finitely
generated ideal, let `M` be an `A`-module and let `Z = V(I)`. Then `H^0_I(M) = H^0_Z(M)`; the
common value `N` is the `I`-power-torsion submodule `M[I^∞]`, both identifications being
compatible with the canonical maps down to `M`; and, writing `M' = M/N`,

1. `H^0_I(M') = 0`, `H^p_I(M) = H^p_I(M')` and `H^p_I(N) = 0` for all `p > 0`;
2. `H^0_Z(M') = 0`, `H^p_Z(M) = H^p_Z(M')` and `H^p_Z(N) = 0` for all `p > 0`.

The two higher-degree clauses of part (1) carry the hypothesis that `A` is Noetherian, which
the source does not have, so this conjunction carries it too. That hypothesis cannot be dropped:
part (3) of [Stacks, Tag 0A6P] refutes those two clauses for a finitely generated ideal of a
non-Noetherian ring, by the argument in the module docstring. Everything else here — the
preamble and the whole of part (2) — holds over an arbitrary ring, and is stated that way by the
eight declarations this conjoins, each of which carries the tag for its own clause; they are
listed in the module docstring and in that of
`StacksFrontier.AlgebraicGeometry.Duality.DivideByTorsion`. The same statement over an arbitrary
ring, with the Noetherian hypothesis attached to those two clauses alone, conjoined with the
counterexamples to them, is
`Stacks.Duality.localCohomology_divide_by_torsion_corrected_and_counterexample`. -/
@[stacks 0AW0 "the preamble and both parts conjoined, over a Noetherian ring"]
theorem localCohomology_divide_by_torsion
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) :
    (∃ e : (idealLocalCohomology.{u, v} A I hI 0).obj M ≅
        (supportLocalCohomology.{u, v} A I hI 0).obj M,
      e.hom ≫ supportLocalCohomologyToModule.{u, v} A I hI M =
        idealLocalCohomologyToModule.{u, v} A I hI M) ∧
    (∃ e : (idealLocalCohomology.{u, v} A I hI 0).obj M ≅
        ModuleCat.of A (Ideal.primaryComponent M I),
      e.hom ≫ ModuleCat.ofHom (Submodule.subtype (Ideal.primaryComponent M I)) =
        idealLocalCohomologyToModule.{u, v} A I hI M) ∧
    (IsZero ((idealLocalCohomology.{u, v} A I hI 0).obj
          (ModuleCat.of A (M ⧸ Ideal.primaryComponent M I))) ∧
        (∀ p : ℤ, 0 < p → IsIso ((idealLocalCohomology.{u, v} A I hI p).map
          (ModuleCat.ofHom (Ideal.primaryComponent M I).mkQ))) ∧
        ∀ p : ℤ, 0 < p → IsZero ((idealLocalCohomology.{u, v} A I hI p).obj
          (ModuleCat.of A (Ideal.primaryComponent M I)))) ∧
      (IsZero ((supportLocalCohomology.{u, v} A I hI 0).obj
          (ModuleCat.of A (M ⧸ Ideal.primaryComponent M I))) ∧
        (∀ p : ℤ, 0 < p → IsIso ((supportLocalCohomology.{u, v} A I hI p).map
          (ModuleCat.ofHom (Ideal.primaryComponent M I).mkQ))) ∧
        ∀ p : ℤ, 0 < p → IsZero ((supportLocalCohomology.{u, v} A I hI p).obj
          (ModuleCat.of A (Ideal.primaryComponent M I)))) :=
  ⟨idealLocalCohomology_zero_iso_supportLocalCohomology_zero.{u, v} A I hI M,
    idealLocalCohomology_zero_iso_torsion.{u, v} A I hI M,
    ⟨idealLocalCohomology_quotient_zero.{u, v} A I hI M,
      fun p hp ↦ idealLocalCohomology_quotient_map_higher.{u, v} A I hI M p hp,
      fun p hp ↦ idealLocalCohomology_torsion_higher.{u, v} A I hI M p hp⟩,
    supportLocalCohomology_quotient_zero.{u, v} A I hI M,
    fun p hp ↦ supportLocalCohomology_quotient_map_higher.{u, v} A I hI M p hp,
    fun p hp ↦ isZero_supportLocalCohomology_primaryComponent.{u, v} A I hI M p hp⟩

end Stacks.Duality

end
