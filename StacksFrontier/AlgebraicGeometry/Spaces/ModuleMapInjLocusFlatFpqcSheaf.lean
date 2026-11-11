module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapBaseChangeCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.TestSchemeFlatFpqcSite
public import StacksFrontier.AlgebraicGeometry.Spaces.TestSchemePullbacks
public import StacksFrontier.CategoryTheory.Sites.SubsingletonPresheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# The injectivity locus of a map of modules is an fpqc sheaf on the flat site

In the situation of Stacks 083F — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
and a map `u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — the functor `F_inj` sends a test
scheme `T` over `Y` to a point if the base change `u_T` is injective and to the empty set
otherwise.  Injectivity of `u_T` is preserved by flat base change but not by arbitrary base
change, so, as Stacks 05MJ says in the case of schemes, `F_inj` is a functor on the test schemes
over `Y` with flat morphisms.  **Stacks 083H** for `F_inj` says that it satisfies the sheaf
property for the fpqc topology there.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.IsInjectiveAt`: `u_T` is injective.
* `AlgebraicGeometry.Space.ModuleMapSituation.flatInjFunctor`: the functor `F_inj` on
  `AlgebraicGeometry.Space.FlatSchemesOver`.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isInjectiveAt_of_flatMorphisms`: injectivity of
  `u_T` persists along flat morphisms of test schemes.
* `AlgebraicGeometry.Space.ModuleMapSituation.isSheaf_flatInjFunctor`: **Stacks 083H** for
  `F_inj`.

## Implementation notes

Everything is at the module universe of the structure rings, where the inverse image of modules
and its exactness along a flat morphism are available.  The other three clauses of Stacks 083H
and the sheaf property of the universal-injectivity locus on all test schemes are in
`StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFpqcSheaf`.

## References

* [Stacks Project, Tag 083H](https://stacks.math.columbia.edu/tag/083H)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : ModuleMapSituation.{u, u} B S hS)

/-- The base change `u_T` of `u` to a test scheme `T` is injective, in the sense of Stacks 083F:
it is a monomorphism of `𝒪_{X_T}`-modules. -/
def IsInjectiveAt (T : D.SchemesOver) : Prop :=
  Mono (D.baseChangeHom (modulePullbackSystem B S hS) T)

/-- Injectivity of the base change of `u` persists along a flat morphism of test schemes, the
comparison of base-change spaces being flat and the inverse image along a flat morphism
preserving monomorphisms. -/
theorem isInjectiveAt_of_flatMorphisms {T T' : D.SchemesOver} (g : T' ⟶ T)
    (hg : flatMorphisms D.Y g) (h : D.IsInjectiveAt T) : D.IsInjectiveAt T' := by
  have hfl : ∀ {U V : BigFppfOver B S hS} (h : U ⟶ V),
      Flat ((BigFppfOver.toScheme B S hS).map h) →
        IsFlat B S hS ((schemeSpaceFunctor B S hS).map h).hom := fun {U V} h hh =>
    (isFlat_iff_presheaf B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) (Functor.relativelyRepresentable.map yoneda h)).2
      ((presheaf_yoneda_map_iff B S hS AlgebraicGeometry.Flat.isStableUnderBaseChange h).2 hh)
  have hflat : IsFlat B S hS (D.baseChangeMap g).hom :=
    D.isFlat_baseChangeMap g
      (hfl g.left ((flatMorphisms_iff g).1 hg))
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS (D.baseChangeMap g) hflat
  have : Mono (D.baseChangeHom (modulePullbackSystem B S hS) T) := h
  exact (D.mono_baseChangeMap_map_iff (modulePullbackSystem B S hS) g).1
    ((modulePullback B S hS (D.baseChangeMap g)).map_mono _)

/-- **The injectivity functor `F_inj` of Stacks 083F.**  Its value at a test scheme `T` over `Y`
is a one-point set when the base change `u_T` is injective and is empty otherwise.  Injectivity
is not stable under arbitrary base change, so, as in Stacks 05MJ, this is a functor on the test
schemes over `Y` with flat morphisms. -/
def flatInjFunctor : (FlatSchemesOver D.Y)ᵒᵖ ⥤ Type u where
  obj T := {x : PUnit.{u + 1} // D.IsInjectiveAt T.unop.obj}
  map g := ↾fun x => ⟨x.1, D.isInjectiveAt_of_flatMorphisms g.unop.1 g.unop.2 x.2⟩
  map_id := by
    intro T
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl
  map_comp := by
    intro T U V g k
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl

/-- A value of the injectivity functor has at most one element. -/
instance flatInjFunctor_obj_subsingleton (T : (FlatSchemesOver D.Y)ᵒᵖ) :
    Subsingleton (D.flatInjFunctor.obj T) :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim a.val b.val)⟩

/-- The injectivity functor is nonempty at a test scheme exactly when the base change of `u`
there is injective. -/
@[simp]
theorem nonempty_flatInjFunctor_obj_iff (T : FlatSchemesOver D.Y) :
    Nonempty (D.flatInjFunctor.obj (op T)) ↔
      Mono (D.baseChangeHom (modulePullbackSystem B S hS) T.obj) :=
  ⟨fun ⟨x⟩ => x.2, fun h => ⟨⟨PUnit.unit, h⟩⟩⟩

/-- **Stacks 083H**, injectivity clause.  The functor `F_inj` of test schemes over `Y` on which
the base change of `u` is injective, a functor on the test schemes over `Y` with flat morphisms,
satisfies the sheaf property for the fpqc topology there.

The topology is generated by the fpqc covering families, so the sheaf property is tested on the
pullback, along a flat morphism `Z ⟶ X`, of the sieve generated by an fpqc covering family
`{T_i ⟶ X}`.  The fibre products `T_i ×_X Z` form an fpqc covering of `Z` whose projections to
`Z` and to `T_i` are both flat, so each projection to `Z` lies in that pullback sieve.  The
functor is subterminal, so it suffices that injectivity of `u` at every `T_i ×_X Z` gives
injectivity at `Z`, and this is descent of injectivity along the flat jointly surjective family
of base-change spaces `X ×_Y (T_i ×_X Z) ⟶ X ×_Y Z`. -/
@[stacks 083H "F_inj, the functor of injectivity of u_T on the test schemes over the base with \
flat morphisms (the category Stacks 05MJ puts it on, injectivity not being stable under \
arbitrary base change), is a sheaf for the fpqc topology there"]
theorem isSheaf_flatInjFunctor :
    Presheaf.IsSheaf (flatFpqcTopology D.Y) D.flatInjFunctor := by
  rw [isSheaf_iff_isSheaf_of_type, flatFpqcTopology, Precoverage.isSheaf_toGrothendieck_iff]
  intro X Z f R hR
  rw [Presieve.isSheafFor_iff_nonempty_of_subsingleton]
  intro hne
  obtain ⟨I, T, k, rfl⟩ := R.exists_eq_ofArrows
  have hRK : Presieve.ofArrows (fun i => (T i).obj) (fun i => (k i).1) ∈
      (Scheme.fpqcPrecoverage.comap (testSchemeFunctor D.Y)) X.obj := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR ⊢
    exact hR
  let P (i : I) : D.SchemesOver := pullback (k i).1 f.1
  let p₁ (i : I) : P i ⟶ Z.obj := pullback.snd (k i).1 f.1
  let p₂ (i : I) : P i ⟶ (T i).obj := pullback.fst (k i).1 f.1
  have hsq (i : I) : IsPullback (p₂ i) (p₁ i) (k i).1 f.1 := IsPullback.of_hasPullback _ _
  have hPK : Presieve.ofArrows P p₁ ∈
      (Scheme.fpqcPrecoverage.comap (testSchemeFunctor D.Y)) Z.obj :=
    Precoverage.mem_coverings_of_isPullback _ hRK f.1 p₁ p₂ fun i => (hsq i).flip
  have hPs : Presieve.ofArrows (fun i => (testSchemeFunctor D.Y).obj (P i))
      (fun i => (testSchemeFunctor D.Y).map (p₁ i)) ∈
        Scheme.fpqcPrecoverage ((testSchemeFunctor D.Y).obj Z.obj) := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hPK
    exact hPK
  have hcov := (Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) _ hPs)
  have hp₁ (i : I) : flatMorphisms D.Y (p₁ i) := (flatMorphisms_iff _).2 (hcov.2 i)
  have hp₂ (i : I) : flatMorphisms D.Y (p₂ i) :=
    (flatMorphisms_iff _).2 (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((hsq i).flip.map (testSchemeFunctor D.Y)) ((flatMorphisms_iff _).1 f.2))
  have hmono (i : I) : Mono (D.baseChangeHom (modulePullbackSystem B S hS) (P i)) := by
    refine (D.nonempty_flatInjFunctor_obj_iff ⟨P i⟩).1
      (hne (⟨p₁ i, hp₁ i⟩ : (⟨P i⟩ : FlatSchemesOver D.Y) ⟶ Z) ?_)
    refine ⟨T i, ⟨p₂ i, hp₂ i⟩, k i, Presieve.ofArrows.mk i, ?_⟩
    exact WideSubcategory.hom_ext _ (hsq i).w
  have hjs := D.isJointlySurjective_baseChangeMap P (fun i => p₁ i)
    (jointlySurjective_yoneda_of_scheme B S hS (fun i => (P i).left) (fun i => (p₁ i).left)
      fun x => hcov.1 x)
  have hfl : ∀ {U V : BigFppfOver B S hS} (h : U ⟶ V),
      Flat ((BigFppfOver.toScheme B S hS).map h) →
        IsFlat B S hS ((schemeSpaceFunctor B S hS).map h).hom := fun {U V} h hh =>
    (isFlat_iff_presheaf B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) (Functor.relativelyRepresentable.map yoneda h)).2
      ((presheaf_yoneda_map_iff B S hS AlgebraicGeometry.Flat.isStableUnderBaseChange h).2 hh)
  refine ⟨⟨PUnit.unit, ?_⟩⟩
  exact mono_of_forall_mono_modulePullback_map_of_isFlat B S hS
    (fun i => D.baseChangeMap (p₁ i))
    (fun i => D.isFlat_baseChangeMap (p₁ i) (hfl _ ((flatMorphisms_iff _).1 (hp₁ i))))
    hjs (D.baseChangeHom (modulePullbackSystem B S hS) Z.obj)
    fun i => (D.mono_baseChangeMap_map_iff (modulePullbackSystem B S hS) (p₁ i)).2 (hmono i)

end ModuleMapSituation

end AlgebraicGeometry.Space

end
