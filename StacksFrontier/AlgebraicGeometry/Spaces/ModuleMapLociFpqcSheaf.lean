module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapBaseChangeCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.TestSchemePullbacks
public import StacksFrontier.CategoryTheory.Sites.SubsingletonPresheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# The four base-change loci of a map of modules are sheaves for the fpqc topology

In the situation of Stacks 083F — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
and a map `u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — the four loci `F_iso`, `F_inj`,
`F_surj` and `F_zero` are subterminal presheaves on the test schemes over `Y` (for `F_inj`, on the
test schemes with flat morphisms).  **Stacks 083H** says that each of them is a sheaf for the
fpqc topology.

Being subterminal, such a presheaf is a sheaf exactly when a section over every member of a
covering sieve produces a section over its target, that is, exactly when the condition it
expresses is fpqc local on the test scheme.  A covering sieve of a test scheme `T` contains a
family of arrows `T_i ⟶ T` which is jointly surjective on points and all of whose members are
flat; base changing it gives a jointly surjective family of flat morphisms
`X ×_Y T_i ⟶ X ×_Y T`, and each of the four conditions descends along such a family with no
hypothesis on the supports, because the ranges of the induced maps on points cover `X ×_Y T`.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isSheaf_isoFunctor`,
  `.isSheaf_surjFunctor` and `.isSheaf_zeroFunctor` are the clauses of **Stacks 083H** for
  `F_iso`, `F_surj` and `F_zero`.  The injectivity functor `F_inj`, defined by injectivity of
  `u_T`, is stable only under flat base change, so, as in Stacks 05MJ, it lives on the test
  schemes over `Y` with flat morphisms; its clause,
  `AlgebraicGeometry.Space.ModuleMapSituation.isSheaf_flatInjFunctor`, is in
  `StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapInjLocusFlatFpqcSheaf`.
* `AlgebraicGeometry.Space.ModuleMapSituation.isSheaf_injFunctor`: the locus of universal
  injectivity, a functor on all test schemes, is an fpqc sheaf as well.

## Implementation notes

Everything is at the module universe of the structure rings, which is the universe at which the
inverse image of modules and the descent of the four conditions along a flat morphism are
available, and hence the universe at which the concrete system
`AlgebraicGeometry.Space.modulePullbackSystem` exists.

Universal injectivity at a test scheme `T` quantifies over the test schemes over `T`, so its
locality is proved at an arbitrary test scheme `T'' ⟶ T` by covering `T''` with the inverse
image of the given covering sieve.

## References

* [Stacks Project, Tag 083H](https://stacks.math.columbia.edu/tag/083H)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 083I](https://stacks.math.columbia.edu/tag/083I)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : ModuleMapSituation.{u, u} B S hS)

/-! ### A flat jointly surjective family of base-change spaces inside a covering sieve -/

/-- **A covering sieve of a test scheme yields a flat jointly surjective family of base-change
spaces.**  An fpqc covering sieve of a test scheme `T` over `Y` contains a family of arrows
`T_i ⟶ T` whose comparisons `X ×_Y T_i ⟶ X ×_Y T` of base-change spaces are flat and jointly
surjective on points.

The family is the fpqc covering family inside the sieve; flatness and joint surjectivity pass
to the base-change spaces because the comparison square over a morphism of test schemes is
cartesian. -/
private theorem exists_flat_jointlySurjective_baseChangeMap {T : D.SchemesOver} {R : Sieve T}
    (hR : R ∈ fpqcTopology D.Y T) :
    ∃ (I : Type (u + 1)) (T' : I → D.SchemesOver) (k : ∀ i, T' i ⟶ T), (∀ i, R.arrows (k i)) ∧
      (∀ i, IsFlat B S hS (D.baseChangeMap (k i)).hom) ∧
        IsJointlySurjective B S hS (fun i => (D.baseChangeSpace (T' i)).1)
          fun i => (D.baseChangeMap (k i)).hom := by
  obtain ⟨I, T', k, hk, hcov, hsurj⟩ :=
    exists_isFpqcCovering_jointlySurjective_family_of_mem_fpqcTopology hR
  exact ⟨I, T', k, hk, fun i => D.isFlat_baseChangeMap (k i) (hcov.1 i),
    D.isJointlySurjective_baseChangeMap T' k hsurj⟩

/-- A subterminal presheaf on the test schemes over `Y` is an fpqc sheaf as soon as the condition
`P` it expresses holds over every test scheme admitting a covering sieve all of whose members
satisfy `P`. -/
private theorem isSheaf_fpqcTopology_of_forall_mem_sieve {F : (D.SchemesOver)ᵒᵖ ⥤ Type*}
    (hsub : ∀ W, Subsingleton (F.obj W)) {P : D.SchemesOver → Prop}
    (hP : ∀ T, Nonempty (F.obj (op T)) ↔ P T)
    (h : ∀ (T : D.SchemesOver) (R : Sieve T), R ∈ fpqcTopology D.Y T →
      (∀ ⦃T' : D.SchemesOver⦄ (k : T' ⟶ T), R.arrows k → P T') → P T) :
    Presheaf.IsSheaf (fpqcTopology D.Y) F := by
  rw [Presheaf.isSheaf_iff_nonempty_of_subsingleton]
  exact fun T R hR hne => (hP T).2 (h T R hR fun _ k hk => (hP _).1 (hne k hk))

/-! ### Stacks 083H -/

/-- **Stacks 083H**, surjectivity clause.  The locus of test schemes over `Y` on which the base
change of `u` is surjective is a sheaf for the fpqc topology.

The locus is subterminal, so the sheaf condition is the implication from surjectivity at every
member of a covering sieve to surjectivity at its target.  A covering sieve contains a flat
family which is jointly surjective after base change, and surjectivity descends along such a
family. -/
@[stacks 083H "F_surj"]
theorem isSheaf_surjFunctor :
    Presheaf.IsSheaf (fpqcTopology D.Y) (D.surjFunctor (modulePullbackSystem B S hS)) := by
  refine D.isSheaf_fpqcTopology_of_forall_mem_sieve
      (fun W => D.surjFunctor_obj_subsingleton (modulePullbackSystem B S hS) W.unop)
      (D.nonempty_surjFunctor_obj_iff (modulePullbackSystem B S hS)) fun T R hR hne => ?_
  obtain ⟨I, T', k, hk, hflat, hjs⟩ := D.exists_flat_jointlySurjective_baseChangeMap hR
  refine epi_of_forall_epi_modulePullback_map_of_isFlat B S hS
    (fun i => D.baseChangeMap (k i)) hflat hjs
    (D.baseChangeHom (modulePullbackSystem B S hS) T) fun i => ?_
  exact (D.epi_baseChangeMap_map_iff (modulePullbackSystem B S hS) (k i)).2 (hne (k i) (hk i))

/-- **Stacks 083H**, vanishing clause.  The locus of test schemes over `Y` on which the base
change of `u` vanishes is a sheaf for the fpqc topology.

The locus is subterminal, so the sheaf condition is the implication from vanishing at every
member of a covering sieve to vanishing at its target, and vanishing descends along the flat
jointly surjective family of base-change spaces the sieve contains. -/
@[stacks 083H "F_zero"]
theorem isSheaf_zeroFunctor :
    Presheaf.IsSheaf (fpqcTopology D.Y) (D.zeroFunctor (modulePullbackSystem B S hS)) := by
  refine D.isSheaf_fpqcTopology_of_forall_mem_sieve
      (fun W => D.zeroFunctor_obj_subsingleton (modulePullbackSystem B S hS) W.unop)
      (D.nonempty_zeroFunctor_obj_iff (modulePullbackSystem B S hS)) fun T R hR hne => ?_
  obtain ⟨I, T', k, hk, hflat, hjs⟩ := D.exists_flat_jointlySurjective_baseChangeMap hR
  refine eq_zero_of_forall_modulePullback_map_eq_zero_of_isFlat B S hS
    (fun i => D.baseChangeMap (k i)) hflat hjs
    (D.baseChangeHom (modulePullbackSystem B S hS) T) fun i => ?_
  exact (D.baseChangeMap_map_eq_zero_iff (modulePullbackSystem B S hS) (k i)).2 (hne (k i) (hk i))

/-- **Stacks 083H**, isomorphism clause.  The locus of test schemes over `Y` on which the base
change of `u` is an isomorphism is a sheaf for the fpqc topology.

The locus is subterminal, so the sheaf condition is the implication from being an isomorphism at
every member of a covering sieve to being one at its target, and being an isomorphism descends
along the flat jointly surjective family of base-change spaces the sieve contains. -/
@[stacks 083H "F_iso"]
theorem isSheaf_isoFunctor :
    Presheaf.IsSheaf (fpqcTopology D.Y) (D.isoFunctor (modulePullbackSystem B S hS)) := by
  refine D.isSheaf_fpqcTopology_of_forall_mem_sieve
      (fun W => D.isoFunctor_obj_subsingleton (modulePullbackSystem B S hS) W.unop)
      (D.nonempty_isoFunctor_obj_iff (modulePullbackSystem B S hS)) fun T R hR hne => ?_
  obtain ⟨I, T', k, hk, hflat, hjs⟩ := D.exists_flat_jointlySurjective_baseChangeMap hR
  refine isIso_of_forall_isIso_modulePullback_map_of_isFlat B S hS
    (fun i => D.baseChangeMap (k i)) hflat hjs
    (D.baseChangeHom (modulePullbackSystem B S hS) T) fun i => ?_
  exact (D.isIso_baseChangeMap_map_iff (modulePullbackSystem B S hS) (k i)).2 (hne (k i) (hk i))

/-- **The universal-injectivity locus is an fpqc sheaf.**  The locus of test schemes over `Y` on
which the base change of `u` is universally injective, that is, injective after every further
base change, is a sheaf for the fpqc topology on all test schemes over `Y`.  This is a variant
of the injectivity clause of Stacks 083H, not that clause itself: Stacks' `F_inj` asks that
`u_T` be injective, a condition stable only under flat base change, and its sheaf property is
`AlgebraicGeometry.Space.ModuleMapSituation.isSheaf_flatInjFunctor`.

The locus is subterminal, so the sheaf condition is the implication from universal injectivity
at every member of a covering sieve to universal injectivity at its target.  The latter asks
for injectivity of the base change at every test scheme `T''` over `T`; the inverse image of
the covering sieve is a covering sieve of `T''`, and injectivity at each member of that sieve
is one instance of universal injectivity at the corresponding member of the given sieve, so
injectivity at `T''` follows by descent along the flat jointly surjective family of base-change
spaces. -/
theorem isSheaf_injFunctor :
    Presheaf.IsSheaf (fpqcTopology D.Y) (D.injFunctor (modulePullbackSystem B S hS)) := by
  refine D.isSheaf_fpqcTopology_of_forall_mem_sieve
      (fun W => D.injFunctor_obj_subsingleton (modulePullbackSystem B S hS) W.unop)
      (D.nonempty_injFunctor_obj_iff (modulePullbackSystem B S hS))
      fun T R hR hne T'' h => ?_
  obtain ⟨I, T', k, hk, hflat, hjs⟩ := D.exists_flat_jointlySurjective_baseChangeMap
    ((fpqcTopology D.Y).pullback_stable h hR)
  refine mono_of_forall_mono_modulePullback_map_of_isFlat B S hS
    (fun i => D.baseChangeMap (k i)) hflat hjs
    (D.baseChangeHom (modulePullbackSystem B S hS) T'') fun i => ?_
  exact (D.mono_baseChangeMap_map_iff (modulePullbackSystem B S hS) (k i)).2
    (hne (k i ≫ h) (hk i) (T' i) (𝟙 (T' i)))

end ModuleMapSituation

end AlgebraicGeometry.Space

end
