module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback
import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone

/-!
# Derived pullback preserves perfectness

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `E` be a perfect object of
`D(𝒪_Y)`. Then `Lf^* E` is a perfect object of `D(𝒪_X)`, for any models of the two derived
categories.

This is the perfect-complex companion of Stacks 09U7, which
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback`
proves for pseudo-coherence, and it is proved along the same lines: replace `E` by a K-flat
representative, so that `Lf^*E` becomes the class of the *degreewise* pullback `f^*P`, and then
check perfectness of `f^*P` cover member by cover member.

## Main definitions

* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.hasDerivedCategoryOXModOfStructureSheafRing`:
  a model of `D(𝒪_X)` at the spelling `SheafOfModules (structureSheafRing X)`, read at the
  spelling `StrictlyPerfect.OXMod X`. It is not an instance.

## Main results

* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfectComplex_modulePullback`:
  degreewise pullback carries a K-flat perfect complex to a perfect complex.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback`:
  **the derived pullback of a perfect object is perfect**, for any models of `D(𝒪_X)` and
  `D(𝒪_Y)`.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_uniqFunctor_obj`:
  perfectness is carried across a change of model of the derived category by the canonical
  equivalence of two localizations.

## Implementation notes

*The proof runs on complexes.* A representative `K` of the given object is resolved by a K-flat
complex `P` (Tag 06YS); `P` is a perfect complex because perfectness of complexes is invariant
under quasi-isomorphisms (`AlgebraicGeometry.RingedSpace.isPerfectComplex_iff_of_quasiIso`), and
`Lf^*` of the class of `P` is the class of `f^*P`
(`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`). No derived category of an open subspace
occurs, and the two models of `D(𝒪_X)` and `D(𝒪_Y)` are binders. The derived pullback needs no
hypothesis either: its `HasLeftDerivedFunctor` instance is unconditional
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy`).

*The cover on the source.* `Stacks.Cohomology.PerfectComplexes.IsPerfectComplex` carries a
cover rather than a pointwise condition, so the cover of `X` is the family of preimages of the
cover of `Y`, indexed by the same type; it covers because `f(x)` lies in some member for every
`x`. Over one member, `f^*Q` is strictly perfect by Stacks 09U6
(`Stacks.StrictlyPerfect.Pullback.isStrictlyPerfect_modulePullback`), the pullback of the local
quasi-isomorphism is again one because both of its ends are K-flat
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect` and
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex` feeding
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.quasiIso_modulePullback_of_kFlat`), and
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictComplexPullbackIso` identifies
`(f|_{f⁻¹V})^*(P|_V)` with `(f^*P)|_{f⁻¹V}`.

*`QuasiIso` of a composite is hoisted.*
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.quasiIso_comp_isIso` is stated over an
abstract abelian category for the reason given for
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isIso_homologyMap_comp_isIso` and
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.epi_homologyMap_comp_isIso`:
at the ringed-space vocabulary the instance arguments of the homology of a complex of
sheaves of modules are reached through two spellings of the structure sheaf, and the search for
the composite instance does not cross them.

*Spellings of the two models.* The models are binders at the spelling
`SheafOfModules (structureSheafRing _)` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, whose instance arguments are
the ones instance search has to find at a call site. `Stacks.Cohomology.PerfectComplexes.IsPerfect`
is stated at the spelling `StrictlyPerfect.OXMod _`, which instance search does not identify with
the first, so it reads the models through the named crossing
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.hasDerivedCategoryOXModOfStructureSheafRing`.
The crossing is attached to the theorem alone by `attribute [local instance] … in`; a
declaration that meets the two spellings attaches it in the same way, until the spellings of
`D(𝒪_X)` are unified. The predicates are written with their full names:
`AlgebraicGeometry.RingedSpace.IsPerfect`, visible here through
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone`, would otherwise be found
first, from the enclosing namespace.

*Change of localization model.*
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_uniqFunctor_obj` takes the two
`HasDerivedCategory` instances as explicit arguments rather than as instance binders, since
both are instances for the same category and only one of them can be found by search.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 09U6](https://stacks.math.columbia.edu/tag/09U6)
* [Stacks Project, Tag 09U7](https://stacks.math.columbia.edu/tag/09U7)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect RingedSpaceModuleAdjunction Stacks.Cohomology.HigherDirectImage

namespace AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

universe u d d' w₁ w₂

/-- Composing a quasi-isomorphism with an isomorphism gives a quasi-isomorphism. -/
theorem quasiIso_comp_isIso {A : Type*} [Category A] [Abelian A]
    {K L M : CochainComplex A ℤ} (g : K ⟶ L) (h : L ⟶ M) (hg : QuasiIso g) (hh : IsIso h) :
    QuasiIso (g ≫ h) := by
  have := hg
  have := hh
  infer_instance

/-- **Degreewise pullback preserves perfectness of a K-flat complex.**  The cover of `X` is the
family of preimages of a cover of `Y` witnessing perfectness of `P`.  Over one member, the
pullback of the strictly perfect complex is strictly perfect (Stacks 09U6), the pullback of the
local quasi-isomorphism is a quasi-isomorphism because both of its ends are K-flat, and
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictComplexPullbackIso` moves the
target to the restriction of `f^*P`. -/
theorem isPerfectComplex_modulePullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules Y) ℤ) (hPk : KFlat Y P)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfectComplex (X := Y) P) :
    Stacks.Cohomology.PerfectComplexes.IsPerfectComplex (X := X)
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  obtain ⟨I, V, hcover, hV⟩ :=
    (Stacks.Cohomology.PerfectComplexes.isPerfectComplex_iff (X := Y) P).mp hP
  refine (Stacks.Cohomology.PerfectComplexes.isPerfectComplex_iff (X := X) _).mpr
    ⟨I, fun i => preimageOpen f (V i), ?_, fun i => ?_⟩
  · apply top_unique
    intro x _
    have hfx : f.hom.base x ∈ iSup V := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hfx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · obtain ⟨Q, hQ, α, hα⟩ := hV i
    have h1 : QuasiIso
        (((modulePullback (restrictedMorphism f (V i))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α) :=
      quasiIso_modulePullback_of_kFlat (restrictedMorphism f (V i)) α hα
        (kFlat_of_isStrictlyPerfect Q hQ) (kFlat_restrictComplex (V i) P hPk)
    exact ⟨((modulePullback (restrictedMorphism f (V i))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Q,
      Stacks.StrictlyPerfect.Pullback.isStrictlyPerfect_modulePullback
        (restrictedMorphism f (V i)) Q hQ,
      ((modulePullback (restrictedMorphism f (V i))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map α ≫ (restrictComplexPullbackIso f (V i) P).inv,
      quasiIso_comp_isIso _ _ h1 (Iso.isIso_inv (restrictComplexPullbackIso f (V i) P))⟩

/-- A model of `D(𝒪_X)` at the spelling `SheafOfModules (structureSheafRing X)`, read at the
spelling `StrictlyPerfect.OXMod X` that `Stacks.Cohomology.PerfectComplexes.IsPerfect` uses. The
two categories agree by `rfl`, but instance search does not cross the spellings. This is not an
instance: a declaration where the two spellings meet attaches it with
`attribute [local instance] … in`, until the spellings of `D(𝒪_X)` are unified. -/
@[instance_reducible] def hasDerivedCategoryOXModOfStructureSheafRing (X : RingedSpace.{u, u})
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))] :
    HasDerivedCategory.{w₁} (OXMod.{u, u} X) :=
  inferInstanceAs (HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X)))

attribute [local instance] hasDerivedCategoryOXModOfStructureSheafRing in
/-- **The derived pullback of a perfect object of `D(𝒪_Y)` is a perfect object of `D(𝒪_X)`**,
for any models of the two derived categories.

A representative `K` of the given object is resolved by a K-flat complex `P` (Tag 06YS); `P` is
again a perfect complex, being quasi-isomorphic to `K`, and `Lf^*` of the object is the class of
the degreewise pullback `f^*P`, which is perfect by
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfectComplex_modulePullback`. -/
@[stacks 09UA]
theorem isPerfect_derivedPullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    [hX : HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [hY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y) E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj E) := by
  obtain ⟨K, hK, ⟨eKE⟩⟩ := hE
  obtain ⟨P, p, hPk, -, hp, -⟩ := exists_kFlatResolution Y K
  have : IsIso ((DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Y))).map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := SheafOfModules.{u} (structureSheafRing Y))
      p).2 hp
  have e : (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing X))).obj
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj E :=
    (Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat f P hPk).symm ≪≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).mapIso
        (asIso ((DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Y))).map p) ≪≫
          eKE)
  exact ⟨_, isPerfectComplex_modulePullback f P hPk
    ((AlgebraicGeometry.RingedSpace.isPerfectComplex_iff_of_quasiIso (X := Y) p hp).2 hK), ⟨e⟩⟩

/-- **Perfectness survives a change of model of the derived category.**  The canonical
equivalence between two localizations of the complexes at the quasi-isomorphisms carries a
perfect object to a perfect object: the representative does not change, and the isomorphism
exhibiting it is composed with `CategoryTheory.Localization.compUniqFunctor`. -/
@[stacks 0F8T]
theorem isPerfect_uniqFunctor_obj {X : RingedSpace.{u, u}}
    (inst₁ : HasDerivedCategory.{d} (OXMod.{u, u} X))
    (inst₂ : HasDerivedCategory.{d'} (OXMod.{u, u} X))
    (K : @DerivedCategory (OXMod.{u, u} X) _ _ inst₁)
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} X inst₁ K) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d'} X inst₂
      ((Localization.uniq (@DerivedCategory.Q (OXMod.{u, u} X) _ _ inst₁)
        (@DerivedCategory.Q (OXMod.{u, u} X) _ _ inst₂)
        (HomologicalComplex.quasiIso (OXMod.{u, u} X) (ComplexShape.up ℤ))).functor.obj K) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  exact ⟨E, hE, ⟨((Localization.compUniqFunctor _ _ _).app E).symm ≪≫
    (Localization.uniq _ _ _).functor.mapIso e⟩⟩

end AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

end
