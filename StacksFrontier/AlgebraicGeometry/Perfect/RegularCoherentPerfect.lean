module

public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
public import StacksFrontier.Homology.Perfect.Regular
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalCriterion
import all StacksFrontier.AlgebraicGeometry.Perfect.PerfectClosedImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A coherent module on a regular scheme is perfect

Let `X` be a regular scheme and let `ℱ` be a coherent `𝒪_X`-module. Then `ℱ`, placed in degree
zero, is a perfect object of the derived category of `𝒪_X`-modules. This is the degree-zero case
of the forward half of [Stacks, Tag 0FDC], which asserts the same for every object of
`D^b_{Coh}(𝒪_X)`.

No quasi-compactness is needed: the statement is affine-local on `X`, and the affine opens
supplied by the definition of a regular scheme already cover it.

## Main definitions

* `AlgebraicGeometry.restrictIsoTilde`: the restriction of a quasi-coherent `𝒪_X`-module to an
  affine open `V`, read as a module on the open subspace of the underlying ringed space, is the
  inverse image along `V ≅ Spec Γ(X, V)` of the sheaf associated to the `Γ(X, V)`-module
  `Γ(ℱ, V)`.

## Main results

* `AlgebraicGeometry.exists_isStrictlyPerfect_restrictComplex_single`: the affine-local core. On
  an affine open `V` whose ring of sections is regular, a quasi-coherent `𝒪_X`-module of finite
  type placed in degree zero has a strictly perfect model over `V`.
* `AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular`: a coherent module on a regular
  scheme, placed in degree zero, is a perfect object of `D(𝒪_X)`.

## Implementation notes

The proof is the local one. On an affine open `V` of `X` the sections `Γ(ℱ, V)` form a finite
module over `Γ(X, V)`, by `Stacks.AlgebraicGeometry.CoherentFinite.finite_sections`, since a
coherent module is quasi-coherent and of finite type. When `Γ(X, V)` is regular, a finite module
over it is perfect — the module half of [Stacks, Tag 066Z],
`StacksDraft.Perfect.isPerfectModule_iff_finite_and_isPerfect_iff_bounded_finiteCohomology` — so
it admits a bounded resolution by finite projective `Γ(X, V)`-modules. The associated complex on
`Spec Γ(X, V)` is strictly perfect and represents `Γ(ℱ, V)^~` in degree zero, which is
`AlgebraicGeometry.exists_isStrictlyPerfect_tilde_model`; pulling it back along
`V ≅ Spec Γ(X, V)` keeps it strictly perfect, and `AlgebraicGeometry.restrictIsoTilde`
identifies what it represents with the restriction of `ℱ` to `V`. The local criterion for
perfectness, [Stacks, Tag 08CN]
(`AlgebraicGeometry.RingedSpace.isPerfect_of_strictlyPerfect_local_models`), then concludes.

This is the same chain as `AlgebraicGeometry.isPerfect_pushforward_structureSheaf`
([Stacks, Tag 0G2E]), which treats `i_*𝒪_Z` for a perfect closed immersion `i`; the two differ
only in how the finite module over `Γ(X, V)` and its identification with a restriction are
produced. The pieces that are common are reused from that file through `import all`, since they
are stated there as private.

`AlgebraicGeometry.restrictIsoTilde` is assembled from
`Stacks.Modules.tildeIsoRestrictFromSpec`, which identifies the restriction of a quasi-coherent
module along `AlgebraicGeometry.IsAffineOpen.fromSpec` with a sheaf associated to a module, and
`AlgebraicGeometry.IsAffineOpen.isoSpec_hom_fromSpec`, which factors the inclusion of the affine
open as `V ≅ Spec Γ(X, V)` followed by `fromSpec`. The two spellings of restriction to an open —
`AlgebraicGeometry.RingedSpace.restrictModules`, in which the local criterion is phrased, and
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, in which the quasi-coherent theory is
phrased — are identified by
`Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict`.

The module `ℱ` is taken to be of type `AlgebraicGeometry.Scheme.Modules`, not of the
definitionally equal type `Stacks.StrictlyPerfect.OXMod X.toRingedSpace`: the `Module Γ(X, V)`
structure on `Γ(ℱ, V)` is found by instance search only at the former spelling.

The covering used for the local criterion is indexed by the points of `X`, each point taken to
the affine open with regular ring of sections that the definition of
`AlgebraicGeometry.IsRegular` supplies at it. Regularity of the ring of sections of an
*arbitrary* affine open — which would follow from `AlgebraicGeometry.isRegular_tfae` — is
therefore not needed.

## References

* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 066Z](https://stacks.math.columbia.edu/tag/066Z)
* [Stacks Project, Tag 08CN](https://stacks.math.columbia.edu/tag/08CN)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open AlgebraicGeometry.RingedSpace (restrictModules)

namespace AlgebraicGeometry

universe u d

attribute [local instance] HasDerivedCategory.standard

/-- **The restriction of a quasi-coherent module to an affine open is a tilde.** For `ℱ` a
quasi-coherent `𝒪_X`-module and `V` an affine open of `X`, the restriction of `ℱ` to the open
subspace `V` of the underlying ringed space is the inverse image along `V ≅ Spec Γ(X, V)` of the
sheaf associated to the `Γ(X, V)`-module `Γ(ℱ, V)`.

This is `Stacks.Modules.tildeIsoRestrictFromSpec`, which states the same for the restriction
along `AlgebraicGeometry.IsAffineOpen.fromSpec`, carried across the factorisation
`AlgebraicGeometry.IsAffineOpen.isoSpec_hom_fromSpec` of the inclusion of `V`. -/
def restrictIsoTilde {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (V : X.Opens) (hV : IsAffineOpen V) :
    (restrictModules X.toRingedSpace V).obj F ≅
      (Scheme.Modules.pullback hV.isoSpec.hom).obj
        ((AlgebraicGeometry.tilde.functor Γ(X, V)).obj (ModuleCat.of Γ(X, V) Γ(F, V))) :=
  letI : IsAffine V.toScheme := hV
  (Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X V).app F ≪≫
    (Scheme.Modules.restrictFunctorCongr (f := hV.isoSpec.hom ≫ hV.fromSpec) (g := V.ι)
      hV.isoSpec_hom_fromSpec).symm.app F ≪≫
    (Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).app F ≪≫
    (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapIso
      (Stacks.Modules.tildeIsoRestrictFromSpec F hV).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hV.isoSpec.hom).app _

/-- **A strictly perfect model over an affine open with regular ring of sections.** Let `ℱ` be a
quasi-coherent `𝒪_X`-module of finite type and let `V` be an affine open of `X` whose ring of
sections `Γ(X, V)` is regular. Then the complex with `ℱ` in degree zero becomes, after
restriction to `V`, isomorphic in the derived category to a strictly perfect complex.

The sections `Γ(ℱ, V)` form a finite, hence perfect, `Γ(X, V)`-module; a bounded resolution of it
by finite projective modules sheafifies to a strictly perfect complex on `Spec Γ(X, V)`, and
pulling that back along `V ≅ Spec Γ(X, V)` gives the model. -/
theorem exists_isStrictlyPerfect_restrictComplex_single {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (V : X.Opens) (hV : IsAffineOpen V) (hreg : IsRegularRing Γ(X, V)) :
    ∃ P : CochainComplex (OXMod.{u, u} (X.toRingedSpace.restrict V.isOpenEmbedding)) ℤ,
      IsStrictlyPerfect P ∧ Nonempty (DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (RingedSpace.restrictComplex
          ((CochainComplex.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) V)) := by
  let R : CommRingCat.{u} := Γ(X, V)
  let : IsRegularRing R := hreg
  have hfin : Module.Finite Γ(X, V) Γ(F, V) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F hV
  let M : ModuleCat.{u} R := ModuleCat.of Γ(X, V) Γ(F, V)
  have hM : StacksDraft.Perfect.IsPerfectModule (R := R) M :=
    ((StacksDraft.Perfect.isPerfectModule_iff_finite_and_isPerfect_iff_bounded_finiteCohomology.{u,
      u} (R := R)).1 Γ(F, V)).mpr hfin
  obtain ⟨P₀, hP₀, ⟨e₀⟩⟩ := exists_isStrictlyPerfect_tilde_model M hM
  let eV := hV.isoSpec
  let H := Scheme.Modules.pullback eV.hom
  let : H.Additive := by infer_instance
  let : H.IsLeftAdjoint := (Scheme.Modules.pullbackPushforwardAdjunction eV.hom).isLeftAdjoint
  let : PreservesFiniteColimits H := ⟨fun _ _ _ => inferInstance⟩
  let : PreservesFiniteLimits (Scheme.Modules.restrictFunctor eV.hom) :=
    preservesFiniteLimits_restrictFunctor eV.hom
  let : PreservesFiniteLimits H := preservesFiniteLimits_of_natIso
    (F := Scheme.Modules.restrictFunctor eV.hom) (G := H)
    (Scheme.Modules.restrictFunctorIsoPullback eV.hom)
  let G := restrictModules X.toRingedSpace V
  refine ⟨(H.mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀,
    isStrictlyPerfect_pullback_of_iso eV P₀ hP₀, ⟨?_⟩⟩
  exact (H.mapDerivedCategoryFactors.app P₀).symm ≪≫
    H.mapDerivedCategory.mapIso e₀ ≪≫
    (H.mapDerivedCategorySingleFunctor 0).app ((AlgebraicGeometry.tilde.functor R).obj M) ≪≫
    (DerivedCategory.singleFunctor
      (OXMod.{u, u} (X.toRingedSpace.restrict V.isOpenEmbedding)) 0).mapIso
        (restrictIsoTilde F V hV).symm ≪≫
    DerivedCategory.Q.mapIso ((G.mapCochainComplexSingleFunctor 0).app F).symm

/-- **A coherent module on a regular scheme is perfect.** Let `X` be a regular scheme and let `ℱ`
be a coherent `𝒪_X`-module. Then `ℱ`, placed in degree zero, is a perfect object of the derived
category of `𝒪_X`-modules.

This is the degree-zero case of the forward half of [Stacks, Tag 0FDC]. Quasi-compactness of `X`
is not assumed: the affine opens with regular ring of sections provided by
`AlgebraicGeometry.IsRegular` cover `X`, and over each of them
`AlgebraicGeometry.exists_isStrictlyPerfect_restrictComplex_single` supplies a strictly perfect
model, which is all the local criterion for perfectness needs. -/
@[sga "6 I 5.11" "special case"]
theorem isPerfect_single_of_isCoherent_of_isRegular {X : Scheme.{u}} (hX : IsRegular X)
    [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
    (F : X.Modules) [F.IsCoherent] :
    RingedSpace.IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) := by
  classical
  have hqft := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have : F.IsQuasicoherent := hqft.1
  have : F.IsFiniteType := hqft.2
  refine RingedSpace.isPerfect_of_strictlyPerfect_local_models X.toRingedSpace _
    ⟨(CochainComplex.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F, ⟨Iso.refl _⟩,
      (X : Type u), (fun x => ((hX x).choose.1 : X.Opens)), ?_, ?_⟩
  · exact top_unique fun y _ => Opens.mem_iSup.mpr ⟨y, (hX y).choose_spec.1⟩
  · exact fun x => exists_isStrictlyPerfect_restrictComplex_single F _ (hX x).choose.2
      (hX x).choose_spec.2

end AlgebraicGeometry

end
