module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.QcohUniversalDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardFromDisjointOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.FlatPushforwardOfKInjectives
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A complex pushed forward from an affine open computes its derived direct image

Let `f : X ⟶ Y` be a morphism of schemes and let `j : U ⟶ X` be the inclusion of an open
subscheme. This file proves that the canonical comparison `f_*(j_*𝒢^•) ⟶ Rf_*(j_*𝒢^•)` is
invertible for every complex `𝒢^•` of quasi-coherent `𝒪_U`-modules, provided `j` and the
composite `g = j ≫ f` are affine morphisms. **No hypothesis is placed on `f` itself**, and in
general the comparison `f_*ℱ^• ⟶ Rf_*ℱ^•` is *not* invertible for a complex `ℱ^•` of
quasi-coherent modules — which is why [Stacks, Tag 0CRX] needs a dévissage, and this is the
class of complexes on which that dévissage starts.

The argument is the one the source gives. Choose a K-injective resolution `t : 𝒢^• ⟶ ℐ^•` of
`𝒢^•` *as a complex of `𝒪_U`-modules*. Then

* `j_*ℐ^•` is K-injective, because `j` is flat and so `j^*` is exact ([Stacks, Tag 08BJ], in the
  form `RingedSpaceModuleAdjunction.isKInjective_modulePushforward_of_isFlat`);
* `j_*t` is a quasi-isomorphism, because `𝒢^•` has quasi-coherent terms and `j` is affine
  ([Stacks, Tag 0G9N] for an affine morphism, in the form
  `AlgebraicGeometry.quasiIso_modulePushforward_map_of_isAffineHom`);

so `j_*t : j_*𝒢^• ⟶ j_*ℐ^•` is itself a K-injective resolution, and the comparison at `j_*𝒢^•`
is invertible exactly when `f_*(j_*t)` is a quasi-isomorphism. Under the composition isomorphism
of direct images that map is `g_*t`, and `g_*t` is a quasi-isomorphism by the same affine case of
[Stacks, Tag 0G9N], now for `g`.

## Main results

* `AlgebraicGeometry.isAffineHom_of_isAffine_of_affineDiagonal` — a morphism from an affine
  scheme to a scheme with affine diagonal is affine. This is what makes `g = j ≫ f` affine when
  `U` is an affine open of `X` and `Y` has affine diagonal.
* `AlgebraicGeometry.isFlat_toShHom_opensι` — the inclusion of an open subscheme is flat.
* `AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_pushforward_of_isAffineHom` —
  **the comparison `f_*(j_*𝒢^•) ⟶ Rf_*(j_*𝒢^•)` is invertible**, at an arbitrary chosen model of
  the two derived categories.

## Implementation notes

The hypotheses on `j` are `IsAffineHom j` together with flatness of the underlying morphism of
ringed spaces, and they are what the two inputs need; for the inclusion of an affine open of a
scheme with affine diagonal both hold, the first by
`Stacks.Cohomology.QcohDelta.isAffineHom_ι_of_isAffineOpen` and the second by
`AlgebraicGeometry.isFlat_toShHom_opensι`. Stating the result for an open subscheme rather than
for a general affine `j` is forced by the flatness input: `j_*` preserves K-injective complexes
because `j^*` is exact, which holds for a flat morphism and not for an affine one.

No Stacks attribute is placed. The statement is a step in the proof of [Stacks, Tag 0CRX], not
one of its assertions, and the affine case of [Stacks, Tag 0G9N] it is assembled from carries no
attribute either, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardAnyModel.lean`.

## References

* [Stacks Project, Tag 0CRX](https://stacks.math.columbia.edu/tag/0CRX)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 01SG](https://stacks.math.columbia.edu/tag/01SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry

universe u w

/-! ### Two geometric inputs -/

/-- **A morphism from an affine scheme to a scheme with affine diagonal is affine.** The graph of
`g : V ⟶ Y` is a base change of the diagonal of `Y`, hence affine, and the second projection
`V ×_{Spec ℤ} Y ⟶ Y` is a base change of `V ⟶ Spec ℤ`, hence affine; `g` is their composite.

That is the content of `CategoryTheory.MorphismProperty.hasOfPostcompProperty_iff_le_diagonal`
applied to the affine morphisms, which are multiplicative and stable under base change. -/
@[ega "II 1.6.2" "(v), Z = Spec ℤ"]
public theorem isAffineHom_of_isAffine_of_affineDiagonal {V Y : Scheme.{u}} [IsAffine V]
    [IsAffineHom (pullback.diagonal (terminal.from Y))] (g : V ⟶ Y) : IsAffineHom g := by
  refine isAffineHom_of_forall_exists_isAffineOpen g fun y => ?_
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : Y.Opens))
    (x := y) (by simp)
  refine ⟨W, hyW, hW, ?_⟩
  have : IsAffineHom W.ι := Stacks.Cohomology.QcohDelta.isAffineHom_ι_of_isAffineOpen Y W hW
  have : IsAffine (pullback g W.ι) := inferInstance
  exact IsAffine.of_isIso (pullbackRestrictIsoRestrict g W).inv

/-- **The inclusion of an open subscheme is flat**: its germ maps are isomorphisms, and a
bijective ring homomorphism is flat. -/
public theorem isFlat_toShHom_opensι (X : Scheme.{u}) (U : X.Opens) :
    AlgebraicGeometry.IsFlat U.ι.toLRSHom.toShHom :=
  isFlat_ofRestrict X.toRingedSpace U

/-- **A map of complexes isomorphic to a quasi-isomorphism is a quasi-isomorphism**, in the
shape of a commuting square with invertible horizontal edges. -/
public theorem quasiIso_of_comm_square {C : Type*} [Category* C] [Abelian C]
    {K L K' L' : CochainComplex C ℤ} (φ : K ⟶ L) (ψ : K' ⟶ L') (a : K ≅ K') (b : L ≅ L')
    (hcomm : φ ≫ b.hom = a.hom ≫ ψ) (h : QuasiIso ψ) : QuasiIso φ := by
  have : QuasiIso (φ ≫ b.hom) := by
    rw [hcomm]
    infer_instance
  exact quasiIso_of_comp_right φ b.hom

/-- **The composition isomorphism of direct images, read on a map of complexes.** If `g_*t` is a
quasi-isomorphism for `g = j ≫ f`, then so is `f_*(j_*t)`: the two differ by the isomorphism
`RingedSpaceModuleAdjunction.modulePushforwardComp` at the source and at the target. -/
public theorem quasiIso_pushforward_pushforward_map {U X Y : Scheme.{u}} (j : U ⟶ X) (f : X ⟶ Y)
    {K J : CochainComplex (SheafOfModules.{u} U.ringCatSheaf) ℤ} (t : K ⟶ J)
    (h : QuasiIso (((modulePushforward
      (j.toLRSHom.toShHom ≫ f.toLRSHom.toShHom)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map t)) :
    QuasiIso ((((modulePushforward j.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙
      ((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ))).map t) :=
  let e := Functor.mapHomologicalComplexCompIso
    (modulePushforwardComp j.toLRSHom.toShHom f.toLRSHom.toShHom) (ComplexShape.up ℤ)
  quasiIso_of_comm_square _ _ (e.app K) (e.app J) (e.hom.naturality t) h

/-! ### The comparison at a complex pushed forward from an open subscheme -/

namespace AnyModel

variable {U X Y : Scheme.{u}} (j : U ⟶ X) (f : X ⟶ Y)
  [HasDerivedCategory.{w} (SheafOfModules.{u} U.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} Y.ringCatSheaf)]

omit [HasDerivedCategory (SheafOfModules U.ringCatSheaf)] in
/-- **A complex of quasi-coherent modules pushed forward from an open subscheme computes its own
derived direct image.** Let `j : U ⟶ X` be an affine flat morphism of schemes — the inclusion of
an affine open of a scheme with affine diagonal, in the application — let `f : X ⟶ Y` be an
arbitrary morphism of schemes such that `j ≫ f` is affine, and let `K` be a complex of
`𝒪_U`-modules with quasi-coherent terms. Then the canonical comparison
`f_*(j_*K) ⟶ Rf_*(j_*K)` is invertible.

No hypothesis is placed on `f`. See the module documentation for the argument. -/
public theorem isIso_derivedPushforwardUnit_app_pushforward_of_isAffineHom
    [IsAffineHom j] [IsAffineHom (j ≫ f)]
    (hjflat : AlgebraicGeometry.IsFlat j.toLRSHom.toShHom)
    (K : CochainComplex (SheafOfModules.{u} U.ringCatSheaf) ℤ)
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    IsIso ((derivedPushforwardUnit.{w} f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
          (ComplexShape.up ℤ)).obj
        (((pushforwardSheafOfModules j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) := by
  obtain ⟨J, t, hJ, ht⟩ := exists_quasiIso_isKInjective_ringCatSheaf U K
  have hjJ : CochainComplex.IsKInjective
      (((pushforwardSheafOfModules j).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    isKInjective_modulePushforward_of_isFlat j.toLRSHom.toShHom hjflat J hJ
  have hjt : QuasiIso (((pushforwardSheafOfModules j).mapHomologicalComplex
      (ComplexShape.up ℤ)).map t) :=
    quasiIso_modulePushforward_map_of_isAffineHom j hqc t hJ ht
  refine (Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff
    (exists_quasiIso_isKInjective_ringCatSheaf X)
    (pushforwardToDerivedCategory.{w} f) (derivedPushforward.{w} f)
    (derivedPushforwardUnit.{w} f) _ hjJ hjt).2 ?_
  refine (Stacks.SmallDerivedCategory.isIso_mapHomotopyCategoryCompQh_map_quotient_map_iff
    (pushforwardSheafOfModules f) _).2 ?_
  -- `f_*(j_* t)` is `g_* t` through the composition isomorphism, and `g_* t` is a
  -- quasi-isomorphism by [Stacks, Tag 0G9N] for the affine morphism `g = j ≫ f`.
  exact quasiIso_pushforward_pushforward_map j f t
    (quasiIso_modulePushforward_map_of_isAffineHom (j ≫ f) hqc t hJ ht)

end AnyModel

end AlgebraicGeometry

end
