module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymGenNatural
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TwistPullbackIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChangeSpec

/-!
# The twist of `𝐏(F)` pulls back to the twist of `𝐏(F')` along the closed immersion of a quotient

Let `u : F ⟶ F'` be an epimorphism of quasi-coherent modules on a scheme `X` and
`i : 𝐏(F') ⟶ 𝐏(F)` the closed immersion of projective bundles it induces
(`Stacks.RelativeProj.projectiveBundleMapOfEpi`). Then `i^*𝒪_{𝐏(F)}(1) ≅ 𝒪_{𝐏(F')}(1)`, by an
isomorphism carrying the pulled-back tautological quotient `i^*π^*F ⟶ i^*𝒪_{𝐏(F)}(1)` to the
tautological quotient of `F'` precomposed with `π'^*u`.

On the `SheafGradedAlgebra` substrate this is `Stacks.Chow.GenuineChern.twistPullbackIso` at
`γ = 𝟙 X`, whose chart hypothesis is the defining equation of the morphism on charts
(`Stacks.AlgebraicGeometry.ProjBundleSurjection.chart_comp_map`) together with the naturality of
the degree-one generator of the symmetric algebra. It is transported to the presentation
`Stacks.RelativeProj.projectiveBundle` by `Stacks.Modules.tautologicalBaseChange_general`, exactly
as the comparison of twists along a base change is in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChangeSpec`.

## Main definitions

* `Stacks.RelativeProj.tautologicalDatumTwistTransportIso`: the transport of a comparison of
  twists `h^*𝒪(1) ≅ 𝒪(1)` on the substrate to `b^*𝒪_{𝐏(E)}(1) ≅ 𝒪_{𝐏(E')}(1)`, for any `b`
  the presentation comparisons carry to `h`.
* `Stacks.RelativeProj.tautologicalDatumTwistMapOfEpiIso`: the isomorphism
  `i^*𝒪_{𝐏(F)}(1) ≅ 𝒪_{𝐏(F')}(1)`.

## Main results

* `Stacks.RelativeProj.tautologicalDatumTwistTransportIso_spec`: the transport is compatible with
  the tautological quotients when the comparison on the substrate is.
* `Stacks.RelativeProj.tautologicalDatumTwistMapOfEpiIso_spec`: the isomorphism carries `i^*` of
  the tautological quotient of `F` to the tautological quotient of `F'` precomposed with `π'^*u`.

## Implementation notes

The transport is stated and proved for a *variable* morphism `b` of projective bundles and a
variable morphism `h` of the substrate. Instantiated at the closed immersion, the same proof runs
out of the kernel's budget: reading the pinning hypothesis of
`Stacks.Modules.tautologicalBaseChange_general` off
`Stacks.Chow.GenuineChern.twistQuotientPullback` then unfolds the particular morphism of relative
homogeneous spectra.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent]
  (u : F ⟶ F') [Epi u]

/-- The morphism of relative homogeneous spectra induced by `Sym(u)`, on the `SheafGradedAlgebra`
substrate: the middle factor of `Stacks.RelativeProj.projectiveBundleMapOfEpi`. -/
def symGradedMapOfEpi : (symGradedBundle F').scheme ⟶ (symGradedBundle F).scheme :=
  Stacks.AlgebraicGeometry.ProjBundleSurjection.map (surjectiveOnAffineSections_symGradedHom u)

/-- `Stacks.RelativeProj.symGradedMapOfEpi u` is the morphism
`Stacks.AlgebraicGeometry.ProjBundleSurjection.map` of the surjection `Sym(u)`. -/
theorem symGradedMapOfEpi_eq :
    symGradedMapOfEpi u =
      Stacks.AlgebraicGeometry.ProjBundleSurjection.map
        (surjectiveOnAffineSections_symGradedHom u) :=
  rfl

/-- The morphism on the substrate lies over the base, in the form of a square over `𝟙 X`. -/
theorem symGradedMapOfEpi_comp_toBase :
    symGradedMapOfEpi u ≫ (symGradedBundle F).toBase = (symGradedBundle F').toBase ≫ 𝟙 X :=
  (symGradedMapOfEpi_eq u ▸ Stacks.AlgebraicGeometry.ProjBundleSurjection.map_comp_toBase _).trans
    (Category.comp_id _).symm

/-- The two presentations carry `Stacks.RelativeProj.projectiveBundleMapOfEpi` to the morphism of
the substrate. -/
@[reassoc]
theorem projectiveBundleMapOfEpi_comp_bundlePresentationIso_inv :
    projectiveBundleMapOfEpi u ≫ (bundlePresentationIso F).inv =
      (bundlePresentationIso F').inv ≫ symGradedMapOfEpi u := by
  rw [projectiveBundleMapOfEpi, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, symGradedMapOfEpi_eq]

/-- The composite of the identification `(𝟙 X)^*F ≅ F` with an epimorphism `u` is an
epimorphism. -/
instance epi_pullbackId_hom_app_comp : Epi ((Scheme.Modules.pullbackId X).hom.app F ≫ u) :=
  epi_comp _ _

/-- The chart description of the morphism on the substrate: on the chart over an affine open it
is `Proj` of `Sym(u)` on sections, which sends the degree-one element of a section `x` to that of
`u(x)`. -/
theorem symGradedMapOfEpi_chart (x' : X) :
    ∃ (U' : X.Opens) (hU' : IsAffineOpen U') (_ : x' ∈ U') (U : X.Opens) (hU : IsAffineOpen U)
      (hUU' : U' ≤ (𝟙 X) ⁻¹ᵁ U)
      (φ : (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading U
        →+*ᵍ
        (schemeSheafGradedAlgebra F' (isQuasicoherentPieces_of_isQuasicoherent F')).grading U')
      (hφ : HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra F'
          (isQuasicoherentPieces_of_isQuasicoherent F')).grading U') ≤
        (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).grading U)).map φ),
      (relativeProj (schemeSheafGradedAlgebra F'
          (isQuasicoherentPieces_of_isQuasicoherent F'))).chart U' hU' ≫ symGradedMapOfEpi u =
        AlgebraicGeometry.Proj.map φ hφ ≫
          (relativeProj (schemeSheafGradedAlgebra F
            (isQuasicoherentPieces_of_isQuasicoherent F))).chart U hU ∧
      ∀ x : Γ(F, U),
        φ (DirectSum.of ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).sectionPieces U) 1
            ((Scheme.Modules.symmetricAlgebraGen X F).val.app (op U) x)) =
          DirectSum.of ((schemeSheafGradedAlgebra F'
              (isQuasicoherentPieces_of_isQuasicoherent F')).sectionPieces U') 1
            ((Scheme.Modules.symmetricAlgebraGen X F').val.app (op U')
              (F'.val.map (homOfLE hUU').op
                (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv F F'
                  ((Scheme.Modules.pullbackId X).hom.app F ≫ u)).val.app (op U) x))) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := x') (U := ⊤) trivial
  refine ⟨U, hU, hxU, U, hU, le_rfl,
    (schemeSheafGradedAlgebraHom u (isQuasicoherentPieces_of_isQuasicoherent F)
      (isQuasicoherentPieces_of_isQuasicoherent F')).sectionHom U,
    Stacks.AlgebraicGeometry.ProjBundleSurjection.irrelevant_le_map_sectionHom
      (surjectiveOnAffineSections_symGradedHom u) hU, ?_, fun x => ?_⟩
  · rw [symGradedMapOfEpi_eq]
    refine (Stacks.AlgebraicGeometry.ProjBundleSurjection.chart_comp_map _ U hU).trans ?_
    rw [Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap_eq_map]
  · refine (Stacks.Chow.GenuineChern.sectionHom_of_symmetricAlgebraGen u
      (isQuasicoherentPieces_of_isQuasicoherent F)
      (isQuasicoherentPieces_of_isQuasicoherent F') U x).trans ?_
    refine congrArg (fun z => DirectSum.of
      ((schemeSheafGradedAlgebra F' (isQuasicoherentPieces_of_isQuasicoherent F')).sectionPieces
        U) 1 ((Scheme.Modules.symmetricAlgebraGen X F').val.app (op U) z)) ?_
    refine Eq.trans ?_ (congrArg (F'.val.map (homOfLE (le_rfl : U ≤ (𝟙 X) ⁻¹ᵁ U)).op)
      (Stacks.Chow.GenuineChern.homEquiv_pullbackId_comp_apply u U x)).symm
    show _ = F'.presheaf.map (𝟙 (op U)) _
    rw [CategoryTheory.Functor.map_id]
    rfl

/-- **The comparison of the tautological twists on the `SheafGradedAlgebra` substrate** along the
morphism induced by `Sym(u)`: `Stacks.Chow.GenuineChern.twistPullbackIso` at `γ = 𝟙 X`. -/
def symTwistMapOfEpiIso :
    (Scheme.Modules.pullback (symGradedMapOfEpi u)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
          (isQuasicoherentPieces_of_isQuasicoherent F)) ≅
      Stacks.ProjectiveBundleSplitting.tautologicalTwist F'
        (isQuasicoherentPieces_of_isQuasicoherent F') :=
  Stacks.Chow.GenuineChern.twistPullbackIso (𝟙 X) (isQuasicoherentPieces_of_isQuasicoherent F)
    (isQuasicoherentPieces_of_isQuasicoherent F') ((Scheme.Modules.pullbackId X).hom.app F ≫ u)
    _ (symGradedMapOfEpi_comp_toBase u) (symGradedMapOfEpi_chart u)

/-- The comparison on the substrate carries the pulled-back tautological quotient of `F` to the
tautological quotient of `F'` precomposed with `u`. -/
theorem symTwistMapOfEpiIso_spec :
    Stacks.Chow.GenuineChern.twistQuotientPullback (𝟙 X)
          (isQuasicoherentPieces_of_isQuasicoherent F)
          (isQuasicoherentPieces_of_isQuasicoherent F') _ (symGradedMapOfEpi_comp_toBase u) ≫
        (symTwistMapOfEpiIso u).hom =
      Stacks.Chow.GenuineChern.twistQuotientTarget (𝟙 X)
        (isQuasicoherentPieces_of_isQuasicoherent F')
        ((Scheme.Modules.pullbackId X).hom.app F ≫ u) :=
  Stacks.Chow.GenuineChern.twistQuotientPullback_comp_twistPullbackIso (𝟙 X) _ _ _ _ _ _

section Transport

variable {X X' : Scheme.{u}} (γ : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent] (E' : X'.Modules)
  [E'.IsQuasicoherent]

/-- **The transport of a comparison of tautological twists from the `SheafGradedAlgebra`
substrate to `Stacks.RelativeProj.projectiveBundle`**: for a morphism `b : 𝐏(E') ⟶ 𝐏(E)` which the
two presentation comparisons carry to a morphism `h` of the substrate, an isomorphism
`h^*𝒪(1) ≅ 𝒪(1)` there gives `b^*𝒪_{𝐏(E)}(1) ≅ 𝒪_{𝐏(E')}(1)`. -/
def tautologicalDatumTwistTransportIso
    (h : (symGradedBundle E').scheme ⟶ (symGradedBundle E).scheme)
    (b : projectiveBundle X' E' ⟶ projectiveBundle X E)
    (hbk : b ≫ (bundlePresentationIso E).inv = (bundlePresentationIso E').inv ≫ h)
    (sym : (Scheme.Modules.pullback h).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
          (isQuasicoherentPieces_of_isQuasicoherent E)) ≅
      Stacks.ProjectiveBundleSplitting.tautologicalTwist E'
        (isQuasicoherentPieces_of_isQuasicoherent E')) :
    (Scheme.Modules.pullback b).obj (tautologicalDatumTwist E) ≅ tautologicalDatumTwist E' :=
  (Scheme.Modules.pullbackComp b (bundlePresentationIso E).inv).app
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
        (isQuasicoherentPieces_of_isQuasicoherent E)) ≪≫
    (Scheme.Modules.pullbackCongr hbk).app
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
        (isQuasicoherentPieces_of_isQuasicoherent E)) ≪≫
    ((Scheme.Modules.pullbackComp (bundlePresentationIso E').inv h).app
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
        (isQuasicoherentPieces_of_isQuasicoherent E))).symm ≪≫
    (Scheme.Modules.pullback (bundlePresentationIso E').inv).mapIso sym

/-- The transported comparison, as the composite it is defined to be. -/
theorem tautologicalDatumTwistTransportIso_hom
    (h : (symGradedBundle E').scheme ⟶ (symGradedBundle E).scheme)
    (b : projectiveBundle X' E' ⟶ projectiveBundle X E)
    (hbk : b ≫ (bundlePresentationIso E).inv = (bundlePresentationIso E').inv ≫ h)
    (sym : (Scheme.Modules.pullback h).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
          (isQuasicoherentPieces_of_isQuasicoherent E)) ≅
      Stacks.ProjectiveBundleSplitting.tautologicalTwist E'
        (isQuasicoherentPieces_of_isQuasicoherent E')) :
    (tautologicalDatumTwistTransportIso E E' h b hbk sym).hom =
      (Scheme.Modules.pullbackComp b (bundlePresentationIso E).inv).hom.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
            (isQuasicoherentPieces_of_isQuasicoherent E)) ≫
        (Scheme.Modules.pullbackCongr hbk).hom.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
            (isQuasicoherentPieces_of_isQuasicoherent E)) ≫
        (Scheme.Modules.pullbackComp (bundlePresentationIso E').inv h).inv.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
            (isQuasicoherentPieces_of_isQuasicoherent E)) ≫
        (Scheme.Modules.pullback (bundlePresentationIso E').inv).map sym.hom :=
  rfl

/-- **The transported comparison is compatible with the tautological quotients**, when the one
on the substrate is: for `v : γ^*E ⟶ E'`, if `sym` carries the pulled-back tautological quotient
of `E` to the tautological quotient of `E'` precomposed with `v`, then the transported comparison
carries `b^*` of the tautological quotient of `𝐏(E)` to that of `𝐏(E')` precomposed with
`π'^*v`. -/
theorem tautologicalDatumTwistTransportIso_spec
    (v : (Scheme.Modules.pullback γ).obj E ⟶ E')
    (h : (symGradedBundle E').scheme ⟶ (symGradedBundle E).scheme)
    (hh : h ≫ (symGradedBundle E).toBase = (symGradedBundle E').toBase ≫ γ)
    (b : projectiveBundle X' E' ⟶ projectiveBundle X E)
    (hbk : b ≫ (bundlePresentationIso E).inv = (bundlePresentationIso E').inv ≫ h)
    (hb : b ≫ projectiveBundleToBase X E = projectiveBundleToBase X' E' ≫ γ)
    (sym : (Scheme.Modules.pullback h).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
          (isQuasicoherentPieces_of_isQuasicoherent E)) ≅
      Stacks.ProjectiveBundleSplitting.tautologicalTwist E'
        (isQuasicoherentPieces_of_isQuasicoherent E'))
    (hsym : Stacks.Chow.GenuineChern.twistQuotientPullback γ
        (isQuasicoherentPieces_of_isQuasicoherent E)
        (isQuasicoherentPieces_of_isQuasicoherent E') h hh ≫ sym.hom =
      Stacks.Chow.GenuineChern.twistQuotientTarget γ
        (isQuasicoherentPieces_of_isQuasicoherent E') v) :
    (Scheme.Modules.pullback b).map (tautologicalDatumUniv E) ≫
        (tautologicalDatumTwistTransportIso E E' h b hbk sym).hom =
      (Scheme.Modules.pullbackComp b (projectiveBundleToBase X E)).hom.app E ≫
        (Scheme.Modules.pullbackCongr hb).hom.app E ≫
        (Scheme.Modules.pullbackComp (projectiveBundleToBase X' E') γ).inv.app E ≫
        (Scheme.Modules.pullback (projectiveBundleToBase X' E')).map v ≫
        tautologicalDatumUniv E' := by
  have key :=
    Stacks.Modules.tautologicalBaseChange_general b (bundlePresentationIso E).inv
      (bundlePresentationIso E').inv h (symGradedBundle E).toBase (symGradedBundle E').toBase γ
      (projectiveBundleToBase X E) (projectiveBundleToBase X' E')
      (bundlePresentationIso_inv_comp_toBase E) (bundlePresentationIso_inv_comp_toBase E') hbk hh
      hb v
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E
        (isQuasicoherentPieces_of_isQuasicoherent E))
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E'
        (isQuasicoherentPieces_of_isQuasicoherent E'))
      sym hsym
  rw [tautologicalDatumUniv_eq E, tautologicalDatumTwistTransportIso_hom E E' h b hbk sym,
    tautologicalDatumUniv_eq E']
  exact key

end Transport

/-- **The comparison `i^*𝒪_{𝐏(F)}(1) ≅ 𝒪_{𝐏(F')}(1)` along the closed immersion of a quotient**,
on `Stacks.RelativeProj.projectiveBundle`: the comparison on the substrate carried along the two
presentation comparisons. -/
def tautologicalDatumTwistMapOfEpiIso :
    (Scheme.Modules.pullback (projectiveBundleMapOfEpi u)).obj (tautologicalDatumTwist F) ≅
      tautologicalDatumTwist F' :=
  tautologicalDatumTwistTransportIso F F' (symGradedMapOfEpi u) (projectiveBundleMapOfEpi u)
    (projectiveBundleMapOfEpi_comp_bundlePresentationIso_inv u) (symTwistMapOfEpiIso u)

/-- **The comparison of the twists along the closed immersion of a quotient is compatible with
the tautological quotients**: the pullback along `i = projectiveBundleMapOfEpi u` of the
tautological quotient of `F`, followed by the comparison, is the tautological quotient of `F'`
precomposed with `π'^*u`, read through the canonical identification of `i^*π^*F` with
`π'^*F`. -/
theorem tautologicalDatumTwistMapOfEpiIso_spec :
    (Scheme.Modules.pullback (projectiveBundleMapOfEpi u)).map (tautologicalDatumUniv F) ≫
        (tautologicalDatumTwistMapOfEpiIso u).hom =
      (Scheme.Modules.pullbackComp (projectiveBundleMapOfEpi u)
          (projectiveBundleToBase X F)).hom.app F ≫
        (Scheme.Modules.pullbackCongr
          ((projectiveBundleMapOfEpi_comp_toBase u).trans (Category.comp_id _).symm)).hom.app F ≫
        (Scheme.Modules.pullbackComp (projectiveBundleToBase X F') (𝟙 X)).inv.app F ≫
        (Scheme.Modules.pullback (projectiveBundleToBase X F')).map
          ((Scheme.Modules.pullbackId X).hom.app F ≫ u) ≫
        tautologicalDatumUniv F' :=
  tautologicalDatumTwistTransportIso_spec (𝟙 X) F F'
    ((Scheme.Modules.pullbackId X).hom.app F ≫ u) (symGradedMapOfEpi u)
    (symGradedMapOfEpi_comp_toBase u) (projectiveBundleMapOfEpi u)
    (projectiveBundleMapOfEpi_comp_bundlePresentationIso_inv u)
    ((projectiveBundleMapOfEpi_comp_toBase u).trans (Category.comp_id _).symm)
    (symTwistMapOfEpiIso u) (symTwistMapOfEpiIso_spec u)

end Stacks.RelativeProj

end
