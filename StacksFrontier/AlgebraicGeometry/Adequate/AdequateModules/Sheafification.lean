module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Sheafification of a presheaf of modules adequate on all affines

[Stacks, Tag 06VP] says that a presheaf of `O`-modules on a big `τ`-site over `S` whose
affine-section functor `F_{F, A}` is adequate for *every* affine scheme `Spec A` over `S` has an
adequate sheafification. The conclusion is about the sheafification, not about the presheaf
itself, which is not even required to be a sheaf.

## Main definitions

* `Stacks.Adequate.presheafAffineSectionFunctor` — the affine-section functor `F_{F, A}` of a
  *presheaf* of modules, the same pushforward along the affine-spectrum functor and its scalar
  identification that `Stacks.Adequate.affineSectionFunctor` applies to a sheaf.
* `Stacks.Adequate.AffineAdequateSheafTopology` — the one input of the source's proof, named as
  an explicit hypothesis: over each affine scheme of the site there is a topology on its site
  algebras for which the affine-spectrum functor is continuous and cocontinuous and every
  module extension `B ↦ B ⊗_A M` is a sheaf. At the value universe `u` of the site it is a
  theorem, `Stacks.Adequate.affineAdequateSheafTopology` of
  `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineSheafTopology.lean`; at a
  general value universe `max u m` it is still open, so the results below that range over
  `max u m` keep it as a hypothesis rather than narrowing to `m = u`.

## Main results

* `AdequateFunctor.isSheaf_of_isAdequate` — an adequate module-valued functor is a sheaf for any
  topology on its domain for which the module extensions are sheaves, because adequacy exhibits
  it as a kernel of a map of module extensions and a kernel of sheaves is a sheaf.
* `Stacks.Adequate.isIso_of_isLocallyBijective` — a locally bijective map between presheaves of
  modules that are both sheaves is an isomorphism.
* `Stacks.Adequate.affineSectionsMap_isIso` — a locally bijective map from a presheaf of modules
  to a sheaf of modules becomes an isomorphism on affine sections, as soon as the presheaf's
  affine-section functor is adequate.
* `Stacks.Adequate.isAdequate_sheafification` — [Stacks, Tag 06VP].

## Implementation notes

The sheafification is not constructed: it enters as a map `η : F ⟶ G.val` from the presheaf to a
sheaf of modules which is locally injective and locally surjective. That is exactly the
universal property of the associated sheaf, so no choice of construction of the sheafification
is made, and the statement applies to any model of it. The conclusion
`Stacks.Adequate.IsAdequate B G` is adequacy of that sheaf `G`, never of `F`.

The source's proof computes `F^+` on an affine `U = Spec A` as the colimit of Cech `H^0` over
standard affine `τ`-coverings of `U`, identifies that Cech `H^0` with a kernel of base changes by
flatness [Stacks, Tag 06UW] and then with `F(A)` itself by faithfully flat descent
[Stacks, Tag 023M], concluding that `F` and `F^#` have the same affine sections. Both of those tags
are formalized, as `AdequateFunctor.moduleValuedFunctorBaseChangeMap_bijective` and the module
equivalence of `StacksFrontier.AlgebraicGeometry.Descent.ModuleEquivalence.FaithfullyFlatAmitsur`;
what they do not by themselves give is the identification of the topology induced on the algebras
of the site, which is what turns those two tags into the sheaf condition for the module extensions
`B ↦ B ⊗_A M`. That sheaf condition, together with the continuity and cocontinuity of the
affine-spectrum functor needed to compare local bijectivity on the two sites, is
`Stacks.Adequate.AffineAdequateSheafTopology`. Given it, the argument here replaces the source's
colimit computation: the affine-section functors of `F` and of `G` are both sheaves for that
topology, and a locally bijective map of sheaves is an isomorphism, so the two affine-section
functors are isomorphic and the adequacy hypothesis transports from `F` to `G`.

`Stacks.Adequate.affineAdequateSheafTopology` proves `Stacks.Adequate.AffineAdequateSheafTopology`
for every chosen big site, with no hypothesis, at the value universe `u` of the site, by
identifying the topology as the one the localization of the ambient big site at the affine induces
on its algebras. That proof runs through `AlgebraicGeometry.tilde`, which takes a
`ModuleCat.{u} A`, so it is available at `AffineAdequateSheafTopology.{u, u}` and not at `.{u, m}`
for a general `m`. The declarations of this file and of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Abelian.lean` are stated over sheaves of
modules of value universe `max u m`, so they keep the hypothesis: dropping it would force `m = u`
and narrow them. Each clause string says so.

The passage from adequacy at every affine of the site to adequacy of `G` as a sheaf of modules
is `Stacks.Adequate.isAdequate_of_forall_affineSectionFunctor`, which is proved outright.

## References

* [Stacks Project, Tag 06VP](https://stacks.math.columbia.edu/tag/06VP)
* [Stacks Project, Tag 06UW](https://stacks.math.columbia.edu/tag/06UW)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 06VG](https://stacks.math.columbia.edu/tag/06VG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w w' u m u₁ v₁

namespace AdequateFunctor

/-- An adequate module-valued functor on a domain of algebras is a sheaf for any topology on
that domain for which the module extensions `B ↦ B ⊗[A] M` are sheaves: adequacy presents it as
the kernel of a map between two such module extensions, and a kernel of sheaves of modules is a
sheaf. -/
public theorem isSheaf_of_isAdequate {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] (ι : C ⥤ CommAlgCat.{u} A)
    (J : GrothendieckTopology Cᵒᵖ) (F : ModuleValuedFunctorOn.{max u w} ι)
    (hF : IsAdequate ι F)
    (hM : ∀ M : ModuleCat.{max u w} A,
      Presheaf.IsSheaf J ((moduleExtensionFunctorOn ι).obj M).presheaf) :
    Presheaf.IsSheaf J F.presheaf := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hF
  let e' := (presheafOfModulesUliftIso _ F).symm ≪≫ e
  apply (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf _).mapIso e')).mpr
  apply PresheafOfModules.isSheaf_of_isLimit
    (kernelIsKernel ((moduleExtensionFunctorOn ι).map f))
  intro j
  cases j
  · exact hM M
  · exact hM N

end AdequateFunctor

namespace Stacks.Adequate

/-- The affine-section functor `F_{F, A}` of a *presheaf* of modules on a big site: the
pushforward of `F` along the affine-spectrum functor of `A` and the scalar identification
`Stacks.Adequate.affineRingMap`. For a sheaf of modules this is
`Stacks.Adequate.affineSectionFunctor` applied to its underlying presheaf. -/
public noncomputable abbrev presheafAffineSectionFunctor
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : PresheafOfModules.{max u m} B.structureSheaf.obj)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S) :
    AdequateFunctor.ModuleValuedFunctorOn
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) :=
  (PresheafOfModules.pushforward (affineRingMap B A f)).obj F

/-- A locally injective and locally surjective map between presheaves of modules whose
underlying presheaves are both sheaves is an isomorphism: it is an isomorphism of sheaves of
abelian groups, and the forgetful functor to presheaves of abelian groups reflects
isomorphisms. -/
public theorem isIso_of_isLocallyBijective {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ RingCat.{w'}}
    {F G : PresheafOfModules.{w} R} (hF : Presheaf.IsSheaf J F.presheaf)
    (hG : Presheaf.IsSheaf J G.presheaf) (η : F ⟶ G)
    (hinj : PresheafOfModules.IsLocallyInjective J η)
    (hsurj : PresheafOfModules.IsLocallySurjective J η) : IsIso η := by
  let SF : Sheaf J AddCommGrpCat.{w} := ⟨F.presheaf, hF⟩
  let SG : Sheaf J AddCommGrpCat.{w} := ⟨G.presheaf, hG⟩
  let θ : SF ⟶ SG := ⟨(PresheafOfModules.toPresheaf R).map η⟩
  have hθ : IsIso θ := (Sheaf.isLocallyBijective_iff_isIso θ).mp ⟨hinj, hsurj⟩
  have : IsIso ((PresheafOfModules.toPresheaf R).map η) :=
    (sheafToPresheaf J AddCommGrpCat.{w}).map_isIso θ
  exact isIso_of_reflects_iso η (PresheafOfModules.toPresheaf R)

/-- Over each affine scheme of the site there is a topology on its algebras in the site for
which the affine-spectrum functor is continuous and cocontinuous and every module extension
`B ↦ B ⊗[A] M` is a sheaf. This is the input of the source's proof of [Stacks, Tag 06VP]: it
is what the flat base change of [Stacks, Tag 06UW] and the faithfully flat descent of
[Stacks, Tag 023M] amount to once the topology induced on the algebras of the site has been
identified. At the value universe `u` of the site it is a theorem with no hypothesis,
`Stacks.Adequate.affineAdequateSheafTopology`; at a general value universe `max u m` it is
open. -/
public abbrev AffineAdequateSheafTopology
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S) : Prop :=
  ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S), schemeSizeBelow B.cutoff (Spec A) →
    ∃ J : GrothendieckTopology
      (AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ,
      (affineSpecOver B A f).IsCocontinuous J B.topology ∧
      (affineSpecOver B A f).IsContinuous J B.topology ∧
      ∀ M : ModuleCat.{max u m} A,
        Presheaf.IsSheaf J ((AdequateFunctor.moduleExtensionFunctorOn
          (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).obj M).presheaf

/-- A locally bijective map from a presheaf of modules to a sheaf of modules on a big site
induces an isomorphism on the affine sections over any affine scheme of the site over `S`, as
soon as the affine-section functor of the presheaf is adequate there: both affine-section
functors are then sheaves for the given topology on the site algebras, the presheaf's because it
is adequate and the sheaf's by continuity of the affine-spectrum functor, and local bijectivity
transfers along the cocontinuous affine-spectrum functor. -/
public theorem affineSectionsMap_isIso
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : PresheafOfModules.{max u m} B.structureSheaf.obj)
    (G : SheafOfModules.{max u m} B.structureSheaf) (η : F ⟶ G.val)
    (hinj : PresheafOfModules.IsLocallyInjective B.topology η)
    (hsurj : PresheafOfModules.IsLocallySurjective B.topology η)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (J : GrothendieckTopology
      (AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ)
    (hco : (affineSpecOver B A f).IsCocontinuous J B.topology)
    (hcont : (affineSpecOver B A f).IsContinuous J B.topology)
    (hM : ∀ M : ModuleCat.{max u m} A,
      Presheaf.IsSheaf J ((AdequateFunctor.moduleExtensionFunctorOn
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).obj M).presheaf)
    (hF : AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
      (presheafAffineSectionFunctor B F A f)) :
    IsIso ((PresheafOfModules.pushforward (affineRingMap B A f)).map η) := by
  have := hco
  have := hcont
  have hFs : Presheaf.IsSheaf J (presheafAffineSectionFunctor B F A f).presheaf :=
    AdequateFunctor.isSheaf_of_isAdequate _ J _ hF hM
  have hGs : Presheaf.IsSheaf J (affineSectionFunctor B G A f).presheaf := by
    change Presheaf.IsSheaf J ((affineSpecOver B A f).op ⋙ G.val.presheaf)
    exact (affineSpecOver B A f).op_comp_isSheaf_of_isSheaf J B.topology G.val.presheaf G.isSheaf
  refine isIso_of_isLocallyBijective hFs hGs _ ?_ ?_
  · exact Presheaf.isLocallyInjective_whisker J B.topology (affineSpecOver B A f)
      ((PresheafOfModules.toPresheaf B.structureSheaf.obj).map η)
  · exact Presheaf.isLocallySurjective_whisker J B.topology (affineSpecOver B A f)
      ((PresheafOfModules.toPresheaf B.structureSheaf.obj).map η)

/-- [Stacks, Tag 06VP]: let `F` be a presheaf of `O`-modules on the big `τ`-site over `S`. If
for *every* affine scheme `Spec A` over `S` belonging to the site the functor `F_{F, A}` is
adequate, then the sheafification of `F` is an adequate `O`-module.

The sheafification enters as a locally injective and locally surjective map `η : F ⟶ G.val` to a
sheaf of modules `G`, and the conclusion is adequacy of `G`. The hypothesis `htop` is the input
of the source's proof; it is a theorem at `m = u`,
`Stacks.Adequate.affineAdequateSheafTopology`, and open for a general `m`, and it is kept as a
hypothesis here because the statement ranges over sheaves of modules of value universe
`max u m`; see the module documentation. -/
@[stacks 06VP "assuming `AffineAdequateSheafTopology.{u, m}`, which is a theorem for `m = u`
(`Stacks.Adequate.affineAdequateSheafTopology`) and open for a general `m`"]
public theorem isAdequate_sheafification
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (htop : AffineAdequateSheafTopology.{u, m} B)
    (F : PresheafOfModules.{max u m} B.structureSheaf.obj)
    (G : SheafOfModules.{max u m} B.structureSheaf) (η : F ⟶ G.val)
    (hinj : PresheafOfModules.IsLocallyInjective B.topology η)
    (hsurj : PresheafOfModules.IsLocallySurjective B.topology η)
    (hF : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S),
      schemeSizeBelow B.cutoff (Spec A) →
        AdequateFunctor.IsAdequate
          (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
          (presheafAffineSectionFunctor B F A f)) :
    IsAdequate B G := by
  refine isAdequate_of_forall_affineSectionFunctor B G fun A f hA => ?_
  obtain ⟨J, hco, hcont, hM⟩ := htop A f hA
  have := affineSectionsMap_isIso B F G η hinj hsurj A f J hco hcont hM (hF A f hA)
  exact (hF A f hA).of_iso
    (asIso ((PresheafOfModules.pushforward (affineRingMap B A f)).map η)).symm

end Stacks.Adequate

end
