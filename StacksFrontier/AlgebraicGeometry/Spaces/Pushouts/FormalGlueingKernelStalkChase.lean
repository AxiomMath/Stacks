module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalGlueingTwoTermStalkComplexGeneral

/-!
# The diagram chase omitted in the proof of Stacks 0AF0, and the hypotheses of Stacks 0AER

The source's proof of Stacks 0AF0 checks that the three comparison maps of the formal glueing
equivalence are isomorphisms by looking at geometric stalks, and the step it marks "(omitted)"
reads Stacks 0AER off the two-term stalk complexes as the statement that

```
Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*(G|_V))_x̄  ≅  Ker(j_*H_x̄ ⊕ G_ȳ ⟶ j'_*G_ȳ)
```

This file supplies the categorical content of that step and discharges the two hypotheses of
Stacks 0AER that Situation 0AEV supplies only implicitly.

## Main results

* `CategoryTheory.Limits.isPullback_of_isIso_kernelMap_of_mono_cokernelMap`: a commutative square
  in an abelian category whose induced map on kernels is an isomorphism and whose induced map on
  cokernels is a monomorphism is a pullback square.  This is the omitted chase: it is exactly the
  two conclusions of Stacks 0AER that turn the comparison of two-term complexes into a cartesian
  square, which then pastes onto
  `AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel_app`.
* `AlgebraicGeometry.Space.isPullback_directImageStalkMap`: **Stacks 0AER as a cartesian
  square**, for an arbitrary morphism of algebraic spaces.  This is the chase above applied to
  the two conclusions of Stacks 0AER, and it is the right-hand square of the omitted step.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isIntegralHom_fromPreimage` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.universallyInjective_fromPreimage`: in
  Situation 0AEV the projection `f^{-1}Z ⟶ Z` is integral and universally injective, which are
  the hypotheses `hint` and `hinj` of Stacks 0AER.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_directImageStalkMap_ambientMorphism`:
  the previous three combined — Stacks 0AER as a cartesian square for the morphism of the formal
  glueing situation, with both of its hypotheses discharged.

## Implementation notes

The chase is proved by comparing the source of the square with the pullback of the other two
maps, and showing that comparison to be both a monomorphism and an epimorphism.  Both halves are
elementary once the right factorisation is named, and neither uses the four lemma or
pseudoelements:

* *Monomorphy.*  A map killed by the comparison is killed by the left vertical, hence factors
  through its kernel, and the composite `Ker u ⟶ A ⟶ A'` is a monomorphism because it is the
  induced map on kernels — an isomorphism — followed by the kernel inclusion of the right
  vertical.
* *Epimorphy.*  The monomorphy of the induced map on cokernels makes the projection of the
  pullback to the target of the left vertical kill `Coker u`, so that projection factors as
  `r` through the image of `u`; the comparison composed with `r` is the canonical epimorphism
  onto that image, so `r` is an epimorphism and therefore a cokernel of its own kernel.  A map
  out of the pullback killed by the comparison also kills `Ker r`, because `Ker r` factors
  through the comparison — this is where the *surjectivity* of the induced map on kernels is
  used — so it descends along `r` and is killed by the canonical epimorphism.

The comparison maps are introduced as variables carrying their defining equations rather than as
`set` definitions: with `set` the defining equation blocks `pullback.lift_fst`, and the
elaboration of the later rewrites is markedly slower.

The two hypotheses of Stacks 0AER are discharged from `iso_over_Z`, the field of Situation 0AEV
saying that `f` is an isomorphism over `Z`: an isomorphism is finite, hence integral by the first
assertion of Stacks 0414, and is universally injective directly.  Nothing weaker is needed, and
in particular the representability hypothesis of the earlier
`AlgebraicGeometry.Space.isIso_kernelMap_and_mono_cokernelMap_pushforwardStalkMap` is avoided:
Situation 0AEV does not supply it, and the version consumed here is the one stated for an
arbitrary morphism, about `AlgebraicGeometry.Space.smallEtaleAbelianDirectImage`.

**What the omitted chase still owes.**  The pasting that finishes the step is
`CategoryTheory.IsPullback.paste_vert` of the cartesian square above onto
`AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel_app`, carried across a
geometric stalk.  The two squares do not yet live in one category: Stacks 0AER, and hence
`isPullback_directImageStalkMap`, is a statement about geometric stalks of *abelian sheaves*,
which are a filtered colimit over a neighbourhood category whose objects sit one universe above
the sections and are therefore pinned at `AddCommGrpCat.{u + 1}`, whereas the square of
Stacks 0AEX lives in the geometric *module* stalks at `u`.  Bridging them needs the Stacks 03D1
compatibility `modulePushforward ⋙ toSheaf ≅ toSheaf ⋙ f_*` for the morphism `f` of
Situation 0AEV, and `AlgebraicGeometry.Space.modulePushforwardCompToSheafIso` does not apply
there: it hypothesises `yoneda.relativelyRepresentable f.hom`, which Situation 0AEV does not
supply, and its right-hand side is
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward` rather than the unconditional
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImage`.  The two direct images are the same
three-factor conjugate of the spaces-étale direct image by the comparison equivalences of
Stacks 03G1 — `AlgebraicGeometry.Space.smallEtaleDirectImage` in `Type u` and
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImage` in `AddCommGrpCat.{u + 1}`, neither with
a hypothesis on the morphism — so the bridge is available in principle; but the sites-level
lemma `Stacks.Sheaves.ToposPullback.pullbackModuleCompToSheafIso` cannot produce it, because its
comparison datum `ε` forces the functor of sheaves of sets to be restriction along a continuous
functor, which a conjugate is not.  The bridge is
`AlgebraicGeometry.Space.modulePushforwardCompToSheafAbelianDirectImageIso`, which compares the
two conjugates factor by factor instead and so needs nothing of `f`, with the coefficients
already lifted to `u + 1`; it is the pushforward companion of
`AlgebraicGeometry.Space.modulePullbackCompToSheafInverseImageIso`.

**What the omitted chase owes after that.**  The two squares now do live in one category:
`AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel_moduleAbelianStalk`
reads the square of Stacks 0AEX as a cartesian square of abelian groups at `u + 1`, which is
where `isPullback_directImageStalkMap` lives.  The pasting is still not the only thing left,
because `CategoryTheory.IsPullback.paste_vert` wants the *same* arrow as the bottom row of the
first square and the top row of the second, not two isomorphic ones: the bottom row is
`AlgebraicGeometry.Space.FormalGlueingSituation.ambientOverlapMap` read at the stalk, which is
`f_*` of the unit of `AlgebraicGeometry.Space.modulePullbackAdjunction` along `j'` followed by
`AlgebraicGeometry.Space.modulePushforwardCompIso`, and the top row is
`(f_* ⋙ (-)_x̄)` of `AlgebraicGeometry.Space.smallEtaleAbelianRestrictionUnit`, the unit of
`AlgebraicGeometry.Space.smallEtaleAbelianInverseImageAdjunction` along `j'`.  Identifying those
two needs three things that the dictionary above does not supply:

* *The two `j'`.*  Situation 0AEV takes `V` to be `AlgebraicGeometry.Space.openComplement` of
  `f^{-1}Z` — the subfunctor of sections whose restrictions into `f^{-1}Z` are over empty
  schemes — while Stacks 0AER takes it to be
  `AlgebraicGeometry.Space.openComplementOfClosedSubspace`, the open subspace that part (1) of
  Stacks 03BZ attaches to the complement of the point set.  These are different constructions,
  equal but not definitionally so; the identification is
  `AlgebraicGeometry.Space.FormalGlueingSituation.V_eq_openComplementPreimage` and
  `...spaceV_eq_openComplementPreimageSpace`.  Still owed at this point is the matching of the
  two inclusions, `openImmersionOver` against `openComplementPreimageι`, across that equality.
* *The mate condition.*  Owning both halves of the dictionary is not the same as knowing they
  are conjugate: what the identification needs is that
  `modulePullbackCompToSheafInverseImageIso` and
  `modulePushforwardCompToSheafAbelianDirectImageIso` carry the unit of the module adjunction
  along `j'` to the unit of the abelian one.  Neither iso is built from the other — the first
  is `CategoryTheory.Adjunction.leftAdjointUniq`, the second a factorwise comparison of
  conjugates — so this is a statement to prove, not a rewrite.  It should be stated for an
  arbitrary étale representable morphism with the transporting functor left free, and only
  instantiated at `j'`, for the reason recorded in
  `StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleConjugateToSheaf.lean`.
* *The two composition isomorphisms.*  `(f ∘ j')_*` is split module-side by
  `AlgebraicGeometry.Space.modulePushforwardCompIso` and abelian-side by
  `AlgebraicGeometry.Space.smallEtaleAbelianDirectImageCompIso`, and the dictionary has to be
  shown to commute with the two.

Only then is the pasting itself a line, and the source's two cases — `ȳ ∈ V`, where
`j'_*𝒢_ȳ = 𝒢_ȳ` makes the kernel `ℋ_x̄`, and `ȳ ∈ f^{-1}Z`, where the stalk of the ideal is
finitely generated and `𝒪_{X,x̄} ⟶ 𝒪_{Y,ȳ}` is flat local with
`𝒪_{X,x̄}/I_x̄ ≅ 𝒪_{Y,ȳ}/I_ȳ` — sit downstream of it.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 0AER](https://stacks.math.columbia.edu/tag/0AER)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
* [Stacks Project, Tag 0414](https://stacks.math.columbia.edu/tag/0414)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe v₁ u₁

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]

/-- A commutative square in an abelian category whose induced map on kernels is an isomorphism
and whose induced map on cokernels is a monomorphism is a pullback square.

`CochainComplex.FilteredInjective.TermwiseSplit.isPullback_of_mono_cokernel_map` is the special
case where both vertical maps are monomorphisms: the two kernels then vanish and the induced map
between them is an isomorphism for free, so only the cokernel hypothesis is left to state.  That
case has the shorter proof — a monomorphic vertical map *is* the kernel of its own cokernel
projection, so the lift of a pullback cone is immediate — and it is kept; this statement is the
one Stacks 0AER needs, where neither vertical map is a monomorphism. -/
theorem isPullback_of_isIso_kernelMap_of_mono_cokernelMap {A A' C C' : 𝒜} {u : A ⟶ C}
    {u' : A' ⟶ C'} {φ : A ⟶ A'} {ψ : C ⟶ C'} (w : u ≫ ψ = φ ≫ u')
    (hker : IsIso (kernel.map u u' φ ψ w)) (hcok : Mono (cokernel.map u u' φ ψ w)) :
    IsPullback φ u u' ψ := by
  have := hker
  have := hcok
  -- The two identities of the induced maps on the kernel and on the cokernel.
  have hmapι : kernel.ι u ≫ φ = kernel.map u u' φ ψ w ≫ kernel.ι u' := by simp
  have hmapπ : cokernel.π u ≫ cokernel.map u u' φ ψ w = ψ ≫ cokernel.π u' := by simp
  have hkermono : Mono (kernel.ι u ≫ φ) := by rw [hmapι]; infer_instance
  -- The comparison into the pullback, as a variable carrying its two defining equations.
  obtain ⟨θ, hθfst, hθsnd⟩ : ∃ θ : A ⟶ Limits.pullback u' ψ,
      θ ≫ pullback.fst u' ψ = φ ∧ θ ≫ pullback.snd u' ψ = u :=
    ⟨pullback.lift φ u w.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- The comparison is a monomorphism: a map it kills is killed by `u`, hence factors through
  -- `Ker u`, and `Ker u ⟶ A'` is a monomorphism because the induced map on kernels is one.
  have hmono : Mono θ := by
    refine Preadditive.mono_of_cancel_zero θ fun {Z} g hg => ?_
    have hkill : ∀ {W : 𝒜} (p : Limits.pullback u' ψ ⟶ W) {x : A ⟶ W}, θ ≫ p = x → g ≫ x = 0 :=
      by intro _ p _ e; rw [← e, ← Category.assoc, hg, zero_comp]
    have h1 := hkill _ hθsnd
    have h3 : kernel.lift u g h1 ≫ (kernel.ι u ≫ φ) = 0 := by
      rw [← Category.assoc, kernel.lift_ι, hkill _ hθfst]
    rw [← kernel.lift_ι u g h1, zero_of_comp_mono _ h3, zero_comp]
  -- The projection to `C` kills `Coker u`, because the induced map on cokernels is a
  -- monomorphism and the square of the pullback cone kills it after that map.
  have hzero : pullback.snd u' ψ ≫ cokernel.π u = 0 := by
    refine (cancel_mono (cokernel.map u u' φ ψ w)).mp ?_
    rw [zero_comp, Category.assoc, hmapπ, ← Category.assoc, ← pullback.condition,
      Category.assoc, cokernel.condition, comp_zero]
  -- So the projection factors through the image of `u`.
  obtain ⟨r, hrι⟩ : ∃ r : Limits.pullback u' ψ ⟶ Abelian.image u,
      r ≫ Abelian.image.ι u = pullback.snd u' ψ :=
    ⟨kernel.lift (cokernel.π u) (pullback.snd u' ψ) hzero, kernel.lift_ι _ _ _⟩
  -- Composed with the comparison it is the canonical epimorphism onto the image, so it is
  -- itself an epimorphism.
  have hθr : θ ≫ r = Abelian.factorThruImage u := by
    rw [← cancel_mono (Abelian.image.ι u), Category.assoc, hrι, hθsnd, Abelian.image.fac]
  have hepir : Epi r := by
    have hc : Epi (θ ≫ r) := by rw [hθr]; infer_instance
    exact epi_of_epi θ r
  -- The comparison is an epimorphism.  A map `g` out of the pullback that it kills also kills
  -- `Ker r`, because `Ker r ⟶ pullback` factors through the comparison; and `r`, being an
  -- epimorphism, is a cokernel of `Ker r`, so `g` descends along `r` to the image of `u`,
  -- where the canonical epimorphism kills it.
  have hepi : Epi θ := by
    refine Preadditive.epi_of_cancel_zero θ fun {Z} g hg => ?_
    have hk1 : kernel.ι r ≫ pullback.snd u' ψ = 0 := by
      rw [← hrι, ← Category.assoc, kernel.condition, zero_comp]
    have hk2 : (kernel.ι r ≫ pullback.fst u' ψ) ≫ u' = 0 := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hk1, zero_comp]
    obtain ⟨lam, hlamι⟩ : ∃ lam : kernel r ⟶ kernel u',
        lam ≫ kernel.ι u' = kernel.ι r ≫ pullback.fst u' ψ :=
      ⟨kernel.lift u' (kernel.ι r ≫ pullback.fst u' ψ) hk2, kernel.lift_ι _ _ _⟩
    obtain ⟨kinv, hkinv⟩ : ∃ kinv : kernel u' ⟶ kernel u,
        kinv ≫ kernel.map u u' φ ψ w = 𝟙 (kernel u') :=
      ⟨inv (kernel.map u u' φ ψ w), IsIso.inv_hom_id _⟩
    have hkapθ : (lam ≫ kinv ≫ kernel.ι u) ≫ θ = kernel.ι r := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hθfst, Category.assoc, Category.assoc, hmapι,
          ← Category.assoc kinv, hkinv, Category.id_comp, hlamι]
      · rw [Category.assoc, hθsnd, Category.assoc, Category.assoc, kernel.condition,
          comp_zero, comp_zero, hk1]
    have hkg : kernel.ι r ≫ g = 0 := by
      rw [← hkapθ, Category.assoc, hg, comp_zero]
    have hck : IsColimit (CokernelCofork.ofπ r (kernel.condition r)) :=
      Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)
    obtain ⟨g', hg'⟩ := CokernelCofork.IsColimit.desc' hck g hkg
    have hrg : r ≫ g' = g := by simpa using hg'
    have hzero' : Abelian.factorThruImage u ≫ g' = 0 := by
      rw [← hθr, Category.assoc, hrg, hg]
    rw [← hrg, zero_of_epi_comp _ hzero', comp_zero]
  have hiso : IsIso θ := isIso_of_mono_of_epi θ
  exact IsPullback.of_iso_pullback ⟨w.symm⟩ (asIso θ) hθfst hθsnd

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

section CartesianForm

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0AER as a cartesian square.**  Let `f : Y ⟶ X` be a morphism of algebraic spaces
over `S` and `Z ⊆ X` a closed subspace whose projection `f^{-1}Z ⟶ Z` is integral and
universally injective, let `ȳ` be a geometric point of `Y` with image `x̄`, and let `G` be an
abelian sheaf on the small étale site of `Y`.  Writing `j' : V ⟶ Y` for the inclusion of
`V = Y ∖ f^{-1}Z`, the square
```
(f_*G)_x̄           ⟶  G_ȳ
    ↓                    ↓
(f_*(j'_*(G|_V)))_x̄  ⟶  (j'_*(G|_V))_ȳ
```
of the canonical comparison of
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImageStalkMap` and the unit `G ⟶ j'_*(G|_V)` is
cartesian.

This is the form in which the source's proof of Stacks 0AF0 uses Stacks 0AER: the step the
source marks "(omitted)" pastes this square onto the pullback square of Stacks 0AEX, and a
pasting of cartesian squares is cartesian.  That the two conclusions of Stacks 0AER — an
isomorphism on kernels and an injection on cokernels — say exactly that the square is cartesian
is `CategoryTheory.Limits.isPullback_of_isIso_kernelMap_of_mono_cokernelMap`. -/
theorem isPullback_directImageStalkMap (f : Y ⟶ X) (Z : ClosedSubspaces B S hS X.1)
    (hint : IsIntegralHom B S hS (Z.1.fromPreimage f.hom))
    (hinj : UniversallyInjective B S hS (Z.1.fromPreimage f.hom))
    (y : GeometricPoint B S hS Y.1) (G : abelianSheaves.{u + 1} B S hS Y) :
    IsPullback
      ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app G)
      ((smallEtaleAbelianDirectImage B S hS f ⋙
          smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map
        (smallEtaleAbelianRestrictionUnit B S hS f Z G))
      ((smallEtaleAbelianStalk B S hS y).map
        (smallEtaleAbelianRestrictionUnit B S hS f Z G))
      ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app
        (smallEtaleAbelianRestrictionPushforward B S hS f Z G)) :=
  have h := isIso_kernelMap_and_mono_cokernelMap_directImageStalkMap B S hS f Z hint hinj y G
  isPullback_of_isIso_kernelMap_of_mono_cokernelMap _ h.1 h.2

end CartesianForm

namespace FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS)

/-- **In Situation 0AEV the projection `f^{-1}Z ⟶ Z` is integral.**  It is an isomorphism by
hypothesis, hence finite, hence integral by the first assertion of Stacks 0414.

This discharges the hypothesis `hint` of Stacks 0AER in the formal glueing situation, rather than
carrying it as an extra assumption. -/
theorem isIntegralHom_fromPreimage : IsIntegralHom B S hS (D.Z.fromPreimage D.f) :=
  have := D.iso_over_Z
  (isFinite_of_isIso B S hS (D.Z.fromPreimage D.f)).isIntegralHom

/-- **In Situation 0AEV the projection `f^{-1}Z ⟶ Z` is universally injective.**  It is an
isomorphism by hypothesis, and an isomorphism is universally injective.

This discharges the hypothesis `hinj` of Stacks 0AER in the formal glueing situation, rather than
carrying it as an extra assumption. -/
theorem universallyInjective_fromPreimage :
    UniversallyInjective B S hS (D.Z.fromPreimage D.f) :=
  have := D.iso_over_Z
  universallyInjective_of_isIso B S hS (D.Z.fromPreimage D.f)

/-- **Stacks 0AER as a cartesian square, in Situation 0AEV.**
`AlgebraicGeometry.Space.isPullback_directImageStalkMap` for the morphism `f` of the formal
glueing situation and the closed subspace `Z` of it, with the two hypotheses of Stacks 0AER
discharged from `iso_over_Z`.

This is the right-hand square of the diagram chase the source of Stacks 0AF0 omits.  What is
still owed to complete that chase is the transport of this square from the geometric stalks of
*abelian sheaves*, where Stacks 0AER lives and which are pinned at universe `u + 1`, to the
geometric *module* stalks at `u`, where the functors of Stacks 0AEW and Stacks 0AEX live; see the
implementation notes. -/
theorem isPullback_directImageStalkMap_ambientMorphism
    (y : GeometricPoint B S hS D.spaceY.1)
    (G : abelianSheaves.{u + 1} B S hS D.spaceY) :
    IsPullback
      ((smallEtaleAbelianDirectImageStalkMap B S hS D.ambientMorphism y).app G)
      ((smallEtaleAbelianDirectImage B S hS D.ambientMorphism ⋙
          smallEtaleAbelianStalk B S hS (geometricPointMap D.ambientMorphism.hom y)).map
        (smallEtaleAbelianRestrictionUnit B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩ G))
      ((smallEtaleAbelianStalk B S hS y).map
        (smallEtaleAbelianRestrictionUnit B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩ G))
      ((smallEtaleAbelianDirectImageStalkMap B S hS D.ambientMorphism y).app
        (smallEtaleAbelianRestrictionPushforward B S hS D.ambientMorphism
          ⟨D.Z, D.closed_Z⟩ G)) :=
  isPullback_directImageStalkMap B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩
    D.isIntegralHom_fromPreimage D.universallyInjective_fromPreimage y G

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
