module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjFunctorQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleFunctorLaws
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjUniversalCompatible

/-!
# The comparison `F(Y) ⟶ Mor(Y, Proj(A))` is surjective

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)` and `Y` a scheme. Section 27.12 forms the
functor `F` by taking, at a quasi-compact `Y`, the union `F(Y) = ⋃_{d ≥ 1} F_d(Y)` of the sets of
strict equivalence classes of triples of weight `d` along the weight transitions, and [Stacks,
Tag 01NC] asserts that `F` is representable by `X`, the comparison being
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.classifyingMorphism`, the map of [Stacks,
Tag 01N8] on classes.

`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorInjective.lean` proves that comparison
injective. **This file proves it surjective**, for a quasi-compact `Y`: every morphism
`Y ⟶ X` is classified by a triple over `Y`, namely by the pullback along `φ : Y ⟶ U_d` of the
universal family `(d, 𝒪_{U_d}(d), ψ^d)` of [Stacks, Tag 01N9], where `φ` is the factorization of
the morphism through a single `U_d` supplied by
`AlgebraicGeometry.Proj.exists_pos_existsUnique_factorization`.

Two inputs make that work, and they are the two halves of this file:

* the universal family is compatible with the identity of `U_d`, so the morphism it classifies is
  `𝟙_{U_d}` — that is
  `StacksFrontier/AlgebraicGeometry/Constructions/ProjUniversalCompatible.lean`, read off here as
  `Stacks.AlgebraicGeometry.ProjClassifyingPullback.classifyingHom_universalVeroneseSections`;
* the classification of [Stacks, Tag 01N8] is **natural in `Y`**: the morphism classified by the
  pullback of a triple along `h : Y' ⟶ Y` is `h` followed by the morphism classified by the
  triple.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjClassifyingPullback.pullbackTwistComp`: the comparison
  `(h ≫ φ)⁎𝒪_X(c) ≅ h^*(φ⁎𝒪_X(c))`, the isomorphism `α` of the pulled-back pair is built from.
* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.universalDegreeTriple`: the universal family
  of [Stacks, Tag 01N9] as a weight-`d` triple over `U_d`.

## Main results

* `Stacks.AlgebraicGeometry.ProjClassifyingPullback.isCompatible_pullbackSections`:
  **compatibility is stable under pullback.** If the pair `(φ, α)` is compatible with `ψ` then
  `(h ≫ φ, h^*α)` is compatible with `h^* ∘ ψ`.
* `Stacks.AlgebraicGeometry.ProjClassifyingPullback.classifyingHom_pullbackSections` and
  `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.classifyingMorphism_pullback`: **the
  classification of [Stacks, Tag 01N8] is natural in `Y`**, on graded maps and on classes.
* `Fd.classifyingMorphism_pullback_universalDegreeTriple`, in the same namespace:
  **surjectivity at a fixed weight**: a morphism `φ : Y ⟶ U_d` is classified by the pullback
  along `φ` of the universal family.
* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.exists_pos_classifyingMorphism_eq`:
  **[Stacks, Tag 01NC], the surjectivity of the comparison** for a quasi-compact `Y`.

## Implementation notes

**How the pulled-back pair is built.** [Stacks, Tag 01N8] attaches to a triple a pair
`(φ, α)` with `α : φ⁎𝒪_X(d) ≅ L`. For the pulled-back triple the morphism is `h ≫ φ` and the
isomorphism is `h^*α` preceded by `pullbackTwistComp`, the composition law
`Stacks.TensorSheafSpellingIso.pullbackCompIso` of the inverse image together with the transport
along the associativity `(h ≫ φ) ≫ ι = h ≫ (φ ≫ ι)`. Both clauses of
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible` are then the corresponding
clauses for `(φ, α)` pushed along `h`:

* in degree one, through `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.pullbackSectionHom_comp`
  — pulling a global section back along a composite is pulling it back twice — and through
  `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.pullbackNatTensorPowIso_inv_one_comp_unitorPow`
  and its section-level form
  `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.unitorPow_hom_app_pullSection_one`, which are
  the **left unit law** of the inverse image as an oplax monoidal functor,
  `Stacks.TensorSheafSpellingIso.pullbackCotensorator_leftUnitor`: that is what identifies the
  comparison of the first tensor powers with the pullback of the left unitor, and it is the only
  coherence this file needs;
* in degree `n`, through the semilinearity of the pullback of a section
  (`AlgebraicGeometry.pullbackSectionHom_smul`) and the composition law for
  `AlgebraicGeometry.Scheme.Hom.appLE`, which turn the local identity over
  `φ ⁻¹ᵁ D₊(f) ⊆ Y` into the same identity over an open of `Y'` mapping into it.

**Where the functor `F` and the bijection are.** This file states surjectivity as an existence
statement about weights and so needs no functor; the functor is built on top of it.
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fcolim`, the colimit of the `F_d` along
divisibility — which is what `F(Y)` is for quasi-compact `Y` — is in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorColimit.lean`, and
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.F`, its extension to a general `Y` by the limit
over the quasi-compact test objects, is in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorRepresentable.lean`. Those two files
consume the surjectivity below together with the injectivity of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorInjective.lean`,
and give the bijection of
[Stacks, Tag 01NC] as a single `Equiv` and a `CategoryTheory.Functor.RepresentableBy` datum for
`Proj(A)`.

## References

* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization (Away)
open Stacks.Ample (IsInvertibleModule)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjDegreeOpenUniversalTriple (universalVeroneseSections
  iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator (pullbackCotensorator
  pullbackNatTensorPowIso_inv_succ)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso
  top_le_preimage_top)
open Stacks.AlgebraicGeometry.ProjChartSectionPullback (pullbackNatTensorPowIso_inv_zero)
open Stacks.AlgebraicGeometry.ProjSectionsUnique (Pair)
open Stacks.AlgebraicGeometry.ProjTripleFunctorLaws (unitorPow_hom_app_pullSection_one)
open Stacks.AlgebraicGeometry.ProjTriplePullback (pullbackSections)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.PullbackUnitSection (unitPullbackHom pullbackSectionHom_app)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorSheafSpellingIso (pullbackCompIso pullbackCotensorator_leftUnitor)

universe u w

namespace Stacks.AlgebraicGeometry.ProjClassifyingPullback

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {Y Y' : Scheme.{u}}

/-- **Pulling a global section back along one of two equal morphisms.** The pullback of a module
along a morphism depends on the morphism, so an equality of morphisms moves the pulled-back
section by the transport it induces on the modules. -/
theorem pullbackSectionHom_congr {X Z : Scheme.{u}} {k k' : Z ⟶ X} (hk : k = k')
    (M : X.Modules) (s : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app
        (eqToHom (congrArg (fun m : Z ⟶ X => (Scheme.Modules.pullback m).obj M) hk)) ⊤
        (pullbackSectionHom k M ⊤ ⊤ (by simp) s)
      = pullbackSectionHom k' M ⊤ ⊤ (by simp) s := by
  subst hk
  simp

/-- **The pullback of a twist along a composite**, `(h ≫ φ)⁎𝒪_X(c) ≅ h^*(φ⁎𝒪_X(c))`: the
composition law of the inverse image, preceded by the transport along the associativity
`(h ≫ φ) ≫ ι = h ≫ (φ ≫ ι)` of the two readings of the composite as a morphism into `Proj(A)`.
This is the isomorphism `α` of the pulled-back pair is composed with. -/
def pullbackTwistComp (h : Y' ⟶ Y) (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) (c : ℤ) :
    pullbackTwist 𝒜 (h ≫ φ) c ≅ (Scheme.Modules.pullback h).obj (pullbackTwist 𝒜 φ c) :=
  eqToIso (congrArg
      (fun m : Y' ⟶ AlgebraicGeometry.Proj 𝒜 =>
        (Scheme.Modules.pullback m).obj (twistingSheaf 𝒜 c))
      (Category.assoc h φ (degreeOpen 𝒜 d).ι)) ≪≫
    ((pullbackCompIso h (toProj 𝒜 φ)).app (twistingSheaf 𝒜 c)).symm

/-- **The degree-`d` section of `f` pulled back along a composite is its pullback along `φ`,
pulled back along `h`**, through `pullbackTwistComp`. This is
`Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.pullbackSectionHom_comp` with the two readings of
the composite identified. -/
theorem pullbackTwistComp_hom_app_pullbackDegreeSection (h : Y' ⟶ Y)
    (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) (f : 𝒜 d) :
    (pullbackTwistComp 𝒜 h φ (d : ℤ)).hom.app ⊤ (pullbackDegreeSection 𝒜 (h ≫ φ) f)
      = pullbackSectionHom h (pullbackTwist 𝒜 φ (d : ℤ)) ⊤ ⊤ (by simp)
          (pullbackDegreeSection 𝒜 φ f) :=
  Eq.trans
    (congrArg
      (fun z : Γ((Scheme.Modules.pullback (h ≫ toProj 𝒜 φ)).obj (twistingSheaf 𝒜 (d : ℤ)), ⊤) =>
        Scheme.Modules.Hom.app
          ((pullbackCompIso h (toProj 𝒜 φ)).app (twistingSheaf 𝒜 (d : ℤ))).inv ⊤ z)
      (pullbackSectionHom_congr (Category.assoc h φ (degreeOpen 𝒜 d).ι)
        (twistingSheaf 𝒜 (d : ℤ))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒜 d f)))
    (Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.pullbackSectionHom_comp h (toProj 𝒜 φ)
      (twistingSheaf 𝒜 (d : ℤ))
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒜 d f)).symm

/-- **A local identity between pulled-back sections of the tensor powers.** If over an open `W`
of `Y` the global section `s` of `L ^⊗ n` is a multiple of `s'` by a function `c`, then over any
open of `Y'` mapping into `W` the pullback of `s` is the same multiple of the pullback of `s'`,
the function being `c` pulled back by `AlgebraicGeometry.Scheme.Hom.appLE`.

Pulling a section back is semilinear and the comparison of the tensor powers is a morphism of
`𝒪_{Y'}`-modules, so both the scalar action and the restriction pass through. -/
theorem resTop_pullSection_eq_smul {L : Y.Modules} [IsInvertibleModule Y L] (h : Y' ⟶ Y) (n : ℕ)
    (s s' : Γ(natTensorPow L n, ⊤)) {W : Y.Opens} {V : Y'.Opens} (hV : V ≤ h ⁻¹ᵁ W)
    (c : Γ(Y, W))
    (hss : resTop (natTensorPow L n) s W = c • resTop (natTensorPow L n) s' W) :
    resTop (natTensorPow ((Scheme.Modules.pullback h).obj L) n) (pullSection h L n s) V
      = h.appLE W V hV c
        • resTop (natTensorPow ((Scheme.Modules.pullback h).obj L) n)
            (pullSection h L n s') V := by
  have key : ∀ t : Γ(natTensorPow L n, ⊤),
      resTop (natTensorPow ((Scheme.Modules.pullback h).obj L) n) (pullSection h L n t) V
        = (pullbackNatTensorPowIso h L n).inv.app V
            (pullbackSectionHom h (natTensorPow L n) W V hV
              (resTop (natTensorPow L n) t W)) := fun t =>
    Eq.trans
      (Stacks.TensorPowerTrivialize.resTop_app (pullbackNatTensorPowIso h L n).inv _ V)
      (congrArg (Scheme.Modules.Hom.app (pullbackNatTensorPowIso h L n).inv V)
        (Eq.trans
          (Stacks.AlgebraicGeometry.ProjChartCocycleMatch.resTop_pullbackSectionHom h
            (natTensorPow L n) ⊤ (top_le_preimage_top h) (by simp) le_top t)
          (pullbackSectionHom_map h (natTensorPow L n) ⊤ W le_top V hV (by simp) t).symm))
  rw [key s, key s', hss, pullbackSectionHom_smul]
  exact Scheme.Modules.Hom.app_smul _ _ _

/-- **The effect on sections of one of two equal morphisms.** The two proofs of the inclusion of
opens are propositions, so only the morphisms have to agree. -/
theorem appLE_congr {X Z : Scheme.{u}} {k k' : Z ⟶ X} (hk : k = k') (U : X.Opens) (V : Z.Opens)
    (e : V ≤ k ⁻¹ᵁ U) (e' : V ≤ k' ⁻¹ᵁ U) (u : Γ(X, U)) :
    k.appLE U V e u = k'.appLE U V e' u := by
  subst hk
  rfl

/-- **The degree-one clause of compatibility is stable under pullback.** The degree-one value of
`ψ^d_{h ≫ φ}` is the degree-one value of `ψ^d_φ` pulled back along `h`
(`pullbackTwistComp_hom_app_pullbackDegreeSection`), and the degree-one value of `h^* ∘ ψ` is the
value of `ψ` pulled back along `h`
(`Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.unitorPow_hom_app_pullSection_one`); the clause
for `(φ, α)` therefore gives the clause for `(h ≫ φ, h^*α)` by applying `h^*` to it. -/
theorem degreeOnePullback {L : Y.Modules} [IsInvertibleModule Y L]
    (ψ : VeroneseSections 𝒜 d L) (p : Pair 𝒜 L d) (hp : IsCompatible 𝒜 ψ p) (h : Y' ⟶ Y)
    (x : 𝒜 (1 * d)) :
    (pullbackTwistComp 𝒜 h p.1 (d : ℤ) ≪≫ (Scheme.Modules.pullback h).mapIso p.2).hom.app ⊤
        ((twistCast 𝒜 (h ≫ p.1) (one_mul d)).hom.app ⊤ (psiPullbackHom 𝒜 (h ≫ p.1) 1 x))
      = (unitorPow ((Scheme.Modules.pullback h).obj L)).hom.app ⊤
          ((pullbackSections 𝒜 ψ h).toFun 1 x) := by
  have hx : (x : A) ∈ 𝒜 d := by simpa using x.2
  rw [twistCast_hom_app_psiPullbackHom 𝒜 (h ≫ p.1) x hx, Iso.trans_hom,
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    pullbackTwistComp_hom_app_pullbackDegreeSection 𝒜 h p.1 ⟨(x : A), hx⟩,
    show (pullbackSections 𝒜 ψ h).toFun 1 x = pullSection h L 1 (ψ.toFun 1 x) from rfl,
    unitorPow_hom_app_pullSection_one h L (ψ.toFun 1 x), ← hp.1 x,
    twistCast_hom_app_psiPullbackHom 𝒜 p.1 x hx]
  exact (pullbackSectionHom_app h p.2.hom ⊤ ⊤ (by simp)
    (pullbackDegreeSection 𝒜 p.1 ⟨(x : A), hx⟩)).symm

/-- **The degree-`n` clause of compatibility is stable under pullback.** The clause for `(φ, α)`
holds over the whole preimage `φ ⁻¹ᵁ D₊(f)`, and `resTop_pullSection_eq_smul` carries it to any
open of `Y'` mapping into that preimage; the scalar it produces is `φ^♯(a/f^n)` restricted along
`h`, which is `(h ≫ φ)^♯(a/f^n)` by the composition law for
`AlgebraicGeometry.Scheme.Hom.appLE`. -/
theorem degreeNPullback {L : Y.Modules} [IsInvertibleModule Y L]
    (ψ : VeroneseSections 𝒜 d L) (p : Pair 𝒜 L d) (hp : IsCompatible 𝒜 ψ p) (h : Y' ⟶ Y)
    (f : 𝒜 d) (V : Y'.Opens)
    (hV : V ≤ toProj 𝒜 (h ≫ p.1) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
    (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) (a : 𝒜 (n * d)) (hax : (a : A) = x) :
    resTop (natTensorPow ((Scheme.Modules.pullback h).obj L) n)
        ((pullbackSections 𝒜 ψ h).toFun n a) V
      = (toProj 𝒜 (h ≫ p.1)).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) V hV
          ((AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A)).hom (Away.mk 𝒜 f.2 n x hx))
        • resTop (natTensorPow ((Scheme.Modules.pullback h).obj L) n)
            ((pullbackSections 𝒜 ψ h).pow f.2 n) V := by
  have hVW : V ≤ h ⁻¹ᵁ (toProj 𝒜 p.1 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) := hV
  have key := resTop_pullSection_eq_smul h n (ψ.toFun n a) (ψ.pow f.2 n) hVW _
    (hp.2 f _ le_rfl n x hx a hax)
  rw [show (pullbackSections 𝒜 ψ h).toFun n a = pullSection h L n (ψ.toFun n a) from rfl,
    show (pullbackSections 𝒜 ψ h).pow f.2 n = pullSection h L n (ψ.pow f.2 n) from rfl, key]
  refine congrArg
    (fun z : Γ(Y', V) =>
      z • resTop (natTensorPow ((Scheme.Modules.pullback h).obj L) n)
        (pullSection h L n (ψ.pow f.2 n)) V) ?_
  refine Eq.trans ?_ (appLE_congr (Category.assoc h p.1 (degreeOpen 𝒜 d).ι).symm
    (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) V (by exact hV) hV _)
  refine Eq.trans ?_ (ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE h (toProj 𝒜 p.1)
      (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) _ V le_rfl hVW)
    ((AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A)).hom (Away.mk 𝒜 f.2 n x hx)))
  exact (CommRingCat.comp_apply _ _ _).symm

/-- **Compatibility is stable under pullback**, the second of the two statements about
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible` that the surjectivity of the
comparison of [Stacks, Tag 01NC] needs: if the pair `(φ, α)` is compatible with `ψ` then
`(h ≫ φ, h^*α ∘ pullbackTwistComp)` is compatible with the pulled-back graded map `h^* ∘ ψ`. -/
theorem isCompatible_pullbackSections {L : Y.Modules} [IsInvertibleModule Y L]
    (ψ : VeroneseSections 𝒜 d L) (p : Pair 𝒜 L d) (hp : IsCompatible 𝒜 ψ p) (h : Y' ⟶ Y) :
    IsCompatible 𝒜 (pullbackSections 𝒜 ψ h)
      ⟨h ≫ p.1, pullbackTwistComp 𝒜 h p.1 (d : ℤ) ≪≫ (Scheme.Modules.pullback h).mapIso p.2⟩ :=
  ⟨fun x => degreeOnePullback 𝒜 ψ p hp h x,
    fun f V hV n x hx a hax => degreeNPullback 𝒜 ψ p hp h f V hV n x hx a hax⟩

/-- **The classification of [Stacks, Tag 01N8] is natural in `Y`**: the morphism `Y' ⟶ U_d`
classified by the pullback of `ψ` along `h : Y' ⟶ Y` is `h` followed by the morphism classified
by `ψ`. By the uniqueness half of the tag, since `isCompatible_pullbackSections` exhibits a
compatible pair whose first component is `h` followed by the classified morphism of `ψ`. -/
theorem classifyingHom_pullbackSections (hd : 0 < d) {L : Y.Modules} [IsInvertibleModule Y L]
    (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) (h : Y' ⟶ Y) :
    ProjTripleClassifying.classifyingHom 𝒜 hd (pullbackSections 𝒜 ψ h)
        (ProjTriplePullback.iSup_nonvanishingOpen_pullbackSections 𝒜 ψ h hgen)
      = h ≫ ProjTripleClassifying.classifyingHom 𝒜 hd ψ hgen :=
  (ProjTripleClassifying.eq_classifyingHom_of_isCompatible 𝒜 hd (pullbackSections 𝒜 ψ h)
    (ProjTriplePullback.iSup_nonvanishingOpen_pullbackSections 𝒜 ψ h hgen) _
    (isCompatible_pullbackSections 𝒜 ψ (ProjTripleClassifying.classifyingPair 𝒜 hd ψ hgen)
      (ProjTripleClassifying.isCompatible_classifyingPair 𝒜 hd ψ hgen) h)).symm

section Universal

variable {S : Type u} {ς : Type w} [CommRing S] [SetLike ς S] [AddSubgroupClass ς S]
  (𝒮 : ℕ → ς) [GradedRing 𝒮]

/-- **The morphism classified by the universal family is the identity of `U_d`.** [Stacks, Tag
01N8] attaches to a triple the unique pair `(φ, α)` compatible with its graded map, and
`Stacks.AlgebraicGeometry.ProjUniversalCompatible.isCompatible_universalVeroneseSections` says
that `(𝟙, id)` is such a pair for the universal family. This is the assertion of [Stacks, Tag
01N9] that `(d, 𝒪_{U_d}(d), ψ^d)` is the *universal* family, read on the identity. -/
theorem classifyingHom_universalVeroneseSections (d : ℕ) (hd : 0 < d) :
    ProjTripleClassifying.classifyingHom 𝒮 hd
        (universalVeroneseSections 𝒮 d)
        (iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top 𝒮 d)
      = 𝟙 (degreeOpen 𝒮 d).toScheme :=
  (ProjTripleClassifying.eq_classifyingHom_of_isCompatible 𝒮 hd _ _ _
    (ProjUniversalCompatible.isCompatible_universalVeroneseSections 𝒮 d)).symm

end Universal

end Stacks.AlgebraicGeometry.ProjClassifyingPullback

namespace Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y Y' : Scheme.{u}} {d : ℕ}

/-- **The comparison `F_d(Y) ⟶ Mor(Y, Proj(A))` is natural in `Y`**: the morphism classified by
the pullback of a class along `h : Y' ⟶ Y` is `h` followed by the morphism classified by the
class. This is `classifyingHom_pullbackSections` read on classes, with the open immersion
`U_d ⟶ Proj(A)` moved past the composite. -/
theorem Fd.classifyingMorphism_pullback (hd : 0 < d) (h : Y' ⟶ Y) (ξ : Fd 𝒜 d Y) :
    Fd.classifyingMorphism 𝒜 hd (Fd.pullback 𝒜 h ξ)
      = h ≫ Fd.classifyingMorphism 𝒜 hd ξ := by
  induction ξ using Quotient.ind with
  | _ t =>
      have := t.isInvertible
      change toProj 𝒜 (ProjTripleClassifying.classifyingHom 𝒜 hd
          (ProjTriplePullback.pullbackSections 𝒜 t.psi h) _)
        = h ≫ toProj 𝒜 (ProjTripleClassifying.classifyingHom 𝒜 hd t.psi t.generated)
      rw [ProjClassifyingPullback.classifyingHom_pullbackSections 𝒜 hd t.psi t.generated h]
      exact Category.assoc h _ (degreeOpen 𝒜 d).ι

section Universal

variable {S : Type u} {ς : Type w} [CommRing S] [SetLike ς S] [AddSubgroupClass ς S]
  (𝒮 : ℕ → ς) [GradedRing 𝒮]

/-- **The universal family `(d, 𝒪_{U_d}(d), ψ^d)` of [Stacks, Tag 01N9], as a weight-`d` triple
over `U_d`.** Its three fields are the invertible module, the graded map and the generation
condition established in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjDegreeOpenRepresents.lean` and
`StacksFrontier/AlgebraicGeometry/TwistTensor/UniversalVeroneseSections.lean`. -/
def universalDegreeTriple (d : ℕ) : DegreeTriple 𝒮 d (degreeOpen 𝒮 d).toScheme where
  module := ProjDegreeOpenRepresents.universalTwist 𝒮 d
  isInvertible := inferInstance
  psi := universalVeroneseSections 𝒮 d
  generated := iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top 𝒮 d

/-- **The class of the universal family classifies the open immersion `U_d ⟶ Proj(A)`.** This is
`classifyingHom_universalVeroneseSections` read on classes. -/
theorem Fd.classifyingMorphism_universalDegreeTriple (d : ℕ) (hd : 0 < d) :
    Fd.classifyingMorphism 𝒮 hd (Fd.mk 𝒮 (universalDegreeTriple 𝒮 d))
      = (degreeOpen 𝒮 d).ι := by
  change toProj 𝒮 (ProjTripleClassifying.classifyingHom 𝒮 hd
      (universalVeroneseSections 𝒮 d) _) = _
  rw [ProjClassifyingPullback.classifyingHom_universalVeroneseSections 𝒮 d hd]
  exact Category.id_comp _

/-- **Surjectivity of the comparison at a fixed weight**: a morphism `φ : Y ⟶ U_d` is classified
by the pullback along `φ` of the universal family of [Stacks, Tag 01N9]. The naturality of the
comparison turns the identity classified by the universal family into `φ` itself.

This is the statement whose absence left the comparison of [Stacks, Tag 01NC] with only its
injectivity half; the quasi-compact statement below is this one together with the factorization
of a morphism through a single `U_d`. -/
theorem Fd.classifyingMorphism_pullback_universalDegreeTriple {d : ℕ} (hd : 0 < d)
    (φ : Y ⟶ (degreeOpen 𝒮 d).toScheme) :
    Fd.classifyingMorphism 𝒮 hd
        (Fd.pullback 𝒮 φ (Fd.mk 𝒮 (universalDegreeTriple 𝒮 d)))
      = toProj 𝒮 φ := by
  rw [Fd.classifyingMorphism_pullback 𝒮 hd φ _,
    Fd.classifyingMorphism_universalDegreeTriple 𝒮 d hd]

/-- **Stacks Tag 01NC: the comparison `F(Y) ⟶ Mor(Y, Proj(A))` is surjective**, for a
quasi-compact scheme `Y`. Let `A` be a graded ring and `X = Proj(A)`. Every morphism `Y ⟶ X` is
classified by a strict equivalence class of triples of some weight `d ≥ 1`, i.e. lies in the
image of `Fd.classifyingMorphism` — which is what surjectivity of the comparison out of
`F(Y) = ⋃_{d ≥ 1} F_d(Y)` says.

Two steps. The morphism factors through a single `U_d` with `d ≥ 1`
(`AlgebraicGeometry.Proj.exists_pos_existsUnique_factorization`, the first of the two reductions
the source's proof omits), and the factorization is classified by the pullback along it of the
universal family of [Stacks, Tag 01N9]
(`Fd.classifyingMorphism_pullback_universalDegreeTriple`). -/
theorem Fd.exists_pos_classifyingMorphism_eq [CompactSpace Y]
    (φ : Y ⟶ AlgebraicGeometry.Proj 𝒮) :
    ∃ (d : ℕ) (hd : 0 < d) (ξ : Fd 𝒮 d Y), Fd.classifyingMorphism 𝒮 hd ξ = φ := by
  obtain ⟨e, he, ⟨χ, hχ, -⟩⟩ := AlgebraicGeometry.Proj.exists_pos_existsUnique_factorization 𝒮 φ
  exact ⟨e, he, Fd.pullback 𝒮 χ (Fd.mk 𝒮 (universalDegreeTriple 𝒮 e)),
    (Fd.classifyingMorphism_pullback_universalDegreeTriple 𝒮 he χ).trans hχ⟩

end Universal

end Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

end
