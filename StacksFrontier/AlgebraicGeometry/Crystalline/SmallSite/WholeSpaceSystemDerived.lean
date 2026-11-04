module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionGood07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionOpen07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechLocal07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechPackage07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechProducts07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Resolution07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemAffine
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Proposition 60.20.1, Tag 07JN]: the complex `M(•)` computes `RΓ(Cris(X/S), F)`

Work in a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine and `p`
nilpotent on `Γ(X, ⊤)`, let `(X, T(n)_e, δ(n))` be the cosimplicial system of thickenings of the
proof of [Stacks, Tag 07JN] (`...SmallSite.wholeSpaceSystem`), and for a sheaf `F` on
`Cris(X/S)` let `M(n) = lim_e Γ((X, T(n)_e, δ(n)), F)`.  [Stacks, Tag 07JN] says that for `F`
locally quasi-coherent with locally surjective comparison maps `c_f` along closed immersions, the
complex `M(0) → M(1) → M(2) → ⋯` computes `RΓ(Cris(X/S), F)`.  This file proves it in the
derived category: `...SmallSite.wholeSpaceSystemDerivedIso` is an isomorphism
`M(•) ≅ RΓ(Cris(X/S), F)` in `D⁺(Ab)`, `RΓ` being `...SmallSite.derivedGlobalSections`.

## The comparison

The isomorphism is the Čech comparison of the proof.  For an injective resolution `I^•` of `F`
consider the double complex `(n, a) ↦ lim_e I^a(T(n)_e)` (`...SmallSite.cechDoubleComplex`).

* Its columns resolve the `M(n)`, because the higher cohomology of `F` vanishes over the affine
  objects `T(n)_e` ([Stacks, Tag 07JJ]) and the towers `e ↦ F(T(n)_e)` and `e ↦ I^a(T(n)_e)` are
  Mittag-Leffler; so `M(•) ⟶ Tot` is a quasi-isomorphism (`...SmallSite.cechComparison`).
* Its rows resolve the global sections of the `I^a`, because the system is a pro-covering of `X`
  (`isOpenProCovering_wholeSpaceSystem`: the affine objects cover, each maps to some `T(0)_e`,
  and the `T(n)_e` are pro-products, [Stacks, Tag 07L4]) and the Čech complex of an injective
  sheaf over a pro-covering resolves its sections; so `Γ(Cris(X/S), I^•) ⟶ Tot` is a
  quasi-isomorphism (`...SmallSite.cechAugmentationOpen`).
* `Γ(Cris(X/S), I^•)` represents `RΓ(Cris(X/S), F)`.

## Main results

* `isOpenProCovering_wholeSpaceSystem`, `hasAffineMonoLevels_wholeSpaceSystem` — the system is a
  pro-covering of `X` with affine levels and monomorphic tower maps.
* `wholeSpaceSystemDerivedIsoOfAbelian` — `M(•) ≅ RΓ(Cris(X/S), G)` in `D(Ab)` for an abelian
  sheaf `G` satisfying the conclusion of [Stacks, Tag 07JJ] with surjective tower restrictions,
  with `wholeSpaceSystemDerivedIsoOfAbelian_hom` recording that it is the Čech zigzag.
* `wholeSpaceSystemDerivedIso` — **[Stacks, Tag 07JN]**, in `D⁺(Ab)`.
* `wholeSpaceSystemDerivedHomologyIso` — its cohomology,
  `H^j(M(0) → M(1) → ⋯) ≅ H^j(Cris(X/S), F)`.

## References

* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.17.5, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe w w' u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- **The system `(X, T(n)_e, δ(n))` is a pro-covering of the whole of `X`.** -/
theorem isOpenProCovering_wholeSpaceSystem :
    IsOpenProCovering S ⊤ (wholeSpaceSystem S hp) where
  liesOver _ _ := le_top
  affine_covers B := generate_hasAffineAmbient_mem S B
  reach B hB _ := by
    have : IsAffine B.obj.thickening.target.scheme := hB
    have : IsAffine B.obj.thickening.source := (isAffineObject_of_isAffine S B).1
    exact exists_hom_to_wholeSpaceSystemOf_level (hp := hp) (g := wholeSpacePresentation S hp)
      (hg := wholeSpacePresentation_surjective S hp) B
  isProProductAt B hB :=
    have : IsAffine B.obj.thickening.target.scheme := hB
    { exists_hom := fun n e φ => exists_wholeSpaceSystemOf_desc_of_isAffineObject (hp := hp)
        (g := wholeSpacePresentation S hp) (hg := wholeSpacePresentation_surjective S hp) B
        (isAffineObject_of_isAffine S B) n e φ
      eventually_eq := fun n e ψ ψ' h => ⟨e, le_rfl, by
        rw [wholeSpaceSystemOf_hom_ext_of_isAffineObject (hp := hp)
          (g := wholeSpacePresentation S hp) (hg := wholeSpacePresentation_surjective S hp) B
          (isAffineObject_of_isAffine S B) ψ ψ' h]⟩ }

/-- **The system `(X, T(n)_e, δ(n))` has affine ambient schemes and monomorphic tower maps.** -/
theorem hasAffineMonoLevels_wholeSpaceSystem : HasAffineMonoLevels (wholeSpaceSystem S hp) where
  mono n e :=
    have : IsClosedImmersion
        (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).hom.targetHom.hom :=
      isClosedImmersion_wholeSpaceSystemOf_map S hp (wholeSpacePresentation S hp)
        (wholeSpacePresentation_surjective S hp) n (Nat.le_succ e)
    mono_of_mono_targetHom _ inferInstance
  isAffine n e := isAffine_target_wholeSpaceSystem hp n e

/-- The sections over `X` of the Zariski direct image are the global sections:
`Γ(X, u_{X/S, *} G) ≅ Γ(Cris(X/S), G)`, naturally in `G`. -/
def zariskiTopSectionsIso :
    zariskiDirectImage S ⋙ (sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj (op ⊤) ≅
      globalSections S :=
  Functor.isoWhiskerLeft (zariskiDirectImage S)
      (Sheaf.ΓNatIsoSheafSections (opensTopology S) AddCommGrpCat.{u + 1}
        Limits.isTerminalTop).symm ≪≫
    zariskiGlobalSectionsDirectImageIso S

/-- The complex `Γ(X, u_{X/S, *} K^•)` is the complex of global sections `Γ(Cris(X/S), K^•)`. -/
def openSectionsComplexTopIso
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) :
    openSectionsComplex ⊤ K ≅ ((globalSections S).mapHomologicalComplex _).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun a => (zariskiTopSectionsIso (S := S)).app (K.X a))
    (fun a b _ => ((zariskiTopSectionsIso (S := S)).hom.naturality (K.d a b)).symm)

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

variable (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hvan : Vanishing07JJ S G)
  (hGs : HasSurjectiveLevelTransitions (wholeSpaceSystem S hp) G)

/-- **The comparison `M(•) ⟶ RΓ(Cris(X/S), G)` in `D(Ab)`** of the proof of
[Stacks, Tag 07JN], for an abelian sheaf `G` on `Cris(X/S)` satisfying the conclusion of
[Stacks, Tag 07JJ] and with surjective restrictions along the towers of the system.  It is the
Čech zigzag of the proof, at the injective resolution `I^•` of `G` of
`CategoryTheory.InjectiveResolution.of`:

`M(•) ⟶ Tot(lim_e I^•(T(•)_e)) ⟵ Γ(X, u_{X/S, *} I^•) = Γ(Cris(X/S), I^•) = RΓ(Cris(X/S), G)`,

the first arrow being `...SmallSite.cechComparison` (the columns of the Čech double complex
resolve the `M(n)`) and the second `...SmallSite.cechAugmentationOpen` (the Čech complex of an
injective sheaf over the pro-covering `T(•)` of `X` resolves its global sections); the second is
a quasi-isomorphism, so it is inverted in the derived category. -/
def wholeSpaceSystemDerivedIsoOfAbelian :
    DerivedCategory.Q.obj ((sectionsComplex (wholeSpaceSystem S hp) G.obj).extend
        ComplexShape.embeddingUpNat) ≅
      DerivedCategory.Plus.ι.obj ((derivedGlobalSections S).obj G) :=
  asIso (DerivedCategory.Q.map (cechComparison (hasAffineMonoLevels_wholeSpaceSystem hp)
      (vanishingOnLevels07Q9_of_vanishing07JJ (hasAffineMonoLevels_wholeSpaceSystem hp) hvan)
      hGs (InjectiveResolution.of G))) ≪≫
    (asIso (DerivedCategory.Q.map (cechAugmentationOpen (isOpenProCovering_wholeSpaceSystem hp)
      (InjectiveResolution.of G).cocomplex))).symm ≪≫
    DerivedCategory.Q.mapIso ((ComplexShape.embeddingUpNat.extendFunctor
      AddCommGrpCat.{u + 1}).mapIso
        (openSectionsComplexTopIso (InjectiveResolution.of G).cocomplex)) ≪≫
    DerivedCategory.Q.mapIso
      (Stacks.Cohomology.mapCochainComplexIso (globalSections S) (InjectiveResolution.of G)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      (Stacks.Cohomology.mapResolutionIsoRightDerived (globalSections S) (InjectiveResolution.of G))

/-- **The comparison is the Čech zigzag**: the class of `...SmallSite.cechComparison`, followed
by the inverse of the class of the quasi-isomorphism `...SmallSite.cechAugmentationOpen`, and the
identifications `Γ(X, u_{X/S, *} I^•) = Γ(Cris(X/S), I^•) = RΓ(Cris(X/S), G)`. -/
theorem wholeSpaceSystemDerivedIsoOfAbelian_hom :
    (wholeSpaceSystemDerivedIsoOfAbelian hp G hvan hGs).hom =
      DerivedCategory.Q.map (cechComparison (hasAffineMonoLevels_wholeSpaceSystem hp)
        (vanishingOnLevels07Q9_of_vanishing07JJ (hasAffineMonoLevels_wholeSpaceSystem hp) hvan)
        hGs (InjectiveResolution.of G)) ≫
      inv (DerivedCategory.Q.map (cechAugmentationOpen (isOpenProCovering_wholeSpaceSystem hp)
        (InjectiveResolution.of G).cocomplex)) ≫
      DerivedCategory.Q.map ((ComplexShape.embeddingUpNat.extendFunctor
        AddCommGrpCat.{u + 1}).map
          (openSectionsComplexTopIso (InjectiveResolution.of G).cocomplex).hom) ≫
      DerivedCategory.Q.map
        (Stacks.Cohomology.mapCochainComplexIso (globalSections S) (InjectiveResolution.of G)).inv ≫
      DerivedCategory.Plus.ι.map
        (Stacks.Cohomology.mapResolutionIsoRightDerived (globalSections S)
          (InjectiveResolution.of G)).hom :=
  rfl

/-- **`H^j(M(•)) ≅ H^j(RΓ(Cris(X/S), G)) ≅ H^j(Cris(X/S), G)`**, the cohomology of the derived
comparison `...SmallSite.wholeSpaceSystemDerivedIsoOfAbelian` in degree `j`, read through the
identification of the cohomology of `RΓ` with the graded crystalline cohomology
(`...SmallSite.homologyDerivedGlobalSectionsIsoObj`). -/
def wholeSpaceSystemDerivedHomologyIsoOfAbelian (j : ℕ) :
    (sectionsComplex (wholeSpaceSystem S hp) G.obj).homology j ≅
      (cohomologyFunctor S j).obj G :=
  ((sectionsComplex (wholeSpaceSystem S hp) G.obj).extendHomologyIso
      ComplexShape.embeddingUpNat (j' := (j : ℤ)) rfl).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} (j : ℤ)).app _).symm ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (j : ℤ)).mapIso
      (wholeSpaceSystemDerivedIsoOfAbelian hp G hvan hGs) ≪≫
    homologyDerivedGlobalSectionsIsoObj S G j

end Derived

/-! ### [Stacks, Tag 07JN] -/

section Tag

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
  (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
  (hM : CohomologyRestriction.IsSurjectiveComparison F.val)

/-- **[Stacks, Proposition 60.20.1, Tag 07JN]: the complex `M(0) → M(1) → M(2) → ⋯` computes
`RΓ(Cris(X/S), F)`**, as an isomorphism in the bounded below derived category `D⁺(Ab)`:

`M(•) ≅ RΓ(Cris(X/S), F)`,

for a sheaf `F` of `𝒪_{X/S}`-modules on `Cris(X/S)`, over an affine situation (`X` and `S`
affine, `p` nilpotent on `Γ(X, ⊤)`), satisfying the two hypotheses of the tag:

1. `F` is locally quasi-coherent, and
2. for every morphism of `Cris(X/S)` whose map of ambient schemes is a closed immersion, the
   comparison map `c_f` is locally surjective.

Here `M(n) = lim_e Γ((X, T(n)_e, δ(n)), F)` for the system `(X, T(n)_e, δ(n))` of the proof
(`...SmallSite.wholeSpaceSystem`, built from the presentation of the
`...SmallSite.WholeSpacePresentation` instance), the complex being extended by zero to `ℤ`, and
`RΓ(Cris(X/S), -)` is `...SmallSite.derivedGlobalSections`, the right derived functor of global
sections.  The isomorphism is the canonical comparison of the proof: the Čech zigzag
`M(•) ⟶ Tot(lim_e I^•(T(•)_e)) ⟵ Γ(Cris(X/S), I^•)` through the Čech double complex of an
injective resolution `I^•` of `F` (`...SmallSite.wholeSpaceSystemDerivedIsoOfAbelian_hom`).
Hypothesis (1) gives the vanishing of [Stacks, Tag 07JJ] at the objects of the system, and (1) and
(2) the surjectivity of the restrictions along its towers; these are what make both arrows of the
zigzag quasi-isomorphisms. -/
@[stacks 07JN "the complex M(0) → M(1) → M(2) → ⋯ of the system (X, T(n)_e, δ(n)) computes \
RΓ(Cris(X/S), F): an isomorphism M(•) ≅ RΓ(Cris(X/S), F) in D⁺(Ab), the Čech comparison through an \
injective resolution, for F locally quasi-coherent with c_f locally surjective along closed \
immersions, X and S affine"]
def wholeSpaceSystemDerivedIso :
    DerivedCategory.Plus.Q.obj
        (Stacks.Cohomology.extendPlusObj
          (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj)) ≅
      (derivedGlobalSections S).obj (abelianSheaf F) :=
  DerivedCategory.Plus.ι.preimageIso
    (wholeSpaceSystemDerivedIsoOfAbelian hp (abelianSheaf F) (vanishing07JJ_abelianSheaf F hF)
      (fun n e => surjective_wholeSpaceSystem_level_map hp F hF hM n e))

/-- **The derived comparison of [Stacks, Tag 07JN] is the Čech comparison**: read in `D(Ab)` it is
`...SmallSite.wholeSpaceSystemDerivedIsoOfAbelian`. -/
theorem ι_map_wholeSpaceSystemDerivedIso_hom :
    DerivedCategory.Plus.ι.map (wholeSpaceSystemDerivedIso hp F hF hM).hom =
      (wholeSpaceSystemDerivedIsoOfAbelian hp (abelianSheaf F) (vanishing07JJ_abelianSheaf F hF)
        (fun n e => surjective_wholeSpaceSystem_level_map hp F hF hM n e)).hom :=
  DerivedCategory.Plus.ι.map_preimage _

/-- **The cohomology of the derived comparison of [Stacks, Tag 07JN]**:
`H^j(M(0) → M(1) → ⋯) ≅ H^j(Cris(X/S), F)` for every `j`, the degree-`j` cohomology of
`...SmallSite.wholeSpaceSystemDerivedIso`. -/
def wholeSpaceSystemDerivedHomologyIso (j : ℕ) :
    (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j ≅
      (cohomologyFunctor S j).obj (abelianSheaf F) :=
  wholeSpaceSystemDerivedHomologyIsoOfAbelian hp (abelianSheaf F)
    (vanishing07JJ_abelianSheaf F hF)
    (fun n e => surjective_wholeSpaceSystem_level_map hp F hF hM n e) j

end Tag

end Crystalline.GlobalCrystallineSituation.SmallSite

end
