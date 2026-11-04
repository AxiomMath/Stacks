module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Acyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Envelope
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorSheafGlobalSections

/-!
# The cosimplicial envelope of the situation's own presentation

Fix a global crystalline situation `(p, (S, I, γ), X)`. The system of thickenings
`(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN], `wholeSpaceSystem`, is built from the polynomial
presentation `A[x_c : c ∈ C] → C = Γ(X, ⊤)` of `Crystalline.canonicalPresentation`. We define the
`Crystalline.CosimplicialEnvelope` of that presentation — the cosimplicial ring `D(*)` of
`p`-adically completed divided power envelopes together with its completed divided power
differentials — and read [Stacks, Tag 07L9] and [Stacks, Tag 07LA] on it.

As a consequence, the vanishing `Vanishing07LF` of [Stacks, Tag 07LF] follows from the existence,
for each `F` satisfying hypotheses (1) and (2) of [Stacks, Tag 07JN] and each `i > 0`, of a
cosimplicial `D(*)`-module `M_*` and an isomorphism of cosimplicial abelian groups

`M(•)  ≅  M_* ⊗̂_{D(*)} Ω^i_{D(*)}`,

where `M(•)` is `cosimplicialSections` of the system at the coefficient sheaf
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`. At a fixed `p`-adic level `e`, an identification of `M(•)_e` with
`L_* ⊗_{D(*)} Ω^i_{D(*)}`, uncompleted, makes the level-`e` Moore complex acyclic.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `wholeSpaceEnvelope`: the cosimplicial envelope of the situation's own presentation, the value
  of `Crystalline.cosimplicialEnvelope` at `Crystalline.canonicalPresentation` of the affine
  crystalline situation of [Stacks, Tag 07MD] attached to the global one.
* `wholeSpaceEnvelopeRing`: its cosimplicial ring `D(0) → D(1) → D(2) → ⋯`.
* `wholeSpaceEnvelopeDifferentials`: the cosimplicial module `Ω_{D(*)}` over it.
* `wholeSpaceCompletedForms`: the cosimplicial module `M_* ⊗̂_{D(*)} Ω^i_{D(*)}` of
  [Stacks, Tag 07LA], for a cosimplicial `D(*)`-module `M_*`.
* `levelCosimplicialSections`: the cosimplicial group `M(•)_e` of sections at a fixed `p`-adic
  level `e`.

## Main results

* `homotopic_id_wholeSpaceDifferentials_zero`: [Stacks, Tag 07L9] at this envelope.
* `homotopic_id_wholeSpaceCompletedForms_zero`: [Stacks, Tag 07LA] at this envelope: for `i > 0`
  the cosimplicial module `M_* ⊗̂_{D(*)} Ω^i_{D(*)}` is homotopic to zero.
* `isZero_homology_alternatingCofaceMapComplex_wholeSpaceCompletedForms`: the Moore complex of its
  underlying cosimplicial abelian group, lifted to the coefficient universe of the cohomology of
  `Cris(X/S)`, is acyclic.
* `homotopic_id_tensor_wholeSpaceForms_zero`: [Stacks, Tag 07LA] at this envelope with the tensor
  product uncompleted: `L_* ⊗_{D(*)} Ω^i_{D(*)}` is homotopic to zero for every cosimplicial
  `D(*)`-module `L_*` and every `i > 0`.
* `isZero_homology_alternatingCofaceMapComplex_tensor_wholeSpaceForms`: the acyclicity of its
  Moore complex, in the coefficient universe of the cohomology of `Cris(X/S)`.
* `isZero_homology_levelCosimplicialSections_of_iso`: an identification of `M(•)_e` with
  `L_* ⊗_{D(*)} Ω^i_{D(*)}` makes the level-`e` Moore complex acyclic.
* `vanishing07LF_of_cosimplicialSectionsIso`: `Vanishing07LF` follows from an isomorphism
  `M(•) ≅ M_* ⊗̂_{D(*)} Ω^i_{D(*)}` for every `F` and every `i > 0`.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07L9](https://stacks.math.columbia.edu/tag/07L9)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 07KQ](https://stacks.math.columbia.edu/tag/07KQ)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicTopology Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

section Presentation

variable [WholeSpacePresentation S hp]

/-! ### The envelope of the situation's own presentation -/

/-- The cosimplicial envelope `Crystalline.CosimplicialEnvelope` of the presentation
`Crystalline.canonicalPresentation` of `Γ(X, ⊤)` over `Γ(S, ⊤)`, from which the system
`(X, T(n)_e, δ(n))` of `wholeSpaceSystem` is built. -/
def wholeSpaceEnvelope :
    _root_.Crystalline.CosimplicialEnvelope (affineSituation S hp)
      (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) :=
  _root_.Crystalline.cosimplicialEnvelope (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp)

/-- The cosimplicial ring `D(0) → D(1) → D(2) → ⋯` of the situation's own presentation: in
degree `n` the `p`-adically completed divided power envelope of the kernel of
`P ⊗_A ⋯ ⊗_A P → Γ(X, ⊤)` out of the `(n + 1)`-fold tensor power of
`Crystalline.canonicalPresentation`. -/
abbrev wholeSpaceEnvelopeRing : CosimplicialObject CommRingCat.{u} :=
  _root_.Crystalline.cosimplicialEnvelopeRing (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp)

/-- The cosimplicial module `Ω_{D(0)} → Ω_{D(1)} → ⋯` of `p`-adically completed divided power
differentials over `wholeSpaceEnvelopeRing`. -/
abbrev wholeSpaceEnvelopeDifferentials :
    _root_.Crystalline.CosimplicialModule (wholeSpaceEnvelopeRing hp) :=
  _root_.Crystalline.cosimplicialEnvelopeDifferentials (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp)

/-- The cosimplicial module `M_* ⊗̂_{D(*)} Ω^i_{D(*)}` of [Stacks, Tag 07LA] over the situation's
own `D(*)`: the `p`-adic completion of the degreewise tensor product of `M_*` with the `p`-adic
completion of the `i`-th exterior power of `Ω_{D(*)}`. -/
def wholeSpaceCompletedForms
    (M : _root_.Crystalline.CosimplicialModule (wholeSpaceEnvelopeRing hp)) (i : ℕ) :
    _root_.Crystalline.CosimplicialModule (wholeSpaceEnvelopeRing hp) :=
  (_root_.Crystalline.pAdicCosimplicialIdeal (wholeSpaceEnvelopeRing hp)
      (affineSituation S hp).p).completion
    (M ⊗ (_root_.Crystalline.pAdicCosimplicialIdeal (wholeSpaceEnvelopeRing hp)
        (affineSituation S hp).p).completion
      ((_root_.Crystalline.exteriorPowerFunctor (wholeSpaceEnvelopeRing hp) i).functor.obj
        (wholeSpaceEnvelopeDifferentials hp)))

/-- [Stacks, Tag 07L9] at the situation's own envelope: the identity endomorphism of
`Ω_{D(*)}` is homotopic to its zero endomorphism. -/
theorem homotopic_id_wholeSpaceDifferentials_zero :
    _root_.Crystalline.Homotopic (𝟙 (wholeSpaceEnvelopeDifferentials hp)) 0 :=
  _root_.Crystalline.cosimplicialEnvelope_differentials_homotopic_zero _ _ _

/-- [Stacks, Tag 07LA] at the situation's own envelope: for every cosimplicial `D(*)`-module
`M_*` and every `i > 0` the cosimplicial module `M_* ⊗̂_{D(*)} Ω^i_{D(*)}` is homotopic to
zero. -/
theorem homotopic_id_wholeSpaceCompletedForms_zero
    (M : _root_.Crystalline.CosimplicialModule (wholeSpaceEnvelopeRing hp)) {i : ℕ}
    (hi : 0 < i) :
    _root_.Crystalline.Homotopic (𝟙 (wholeSpaceCompletedForms hp M i)) 0 :=
  _root_.Crystalline.cosimplicialEnvelope_completedForms_homotopic_zero _ _ _ M hi

/-- The Moore complex of `M_* ⊗̂_{D(*)} Ω^i_{D(*)}` is acyclic for `i > 0`, after the universe
lift to the coefficient universe `u + 1` in which the cohomology of `Cris(X/S)` lives. -/
theorem isZero_homology_alternatingCofaceMapComplex_wholeSpaceCompletedForms
    (M : _root_.Crystalline.CosimplicialModule (wholeSpaceEnvelopeRing hp)) {i : ℕ}
    (hi : 0 < i) (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
      ((_root_.Crystalline.cosimplicialModuleForget (wholeSpaceEnvelopeRing hp)).obj
          (wholeSpaceCompletedForms hp M i) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u})).homology j) :=
  _root_.Crystalline.isZero_homology_alternatingCofaceMapComplex_uliftFunctor_of_homotopic_id_zero
    (homotopic_id_wholeSpaceCompletedForms_zero hp M hi) j

/-- The cosimplicial module `L_* ⊗_{D(*)} Ω^i_{D(*)}`, with the tensor product uncompleted, is
homotopic to zero for every cosimplicial `D(*)`-module `L_*` and every `i > 0`. -/
theorem homotopic_id_tensor_wholeSpaceForms_zero
    (L : _root_.Crystalline.CosimplicialModule (wholeSpaceEnvelopeRing hp)) {i : ℕ}
    (hi : 0 < i) :
    _root_.Crystalline.Homotopic (𝟙 (L ⊗
      (_root_.Crystalline.exteriorPowerFunctor (wholeSpaceEnvelopeRing hp) i).functor.obj
        (wholeSpaceEnvelopeDifferentials hp))) 0 :=
  _root_.Crystalline.homotopic_id_tensor_zero
    (_root_.Crystalline.homotopic_id_exteriorPower_zero hi
      (homotopic_id_wholeSpaceDifferentials_zero hp)) L

/-- The Moore complex of `L_* ⊗_{D(*)} Ω^i_{D(*)}` is acyclic for `i > 0`, after the universe
lift to the coefficient universe `u + 1` of the cohomology of `Cris(X/S)`. -/
theorem isZero_homology_alternatingCofaceMapComplex_tensor_wholeSpaceForms
    (L : _root_.Crystalline.CosimplicialModule (wholeSpaceEnvelopeRing hp)) {i : ℕ}
    (hi : 0 < i) (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
      ((_root_.Crystalline.cosimplicialModuleForget (wholeSpaceEnvelopeRing hp)).obj
          (L ⊗ (_root_.Crystalline.exteriorPowerFunctor (wholeSpaceEnvelopeRing hp) i).functor.obj
            (wholeSpaceEnvelopeDifferentials hp)) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u})).homology j) :=
  _root_.Crystalline.isZero_homology_alternatingCofaceMapComplex_uliftFunctor_of_homotopic_id_zero
    (homotopic_id_tensor_wholeSpaceForms_zero hp L hi) j

/-! ### The level-wise step of the source's proof -/

/-- The cosimplicial abelian group `M(•)_e` at a fixed `p`-adic level `e`: the degree-`n` group
is `Γ((X, T(n)_e, δ(n)), G)`. The cosimplicial module `M(•)` of [Stacks, Tag 07JN] is the limit of
these over `e`. -/
def levelCosimplicialSections (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (G : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (e : ℕ) :
    CosimplicialObject AddCommGrpCat.{u + 1} :=
  sectionSystem T G ⋙ (evaluation ℕᵒᵖ AddCommGrpCat.{u + 1}).obj (op e)

/-- `M(n)_e` is the group of sections over `(X, T(n)_e, δ(n))`. -/
theorem levelCosimplicialSections_obj (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (G : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (e n : ℕ) :
    (levelCosimplicialSections T G e).obj ⦋n⦌ = G.obj (op ((T.obj (op ⦋n⦌)).obj e)) :=
  rfl

/-- If at a fixed `p`-adic level `e` the cosimplicial group `M(•)_e` of sections of `G` is
isomorphic to the underlying cosimplicial group of `L_* ⊗_{D(*)} Ω^i_{D(*)}` for some cosimplicial
`D(*)`-module `L_*` and some `i > 0`, then the Moore complex

`M(0)_e → M(1)_e → M(2)_e → ⋯`

is acyclic. -/
theorem isZero_homology_levelCosimplicialSections_of_iso
    (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (G : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (e : ℕ)
    (L : _root_.Crystalline.CosimplicialModule (wholeSpaceEnvelopeRing hp)) {i : ℕ} (hi : 0 < i)
    (ε : levelCosimplicialSections T G e ≅
      (_root_.Crystalline.cosimplicialModuleForget (wholeSpaceEnvelopeRing hp)).obj
          (L ⊗ (_root_.Crystalline.exteriorPowerFunctor (wholeSpaceEnvelopeRing hp) i).functor.obj
            (wholeSpaceEnvelopeDifferentials hp)) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}) (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
      (levelCosimplicialSections T G e)).homology j) :=
  _root_.Crystalline.isZero_homology_alternatingCofaceMapComplex_of_iso ε j
    (isZero_homology_alternatingCofaceMapComplex_tensor_wholeSpaceForms hp L hi j)

end Presentation

/-! ### [Stacks, Tag 07LF] from one isomorphism -/

section Affine

variable [IsAffine S.X] [IsAffine S.S.scheme]

/-- The conclusion

`H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`  for `i > 0` and `j ≥ 0`

of [Stacks, Tag 07LF], in the form `Vanishing07LF`, follows from the existence, for every sheaf of
`𝒪_{X/S}`-modules `F` satisfying hypotheses (1) and (2) of [Stacks, Tag 07JN] and every `i > 0`,
of a cosimplicial module `M_*` over the situation's own `D(*)` and an isomorphism of cosimplicial
abelian groups between the cosimplicial module `M(•)` of [Stacks, Tag 07JN] at the coefficient
sheaf and the universe lift of `M_* ⊗̂_{D(*)} Ω^i_{D(*)}`. -/
theorem vanishing07LF_of_cosimplicialSectionsIso
    (hiso : ∀ F : SheafOfModules.{u} (structureSheaf S), IsLocallyQuasiCoherent F →
      CohomologyRestriction.IsSurjectiveComparison F.val → ∀ i : ℕ, 0 < i →
        ∃ M : _root_.Crystalline.CosimplicialModule
            (wholeSpaceEnvelopeRing (isNilpotent_prime_sections_of_isAffine S)),
          Nonempty (cosimplicialSections
              (wholeSpaceSystem S (isNilpotent_prime_sections_of_isAffine S))
              (tensorDifferentialFormsSheaf F i).obj ≅
            (_root_.Crystalline.cosimplicialModuleForget
                  (wholeSpaceEnvelopeRing (isNilpotent_prime_sections_of_isAffine S))).obj
                (wholeSpaceCompletedForms (isNilpotent_prime_sections_of_isAffine S) M i) ⋙
              AddCommGrpCat.uliftFunctor.{u + 1, u})) :
    Vanishing07LF S := by
  refine vanishing07LF_of_isZero_homology_sectionsComplex' fun F hF hM i hi j ↦ ?_
  obtain ⟨M, ⟨e⟩⟩ := hiso F hF hM i hi
  exact _root_.Crystalline.isZero_homology_alternatingCofaceMapComplex_of_iso e j
    (isZero_homology_alternatingCofaceMapComplex_wholeSpaceCompletedForms
      (isNilpotent_prime_sections_of_isAffine S) M hi j)

end Affine

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
