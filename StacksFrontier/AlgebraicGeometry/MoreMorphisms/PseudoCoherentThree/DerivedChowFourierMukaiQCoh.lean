module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowLemmaGeneral
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreTensorInstance
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh

/-!
# The Fourier–Mukai comparison of [Stacks, Tag 0CSK] at a quasi-coherent complex

Let `p : T ⟶ X` and `q : T ⟶ P` be two morphisms out of a scheme `T` and let `iZ : Z ⟶ T` be a
closed subscheme, with `b = iZ ≫ p` an isomorphism over an open `U ⊆ X`, `c = iZ ≫ q` and
`b ⁻¹ᵁ U = c ⁻¹ᵁ V` for an open `V ⊆ P`.  This is the situation of derived Chow's lemma
[Stacks, Tag 0CSJ], where `T = X ×_A ℙⁿ_A` and `p`, `q` are its two projections.  For a complex
`K` of `𝒪_X`-modules with quasi-coherent cohomology and an `E` satisfying clause (5) of
[Stacks, Tag 0CSJ],

`Rq_*(Lp^*K ⊗^𝐋 E)|_V ≅ R(c ∘ (b|_U)⁻¹)_*(K|_U)`,

which is the displayed equation of [Stacks, Tag 0CSK] at the source's own hypothesis
`K ∈ D_QCoh(𝒪_X)`.

`AlgebraicGeometry.chowDatum_derivedPushforward_tensor_restrict_iso`, in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/PseudoCoherentThree/DerivedChowFourierMukai.lean`,
proves the same comparison for an *arbitrary* `K ∈ D(𝒪_X)` — which is more general than the
source — but it reaches that generality by taking two of the source's steps as inputs of its
own: the projection formula of [Stacks, Tag 08EU] at the closed immersion `i : W ⟶ q ⁻¹ᵁ V`, and
clause (5) of [Stacks, Tag 0CSJ] in the restricted form `Lj^*E ≅ Ri_*𝒪_W`.  This file proves
both, at the quasi-coherence condition on `K` that the source states, and assembles the whole of
Tag 0CSK, finite presentation of `U ⟶ V` included, at the setting of [Stacks, Tag 0CSJ].

## Main results

* `AlgebraicGeometry.DerivedChow.pushforwardUnitRestrictIso`: clause (5) of [Stacks, Tag 0CSJ] in
  the form the Fourier–Mukai computation uses it.  For `iZ : Z ⟶ T` affine and `O ⊆ T` open, the
  restriction of `(iZ)_*𝒪_Z` to `O` is the derived direct image of `𝒪` of the part of `Z` over
  `O`: `Lj^*((iZ)_*𝒪_Z[0]) ≅ R(iZ ∣_ O)_*(𝒪_{iZ⁻¹O}[0])`.
* `AlgebraicGeometry.derivedProjectionFormulaUnitRightIso`: [Stacks, Tag 08EU] at the structure
  sheaf of the source, written with the direct image on the right of the tensor product:
  `M ⊗^𝐋 Ri_*𝒪_A ≅ Ri_*(Li^*M)` for `i : A ⟶ B` quasi-compact and quasi-separated and
  `M ∈ D_QCoh(𝒪_B)`.
* `AlgebraicGeometry.chowDatum_derivedPushforward_tensor_restrict_iso_of_isDQCoh`:
  **the comparison of [Stacks, Tag 0CSK]** at `K ∈ D_QCoh(𝒪_X)`, standing at the derived Chow
  datum of [Stacks, Tag 0CSJ] and nothing else.
* `AlgebraicGeometry.finitePresentation_chowDatumMorphism_of_locallyOfFinitePresentation`: the
  morphism `U ⟶ V` is of finite presentation when `X ⟶ S` is locally of finite presentation and
  `P ⟶ S` is locally of finite type, with no quasi-compactness asked of `U` or `V`.
* `AlgebraicGeometry.chowDatum_fourierMukai`: **[Stacks, Tag 0CSK]** in full, at the setting of
  [Stacks, Tag 0CSJ] — `X ×_A ℙᵐ_A` and its two projections — that `U ⟶ V` is a finitely
  presented closed immersion and that the comparison holds for every `K ∈ D_QCoh(𝒪_X)`.

## Implementation notes

*Where the two inputs come from.*  The projection formula is
`Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh`, which is
[Stacks, Tag 08EU] at exactly the source's hypotheses — a quasi-compact and quasi-separated
morphism of schemes and quasi-coherent cohomology on both sides — and in particular is not
restricted to the structure sheaf.  Turning its `Rf_*E ⊗^𝐋 K ⟶ Rf_*(E ⊗^𝐋 Lf^*K)` into the
orientation `M ⊗^𝐋 Ri_*𝒪_A ≅ Ri_*(Li^*M)` that `Lp^*K ⊗^𝐋 E` forces uses the commutativity and
left unit constraints of [Stacks, Tag 0FPT],
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso` and
`Stacks.RingedSpace.derivedTensorLeftUnitIso`.  Quasi-coherence of the two tensor factors is
`AlgebraicGeometry.isQuasicoherent_homology_singleFunctor_obj` for `𝒪_A[0]` and
[Stacks, Tag 08DW] part (1),
`Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel`, for `Lj^*Lp^*K`; the latter
is used at a free model binder because the derived categories here are the standard ones.

*Clause (5).*  [Stacks, Tag 0CSJ] produces `E` with `Lj^*E ≅ Lj^*((iZ)_*𝒪_Z[0])`, and that is
the hypothesis taken below.  Descending it to `Ri_*𝒪_W` is three steps, all of them in the library:
`AlgebraicGeometry.derivedPushforwardSingleIsoOfIsAffineHom` identifies `(iZ)_*𝒪_Z[0]` with
`R(iZ)_*(𝒪_Z[0])`, `AlgebraicGeometry.DerivedChow.derivedPushforwardRestrictOpenIso` is
[Stacks, Tag 08FE] at the open `O`, and
`Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso` is the unit comparison
`Lk^*(𝒪_Z[0]) ≅ 𝒪_W[0]`, which holds for an arbitrary morphism of ringed spaces.  The same three
steps, composed in the other direction, already appear inside
`AlgebraicGeometry.hasDerivedChowDatum_of_isPullback`.

*The model of the derived categories.*  `HasDerivedCategory.standard` is seated at a raised
priority, as in `DerivedChowFourierMukai` and `DerivedChowLemma`: the import closure carries the
locally small model as a global instance, and the coherences this file composes are baked at the
standard one.

## References

* [Stacks Project, Tag 0CSK](https://stacks.math.columbia.edu/tag/0CSK)
* [Stacks Project, Tag 0CSJ](https://stacks.math.columbia.edu/tag/0CSJ)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

open DerivedChow

/-! ### Clause (5) of [Stacks, Tag 0CSJ] in its restricted form -/

namespace DerivedChow

/-- **The restriction of `(iZ)_*𝒪_Z` to an open of the target.**  For an affine morphism
`iZ : Z ⟶ T` and an open `O ⊆ T`, writing `j : O ⟶ T` for the inclusion and
`i = iZ ∣_ O : iZ⁻¹O ⟶ O`,

`Lj^*((iZ)_*𝒪_Z[0]) ≅ Ri_*(𝒪_{iZ⁻¹O}[0])`.

Direct image along an affine morphism computes the derived direct image of a quasi-coherent
module (`AlgebraicGeometry.derivedPushforwardSingleIsoOfIsAffineHom`), the derived direct image
localizes on the target ([Stacks, Tag 08FE], here
`AlgebraicGeometry.DerivedChow.derivedPushforwardRestrictOpenIso`), and the derived pullback of
the structure sheaf is the structure sheaf
(`Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso`). -/
def pushforwardUnitRestrictIso {T Z : Scheme.{u}} (iZ : Z ⟶ T) [IsAffineHom iZ] (O : T.Opens) :
    (derivedPullback (ofScheme O.ι)).obj
        ((DerivedCategory.singleFunctor T.Modules 0).obj
          ((Scheme.Modules.pushforward iZ).obj (SheafOfModules.unit Z.ringCatSheaf))) ≅
      (derivedPushforward (ofScheme (iZ ∣_ O))).obj
        (structureSheafSingle (iZ ⁻¹ᵁ O).toScheme) :=
  (derivedPullback (ofScheme O.ι)).mapIso
      (derivedPushforwardSingleIsoOfIsAffineHom iZ (SheafOfModules.unit Z.ringCatSheaf)).symm ≪≫
    (derivedPushforwardRestrictOpenIso iZ O).app _ ≪≫
    (derivedPushforward (ofScheme (iZ ∣_ O))).mapIso
      (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso (ofScheme (iZ ⁻¹ᵁ O).ι))

end DerivedChow

/-! ### [Stacks, Tag 08EU] at the structure sheaf, with the direct image on the right -/

/-- **[Stacks, Tag 08EU] at the structure sheaf of the source, with the direct image on the
right of the tensor product.**  For a quasi-compact and quasi-separated morphism of schemes
`i : A ⟶ B` and a complex `M` of `𝒪_B`-modules with quasi-coherent cohomology,

`M ⊗^𝐋_{𝒪_B} Ri_*(𝒪_A[0]) ≅ Ri_*(Li^*M)`.

The projection-formula map of [Stacks, Tag 0B53] is invertible here by
`Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh`: its source
complex is `𝒪_A[0]`, whose cohomology is quasi-coherent, and its target complex is `M`.  That
map has the direct image on the *left*, so the two factors are exchanged by the commutativity
constraint of [Stacks, Tag 0FPT]; the surviving `𝒪_A[0] ⊗^𝐋 Li^*M` on the right is cancelled by
the left unit constraint of the same tag. -/
def derivedProjectionFormulaUnitRightIso {A B : Scheme.{u}} (i : A ⟶ B) [QuasiCompact i]
    [QuasiSeparated i] (M : DerivedCategory B.Modules)
    (hM : ∀ n : ℤ, ((DerivedCategory.homologyFunctor B.Modules n).obj M).IsQuasicoherent) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor B.sheaf).obj M).obj
        ((derivedPushforward (ofScheme i)).obj (structureSheafSingle A)) ≅
      (derivedPushforward (ofScheme i)).obj ((derivedPullback (ofScheme i)).obj M) :=
  have hu : ∀ n : ℤ, ((DerivedCategory.homologyFunctor A.Modules n).obj
      (structureSheafSingle A)).IsQuasicoherent :=
    fun n => isQuasicoherent_homology_singleFunctor_obj A _ inferInstance n
  have hiso :=
    Stacks.Cohomology.ProjectionFormulaQCoh.projectionFormulaMap_isIso_of_isQuasicoherent_homology
      i inferInstance inferInstance (structureSheafSingle A) M hu hM
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct B.sheaf).braidingIso
      (Stacks.RingedSpace.toRingedSite B.toRingedSpace) M
      ((derivedPushforward (ofScheme i)).obj (structureSheafSingle A)) ≪≫
    @asIso _ _ _ _ _ hiso ≪≫
    (derivedPushforward (ofScheme i)).mapIso
      (Stacks.RingedSpace.derivedTensorLeftUnitIso A.toRingedSpace
        ((derivedPullback (ofScheme i)).obj M))

/-! ### The comparison of [Stacks, Tag 0CSK] -/

/-- **[Stacks, Tag 0CSK], the derived comparison, at a quasi-coherent complex.**  In the
situation of derived Chow's lemma — `p : T ⟶ X` and `q : T ⟶ P` the two projections of
`T = X ×_A ℙⁿ_A`, `iZ : Z ⟶ T` the closed subscheme, `b = iZ ≫ p` an isomorphism over the open
`U ⊆ X`, `c = iZ ≫ q`, and `b ⁻¹ᵁ U = c ⁻¹ᵁ V` for an open `V ⊆ P` — let `E` satisfy clause (5)
of [Stacks, Tag 0CSJ], that its restriction to `q ⁻¹ᵁ V` agrees with that of `(iZ)_*𝒪_Z`.  Then
for every `K ∈ D_QCoh(𝒪_X)`

`Rq_*(Lp^*K ⊗^𝐋 E)|_V ≅ R(c ∘ (b|_U)⁻¹)_*(K|_U)`.

This statement stands at the data of [Stacks, Tag 0CSJ] and nothing else: `hb`, `hW` and `hE`
are clauses (2), (4) and (5) of that lemma, in the shape
`AlgebraicGeometry.exists_derivedChowDatum` produces them, and `hK` is the quasi-coherence
condition on `K` that [Stacks, Tag 0CSK] states.  The whole of Tag 0CSK, at the projections of
`X ×_A ℙᵐ_A`, is `AlgebraicGeometry.chowDatum_fourierMukai` below.  The proof is
`AlgebraicGeometry.chowDatum_derivedPushforward_tensor_restrict_iso`, whose two inputs are
supplied by `AlgebraicGeometry.DerivedChow.pushforwardUnitRestrictIso` and by
`AlgebraicGeometry.derivedProjectionFormulaUnitRightIso`. -/
@[stacks 0CSK "the derived comparison Rq_*(Lp^*K ⊗ᴸ E)|_V ≅ R(U → V)_*(K|_U) for K in \
D_QCoh(O_X), which is the condition on K that Tag 0CSK itself states. Everything else the \
statement fixes — p, q, iZ, U, V, E and the three conditions hb, hW, hE on them — is the datum \
of Lemma 0CSJ, hE being clause (5) of that lemma in the very shape exists_derivedChowDatum \
produces it. Nothing further enters: the projection formula of Tag 08EU and clause (5) in the \
restricted form the computation reads it in are both proved here, as \
derivedProjectionFormulaUnitRightIso and DerivedChow.pushforwardUnitRestrictIso. The whole \
statement, with the two geometric assertions that U ⟶ V is a closed immersion and is of finite \
presentation, is chowDatum_fourierMukai"]
theorem chowDatum_derivedPushforward_tensor_restrict_iso_of_isDQCoh
    {X P T Z : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ P) (iZ : Z ⟶ T) [IsClosedImmersion iZ]
    (U : X.Opens) (V : P.Opens) (hb : IsIso ((iZ ≫ p) ∣_ U))
    (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V)
    (E : DerivedCategory T.Modules)
    (hE : (derivedPullback (ofScheme (q ⁻¹ᵁ V).ι)).obj E ≅
      (derivedPullback (ofScheme (q ⁻¹ᵁ V).ι)).obj
        ((DerivedCategory.singleFunctor T.Modules 0).obj
          ((Scheme.Modules.pushforward iZ).obj (SheafOfModules.unit Z.ringCatSheaf))))
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    Nonempty ((derivedPullback (ofScheme V.ι)).obj ((derivedPushforward (ofScheme q)).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor T.sheaf).obj
          ((derivedPullback (ofScheme p)).obj K)).obj E)) ≅
      (derivedPushforward (ofScheme (chowDatumMorphism p q iZ U V hb hW))).obj
        ((derivedPullback (ofScheme U.ι)).obj K)) := by
  have hp := Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel p K hK
  exact chowDatum_derivedPushforward_tensor_restrict_iso p q iZ U V hb hW E K
    (hE ≪≫ DerivedChow.pushforwardUnitRestrictIso iZ (q ⁻¹ᵁ V))
    (derivedProjectionFormulaUnitRightIso (iZ ∣_ (q ⁻¹ᵁ V)) _
      (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel (q ⁻¹ᵁ V).ι _ hp))

/-! ### The finitely presented closed immersion `U ⟶ V`, at the hypotheses of the source -/

section Morphism

variable {X P T Z : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ P) (iZ : Z ⟶ T) (U : X.Opens) (V : P.Opens)

/-- **`U ⟶ V` is a morphism over the base.**  If `p ≫ f = q ≫ g`, then the morphism
`c ∘ (b|_U)⁻¹ : U ⟶ V` followed by `V ⟶ P ⟶ S` is `U ⟶ X ⟶ S`: precomposed with the
isomorphism `W ≅ U`, both sides are the composite `W ⟶ T ⟶ S`. -/
theorem chowDatumMorphism_comp_ι_comp {S : Scheme.{u}} (f : X ⟶ S) (g : P ⟶ S)
    (hpq : p ≫ f = q ≫ g) (hb : IsIso ((iZ ≫ p) ∣_ U))
    (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V) :
    chowDatumMorphism p q iZ U V hb hW ≫ V.ι ≫ g = U.ι ≫ f := by
  have hiso := isIso_chowDatumGraphIso p q iZ U V hb hW
  have h1 : chowDatumGraphIso p q iZ U V hW ≫ chowDatumMorphism p q iZ U V hb hW ≫ V.ι ≫ g =
      chowDatumGraphIso p q iZ U V hW ≫ U.ι ≫ f := by
    rw [← Category.assoc _ _ (V.ι ≫ g), chowDatumGraphIso_comp_chowDatumMorphism,
      ← Category.assoc _ _ f, chowDatumGraphIso_comp_ι]
    simp only [Category.assoc]
    rw [morphismRestrict_ι_assoc, hpq]
  exact (cancel_epi (chowDatumGraphIso p q iZ U V hW)).mp h1

/-- **The morphism `U ⟶ V` of [Stacks, Tag 0CSK] is of finite presentation**, as soon as
`X ⟶ S` is locally of finite presentation and `P ⟶ S` is locally of finite type.  It is a closed
immersion (`AlgebraicGeometry.isClosedImmersion_chowDatumMorphism`), hence quasi-compact and
quasi-separated; and it is locally of finite presentation by [Stacks, Tag 02FV] part (1) applied
to `U ⟶ V ⟶ S`, the composite being `U ⟶ X ⟶ S`
(`AlgebraicGeometry.chowDatumMorphism_comp_ι_comp`), which is locally of finite presentation
because `U ⟶ X` is an open immersion.

No quasi-compactness of `U` or `V` is asked for: the source's "`U` and `V` are of finite
presentation over `A`" is used only through local finite presentation, the two global conditions
coming from the closed immersion itself. -/
theorem finitePresentation_chowDatumMorphism_of_locallyOfFinitePresentation {S : Scheme.{u}}
    (f : X ⟶ S) (g : P ⟶ S) [LocallyOfFinitePresentation f] [LocallyOfFiniteType g]
    (hpq : p ≫ f = q ≫ g) (hb : IsIso ((iZ ≫ p) ∣_ U))
    (hc : IsClosedImmersion ((iZ ≫ q) ∣_ V))
    (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V) :
    AlgebraicGeometry.FinitePresentation (chowDatumMorphism p q iZ U V hb hW) := by
  have := isClosedImmersion_chowDatumMorphism p q iZ U V hb hc hW
  have : LocallyOfFinitePresentation (chowDatumMorphism p q iZ U V hb hW ≫ V.ι ≫ g) := by
    rw [chowDatumMorphism_comp_ι_comp p q iZ U V f g hpq hb hW]
    infer_instance
  exact ⟨locallyOfFinitePresentation_of_comp _ (V.ι ≫ g), inferInstance, inferInstance⟩

end Morphism

/-! ### [Stacks, Tag 0CSK] -/

/-- **[Stacks, Tag 0CSK].**  Let `A` be a ring, let `f : X ⟶ Spec A` be locally of finite
presentation (in the source, `X` is separated and of finite presentation over `A`), let
`p : X ×_A ℙᵐ_A ⟶ X` and `q : X ×_A ℙᵐ_A ⟶ ℙᵐ_A` be the two projections, and let
`U ⊆ X`, `V ⊆ ℙᵐ_A`, `iZ : Z ⟶ X ×_A ℙᵐ_A` and `E ∈ D(𝒪_{X ×_A ℙᵐ_A})` be as in
[Stacks, Tag 0CSJ]: `iZ` is a closed immersion, `b = iZ ≫ p` is an isomorphism over `U`,
`c = iZ ≫ q` is a closed immersion over `V`, `b ⁻¹ᵁ U = c ⁻¹ᵁ V`, and the restriction of `E` to
`X ×_A V` is that of `(b, c)_*𝒪_Z` — each in the very shape
`AlgebraicGeometry.exists_derivedChowDatum` produces it.  Then the morphism
`c ∘ (b|_U)⁻¹ : U ⟶ V` is a closed immersion of finite presentation, and for every
`K ∈ D_QCoh(𝒪_X)`

`Rq_*(Lp^*K ⊗^𝐋 E)|_V ≅ R(c ∘ (b|_U)⁻¹)_*(K|_U)`.

The clauses of [Stacks, Tag 0CSJ] not listed — finite presentation of `iZ`, the point `z`,
separatedness and quasi-compactness of `X`, pseudo-coherence and support of `E` — are not used,
so the statement is given without them. -/
@[stacks 0CSK]
theorem chowDatum_fourierMukai {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation f] (m : ℕ) (U : X.Opens)
    (V : (projectiveSpaceOver m (Spec (.of A))).Opens) {Z : Scheme.{u}}
    (iZ : Z ⟶ pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A)))
    [IsClosedImmersion iZ]
    (hb : IsIso ((iZ ≫ pullback.fst f
      (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ∣_ U))
    (hc : IsClosedImmersion ((iZ ≫ pullback.snd f
      (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ∣_ V))
    (hW : (iZ ≫ pullback.fst f
        (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ⁻¹ᵁ U =
      (iZ ≫ pullback.snd f
        (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ⁻¹ᵁ V)
    (E : DerivedCategory
      (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).Modules)
    (hE : Nonempty ((derivedPullback (ofScheme (pullback.snd f
        (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A)) ⁻¹ᵁ V).ι)).obj E ≅
      (derivedPullback (ofScheme (pullback.snd f
        (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A)) ⁻¹ᵁ V).ι)).obj
        ((DerivedCategory.singleFunctor
          (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).Modules 0).obj
          ((Scheme.Modules.pushforward iZ).obj (SheafOfModules.unit Z.ringCatSheaf))))) :
    IsClosedImmersion (chowDatumMorphism (pullback.fst f _) (pullback.snd f _) iZ U V hb hW) ∧
      AlgebraicGeometry.FinitePresentation
        (chowDatumMorphism (pullback.fst f _) (pullback.snd f _) iZ U V hb hW) ∧
      ∀ K : DerivedCategory X.Modules,
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) →
        Nonempty ((derivedPullback (ofScheme V.ι)).obj
            ((derivedPushforward (ofScheme (pullback.snd f
              (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))))).obj
              (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
                  (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).sheaf).obj
                ((derivedPullback (ofScheme (pullback.fst f
                  (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))))).obj K)).obj E)) ≅
          (derivedPushforward (ofScheme
            (chowDatumMorphism (pullback.fst f _) (pullback.snd f _) iZ U V hb hW))).obj
            ((derivedPullback (ofScheme U.ι)).obj K)) := by
  obtain ⟨e⟩ := hE
  exact ⟨isClosedImmersion_chowDatumMorphism _ _ iZ U V hb hc hW,
    finitePresentation_chowDatumMorphism_of_locallyOfFinitePresentation _ _ iZ U V f
      (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A)) pullback.condition hb hc hW,
    fun K hK => chowDatum_derivedPushforward_tensor_restrict_iso_of_isDQCoh _ _ iZ U V hb hW E e
      K hK⟩

end AlgebraicGeometry

end
