module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusHomReduction
public import StacksFrontier.AlgebraicGeometry.Quot.AffineFinitePresentationGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreDualVanishing
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine

/-!
# Stacks 0DLC, part (3), in the case `W = Y`

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces, `K` a
pseudo-coherent and `E` a `Y`-perfect object of `D(𝒪_X)`, and assume that the negative fibre
extensions `Ext^i(K_y, E_y)`, `i < 0`, vanish at every point `y` of `Y` with values in a field.
Stacks 0DLC, part (3), in this case says that the functor `F : V ↦ Hom_{𝒪_{X_V}}(K_V, E_V)` is an
algebraic space affine and of finite presentation over `Y`.  The source argues in three steps:

* **(S)** by part (2), `Ext^i(K_V, E_V) = 0` for `i < 0` and every `V` over `Y`, so Stacks 0DL9
  (applied to the Čech hypercovering of an fppf covering) makes `F` an fppf sheaf over `Y`;
* **(G)** being an algebraic space affine and of finite presentation over `Y` is then étale local
  on `Y` (Stacks 04U0, 03WG, 0410), so one may assume `Y` affine;
* **(L)** over an affine `Y`, Stacks 0DKY gives a pseudo-coherent `L` on `Y` with
  `F(V) = Hom(L_V, 𝒪_V)` naturally in `V`; the fibre condition gives `H^i(L) = 0` for `i > 0`
  (`AlgebraicGeometry.Space.fieldFibreDualVanishingIsLE`), so `L` is represented by a complex
  `⋯ → 𝒪^{m₁} → 𝒪^{m₀} → 0` (Stacks 064U), and `F` is the fibre product of the zero section
  `Y ⟶ 𝐀^{m₁}_Y` with a linear map `𝐀^{m₀}_Y ⟶ 𝐀^{m₁}_Y`.

This file states the external inputs as explicit hypotheses (Stacks 0DL9 and Stacks 0DKY, both
not yet proved here), names the internal steps (S) and (L), which are proved in
`StacksFrontier/AlgebraicGeometry/Quot/RelativeDerivedHomSheafDescentProof.lean` and
`StacksFrontier/AlgebraicGeometry/Quot/RelHomStructureRepresentable.lean`, and proves the
assembly: the case `W = Y` of part (3) from part (2), the two external inputs and those two steps.
Step (G) is `AlgebraicGeometry.Space.affineFinitePresentationOfAffineTestSchemes`
(`StacksFrontier/AlgebraicGeometry/Quot/AffineFinitePresentationGluing.lean`); the step from the
fibre condition to `H^i(L) = 0` for `i > 0` and the reduction from `Y` to its affine test schemes
are carried out here.  Nothing is registered.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDerivedHomDualExistsNaturalCompatible`: the content of Stacks
  0DKY, with the objectwise base change isomorphisms and their naturality in degree zero for one
  and the same `L`.
* `AlgebraicGeometry.Space.augmentationCone`, `fppfCoveringMorphisms` and
  `DerivedHomHypercoveringDescent`: the content of Stacks 0DL9.
* `AlgebraicGeometry.Space.RelativeDerivedHomIsSheafOfDescent` and
  `RelHomStructureRepresentableOfIsLE`: the internal steps (S) and (L) of the proof, proved by
  `AlgebraicGeometry.Space.relativeDerivedHomIsSheafOfDescent` and
  `AlgebraicGeometry.Space.relHomStructureRepresentableOfIsLE`.

## Main results

* `AlgebraicGeometry.Space.hasNoNegativeExtAt_overInclusion_iff`: the negative fibre extensions of
  the restrictions `K_V`, `E_V` to a base change `X_V ⟶ V` at a point of `V` are those of `K`, `E`
  at the same point regarded as a point of `Y`.
* `AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_steps`: **Stacks 0DLC,
  part (3), in the case `W = Y`**, from part (2) at `W = Y`, Stacks 0DKY, Stacks 0DL9 and the
  internal steps (S) and (L).

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 0DL9](https://stacks.math.columbia.edu/tag/0DL9)
* [Stacks Project, Tag 04U0](https://stacks.math.columbia.edu/tag/04U0)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 0410](https://stacks.math.columbia.edu/tag/0410)
* [Stacks Project, Tag 064U](https://stacks.math.columbia.edu/tag/064U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Stacks 0DKY, with one `L` for both of its forms -/

variable (B S hS) in
/-- **The content of Stacks 0DKY** (Stacks 0DKY, not yet proved here), as a proposition, with
both of the forms the proof of Stacks 0DLC consumes holding for one and the same `L`: for a
morphism `f : X ⟶ Y` of algebraic spaces with `Y` quasi-compact and quasi-separated and `f`
proper, flat and of finite presentation, a `Y`-perfect `E` and a pseudo-coherent `K` in
`D(𝒪_X)`, there is a pseudo-coherent `L` in `D(𝒪_Y)` such that

* `Rf'_* R𝓗om(L(g')^*K, L(g')^*E) ≅ R𝓗om(Lg^*L, 𝒪_{Y'})` after every cartesian base change
  `X' = X ×_Y Y'`, as in `AlgebraicGeometry.Space.RelativeDerivedHomDualExists`; and
* the functor `T ↦ Hom(K_T, E_T)` on the test schemes over `Y` is the functor
  `T ↦ Hom(L_T, 𝒪_T)`, naturally in `T`, as in
  `AlgebraicGeometry.Space.RelativeDerivedHomDualExistsNatural`.

The `L` of the source satisfies both: the second is the first in degree zero, read through
Stacks 08JA and 0D6H, together with the compatibility of the isomorphisms of Stacks 0DKY with
further base change.  Each of the two named propositions alone leaves `L` independent of the
other, which does not suffice: part (3) of Stacks 0DLC needs the natural form at an `L` of which
the objectwise form shows `H^i(L) = 0` for `i > 0`. -/
def RelativeDerivedHomDualExistsNaturalCompatible : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    IsQuasiCompactSpace B S hS Y.1 → IsAbsolutelyQuasiSeparated B S hS hZ Y.1 →
    IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (K E : derivedModules B S hS X),
      IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
      ∃ L : derivedModules B S hS Y, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L ∧
        (∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
          IsPullback g' f' f g →
          Nonempty ((spaceDerivedPushforward B S hS f').obj
              (((smallEtaleDerivedSheafHom B S hS X').obj
                (Opposite.op (((smallEtaleDerivedPullbackData B S hS).pull g').obj K))).obj
                  (((smallEtaleDerivedPullbackData B S hS).pull g').obj E)) ≅
            smallEtaleDerivedDual B S hS Y'
              (((smallEtaleDerivedPullbackData B S hS).pull g).obj L))) ∧
        Nonempty (relativeDerivedHom f K E ≅
          (smallEtaleDerivedPullbackData B S hS).relHomFunctor
            (smallEtaleDerivedPullbackData_isCoherent B S hS) (schemesOverCone Y) L
            (structureObject B S hS Y))

/-- The objectwise form of Stacks 0DKY follows from the compatible form. -/
theorem RelativeDerivedHomDualExistsNaturalCompatible.relativeDerivedHomDualExists
    (h : RelativeDerivedHomDualExistsNaturalCompatible B S hS) :
    RelativeDerivedHomDualExists B S hS := by
  intro hZ X Y f hqc hqs hp hflat hfp K E hE hK
  obtain ⟨L, hL, hbc, -⟩ := h hZ f hqc hqs hp hflat hfp K E hE hK
  refine ⟨L, hL, ?_, fun g' f' g hpb => hbc g' f' g hpb⟩
  obtain ⟨e⟩ := hbc (𝟙 X) f (𝟙 Y) (IsPullback.of_horiz_isIso ⟨by simp⟩)
  let P := smallEtaleDerivedPullbackData B S hS
  exact ⟨(spaceDerivedPushforward B S hS f).mapIso
      (((smallEtaleDerivedSheafHom B S hS X).mapIso ((P.idIso X).app K).op).app E ≪≫
        ((smallEtaleDerivedSheafHom B S hS X).obj (Opposite.op ((P.pull (𝟙 X)).obj K))).mapIso
          ((P.idIso X).app E).symm) ≪≫ e ≪≫
    (((smallEtaleDerivedSheafHom B S hS Y).mapIso ((P.idIso Y).app L).op).app _).symm⟩

/-- The natural form of Stacks 0DKY follows from the compatible form. -/
theorem RelativeDerivedHomDualExistsNaturalCompatible.relativeDerivedHomDualExistsNatural
    (h : RelativeDerivedHomDualExistsNaturalCompatible B S hS) :
    RelativeDerivedHomDualExistsNatural B S hS := by
  intro hZ X Y f hqc hqs hp hflat hfp K E hE hK
  obtain ⟨L, hL, -, hnat⟩ := h hZ f hqc hqs hp hflat hfp K E hE hK
  exact ⟨L, hL, hnat⟩

/-! ### Stacks 0DL9 -/

/-- The augmentation of an augmented simplicial algebraic space `U_• ⟶ X`, as a cone from the
simplicial object to `X`: its legs are the morphisms `a_n : U_n ⟶ X`. -/
def augmentationCone (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)) :
    PullbackData.ConeTo A.left A.right where
  leg n := A.hom.app n
  w g := by simp

variable (B S hS) in
/-- The morphisms of algebraic spaces which are fppf coverings on their own: flat, locally of
finite presentation and surjective (Stacks 03Y8 for a one-member family). -/
def fppfCoveringMorphisms : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun X _ f => IsFppfCovering B S hS (fun _ : Unit => X.1) (fun _ => f.hom)

variable (B S hS) in
/-- **The content of Stacks 0DL9** (Stacks 0DL9, not yet proved here), as a proposition: let
`a : U_• ⟶ X` be an fppf hypercovering of an algebraic space `X` and let `K`, `E` be
pseudo-coherent objects of `D(𝒪_X)` with `Ext^i(La_n^*K, La_n^*E) = 0` for all `n ≥ 0` and
`i < 0`.  Then

1. `Ext^i(K, E) = 0` for `i < 0`, and
2. the sequence `0 → Hom(K, E) → Hom(La_0^*K, La_0^*E) ⇉ Hom(La_1^*K, La_1^*E)` is exact: a
   morphism `La_0^*K ⟶ La_0^*E` whose two restrictions along the faces `U_1 ⟶ U_0` agree is the
   pullback of exactly one morphism `K ⟶ E`.

The restrictions along the faces are those of the relative Hom functor of the augmentation
cone, `CategoryTheory.PullbackData.relHomMap`, which reads them through the canonical comparison
`La_1^* ≅ Lδ^* La_0^*` of Stacks 0D6D.  The source states the lemma for `K`, `E` in
`D_QCoh(𝒪_X)`; this is the case of pseudo-coherent `K`, `E`, which lie in `D_QCoh(𝒪_X)`, and is
the case the proof of Stacks 0DLC uses (there `K` is pseudo-coherent and `E` is `Y`-perfect,
hence pseudo-coherent). -/
def DerivedHomHypercoveringDescent : Prop :=
  ∀ (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)),
    (fppfCoveringMorphisms B S hS).IsHypercovering A →
    ∀ K E : derivedModules B S hS A.right,
      (smallEtaleRingedSite B S hS A.right.1 A.right.2).IsPseudoCoherent K →
      (smallEtaleRingedSite B S hS A.right.1 A.right.2).IsPseudoCoherent E →
      (∀ (n : ℕ) (i : ℤ), i < 0 →
        Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull
            (A.hom.app (Opposite.op (SimplexCategory.mk n)))).obj K ⟶
          (((smallEtaleDerivedPullbackData B S hS).pull
            (A.hom.app (Opposite.op (SimplexCategory.mk n)))).obj E)⟦i⟧)) →
      (∀ i : ℤ, i < 0 → Subsingleton (K ⟶ E⟦i⟧)) ∧
      ∀ φ : (smallEtaleDerivedPullbackData B S hS).relHomObj (augmentationCone A) K E
          (Opposite.op (SimplexCategory.mk 0)),
        ((smallEtaleDerivedPullbackData B S hS).relHomMap (augmentationCone A) K E
            (SimplexCategory.δ (0 : Fin 2)).op φ =
          (smallEtaleDerivedPullbackData B S hS).relHomMap (augmentationCone A) K E
            (SimplexCategory.δ (1 : Fin 2)).op φ) ↔
        ∃! g : K ⟶ E, ((smallEtaleDerivedPullbackData B S hS).pull
          (A.hom.app (Opposite.op (SimplexCategory.mk 0)))).map g = φ

/-! ### The internal steps (S) and (L) -/

variable (B S hS) in
/-- **Step (S) of the proof of Stacks 0DLC, part (3)** (internal; proved by
`AlgebraicGeometry.Space.relativeDerivedHomIsSheafOfDescent`
in `StacksFrontier/AlgebraicGeometry/Quot/RelativeDerivedHomSheafDescentProof.lean`): granted Stacks
0DL9, for a morphism `f : X ⟶ Y` of algebraic spaces and pseudo-coherent `K`, `E` in `D(𝒪_X)`
with `Ext^i(K_V, E_V) = 0` for `i < 0` and every algebraic space `V` over `Y`, the functor
`T ↦ Hom(K_T, E_T)` on the test schemes over `Y` is an fppf sheaf over `Y`.

For a covering `{T_i ⟶ T}` the source applies Stacks 0DL9 to the Čech hypercovering
`X_{T_•} ⟶ X_T` of the base change of `f` to `T`. -/
def RelativeDerivedHomIsSheafOfDescent : Prop :=
  DerivedHomHypercoveringDescent B S hS →
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (K E : derivedModules B S hS X),
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E →
    (∀ (V : Over Y) (i : ℤ), i < 0 →
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦i⟧)) →
    IsFppfSheafOver (relativeDerivedHom f K E)

variable (B S hS) in
/-- **Step (L) of the proof of Stacks 0DLC, part (3)** (internal; proved by
`AlgebraicGeometry.Space.relHomStructureRepresentableOfIsLE`
in `StacksFrontier/AlgebraicGeometry/Quot/RelHomStructureRepresentable.lean`): over an affine
scheme `V`, for a pseudo-coherent `L` in `D(𝒪_V)` with `H^i(L) = 0` for `i > 0`, the functor
`T ↦ Hom(L_T, 𝒪_T)` on the test schemes over `V` is an algebraic space affine and of finite
presentation over `V`.  In the source: `L` is a complex `⋯ → 𝒪^{m₁} → 𝒪^{m₀} → 0` (Stacks
064U), so the functor is `T ↦ Ker(Γ(T, 𝒪_T)^{m₀} → Γ(T, 𝒪_T)^{m₁})`, the fibre product of a
linear map `𝐀^{m₀}_V ⟶ 𝐀^{m₁}_V` with the zero section. -/
def RelHomStructureRepresentableOfIsLE : Prop :=
  ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
    ∀ L : derivedModules B S hS ((schemeSpaceFunctor B S hS).obj V),
      (smallEtaleRingedSite B S hS _ ((schemeSpaceFunctor B S hS).obj V).2).IsPseudoCoherent L →
      L.IsLE 0 →
      IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj V)
        ((smallEtaleDerivedPullbackData B S hS).relHomFunctor
          (smallEtaleDerivedPullbackData_isCoherent B S hS)
          (schemesOverCone ((schemeSpaceFunctor B S hS).obj V)) L
          (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)))

/-! ### The assembly -/

section Assembly

variable {X Y : AlgebraicSpaces B S hS}

/-- **The fibres of a base change.**  For an algebraic space `V` over `Y` and a test scheme `T₀`
over `V`, the negative extensions of the restrictions `K_V`, `E_V` at `T₀` (for the base change
`X_V ⟶ V`) are those of `K`, `E` at `T₀` regarded as a test scheme over `Y`: the fibre of `X_V`
over `T₀` is the fibre of `X`, by pasting the two cartesian squares. -/
theorem hasNoNegativeExtAt_overInclusion_iff (f : X ⟶ Y) (V : Over Y)
    (K E : derivedModules B S hS X) (T₀ : SchemesOver V.left) :
    HasNoNegativeExtAt (overInclusion f V)
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K)
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E) T₀ ↔
      HasNoNegativeExtAt f K E
        ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).obj T₀) := by
  let fV := overInclusion f V
  let T₁ : SchemesOver Y := (CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).obj T₀
  have hpb : IsPullback (baseChangeProjection fV T₀ ≫ overProjection f V)
      (baseChangeInclusion fV T₀) f T₁.hom :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS fV T₀.hom).paste_horiz
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f V.hom)
  have hT₁ : IsPullback (baseChangeProjection f T₁) (baseChangeInclusion f T₁) f T₁.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f T₁.hom
  refine forall₂_congr fun i _ => ?_
  rw [subsingleton_pull_comp_iff]
  exact (subsingleton_pull_iff_of_iso (hpb.isoIsPullback _ _ hT₁)
    (hpb.isoIsPullback_hom_fst _ _ hT₁) K E i).symm

/-- **Stacks 0DLC, part (3), in the case `W = Y`**, from part (2) in the case `W = Y` (`h2`),
Stacks 0DKY (`h0DKY`), Stacks 0DL9 (`h0DL9`) and the internal steps (S) and (L) (`hS'`, `hL`).

The functor `T ↦ Hom(K_T, E_T)` is an fppf sheaf over `Y` by step (S), as the negative
extensions of `K_V`, `E_V` vanish for every `V` over `Y` by part (2).  By step (G),
`AlgebraicGeometry.Space.affineFinitePresentationOfAffineTestSchemes`, it suffices to
show that its restriction to an affine test scheme `V` over `Y` is an algebraic space affine and
of finite presentation over `V`.  That restriction is the relative derived Hom functor of the
base change `X_V ⟶ V` at `K_V`, `E_V`
(`AlgebraicGeometry.Space.relativeDerivedHomBaseChangeIso`); `V` is quasi-compact and
quasi-separated, so Stacks 0DKY gives a pseudo-coherent `L` on `V` with that functor isomorphic to
`T ↦ Hom(L_T, 𝒪_T)`; the objectwise isomorphisms of Stacks 0DKY turn the fibre condition into the
vanishing of the negative extensions of the fibres of `L` into the structure sheaf
(`AlgebraicGeometry.Space.hasNoNegativeExtAt_iff_of_dual`), so `H^i(L) = 0` for `i > 0`
(`AlgebraicGeometry.Space.fieldFibreDualVanishingIsLE`); and step (L) concludes. -/
theorem relativeDerivedHomRepresentableOfFibres_of_steps
    (h2 : NegativeExtVanishesOfFibres B S hS)
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS)
    (h0DL9 : DerivedHomHypercoveringDescent B S hS)
    (hS' : RelativeDerivedHomIsSheafOfDescent B S hS)
    (hL : RelHomStructureRepresentableOfIsLE B S hS) :
    RelativeDerivedHomRepresentableOfFibres B S hS := by
  intro X Y f hp hflat hfp K E hK hE hfib
  refine affineFinitePresentationOfAffineTestSchemes Y _
    (hS' h0DL9 f K E hK hE.1 (h2 f hp hflat hfp K E hK hE hfib)) fun V hV => ?_
  let V' : Over Y := (schemesOverToOver Y).obj V
  let fV := overInclusion f V'
  let pV := overProjection f V'
  have hsq : IsPullback pV fV f V'.hom := AlgebraicSpaces.isPullback_fiberProduct B S hS f V'.hom
  have hflatV : IsFlat B S hS fV.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hsq hflat
  have hfpV : IsFinitePresentation B S hS fV.hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hsq hfp
  have hrep : yoneda.relativelyRepresentable pV.hom :=
    (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS hsq).flip
      (relativelyRepresentable_of_isAlgebraicSpace B S hS Y.2 V.hom.hom)
  have hKV : (smallEtaleRingedSite B S hS (overBaseChange f V').1
      (overBaseChange f V').2).IsPseudoCoherent
      (((smallEtaleDerivedPullbackData B S hS).pull pV).obj K) :=
    isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable B S hS pV hrep K hK
  have hEV :=
    isPerfectRelativeToCanonical_pull_of_isPullback hsq hrep hflatV hfpV.1 hflat hfp.1 E hE
  obtain ⟨L, hLpc, hbc, ⟨e⟩⟩ := h0DKY B.contains_terminal fV
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS V.left hV)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS B.contains_terminal
      (isAffineSpace_yoneda B S hS V.left hV))
    ((isProper_isStableUnderBaseChange B S hS).of_isPullback hsq hp) hflatV hfpV _ _ hEV hKV
  have hL0 : L.IsLE 0 := fieldFibreDualVanishingIsLE B S hS (testSpace V) L hLpc fun T₀ hT₀ =>
    (hasNoNegativeExtAt_iff_of_dual fV _ _ L T₀
      (hbc _ _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS fV T₀.hom)).some).1
      ((hasNoNegativeExtAt_overInclusion_iff f V' K E T₀).2 (hfib _ hT₀))
  exact (hL V.left hV L hLpc hL0).of_iso (e.symm ≪≫ relativeDerivedHomBaseChangeIso f V' K E)

end Assembly

end AlgebraicGeometry.Space

end
