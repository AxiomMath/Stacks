module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Denominators
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# The generic-point decomposition of the meromorphic sections of a module

Let `X` be a scheme, let `X⁰` be the set of generic points of its irreducible components, and
for `η ∈ X⁰` let `j_η : Spec 𝒪_{X, η} ⟶ X` be the canonical morphism. Part (2) of
[Stacks, Tag 0EMF] asserts that for a quasi-coherent `𝒪_X`-module `F` the sheaf `K_X(F)` of
meromorphic sections of `F` is both the direct sum and the product of the generic-point
contributions `j_{η, *} F_η = j_{η, *} j_η^* F`, and is quasi-coherent, provided every weakly
associated point of `X` is a generic point of an irreducible component and every quasi-compact
open has only finitely many irreducible components.

This file supplies the infrastructure for that statement except the comparison morphism itself:

* the generic-point contribution `j_{η, *} j_η^* F`, read as a sheaf of modules over the sheaf
  of total quotient rings `K_X`, which is what the comparison morphism out of `K_X(F)` lands in;
* local finiteness of the family of contributions, so that its coproduct is its product;
* quasi-coherence of the product, for `F` quasi-coherent.

The comparison morphism `K_X(F) ⟶ ∏_{η ∈ X⁰} j_{η, *} F_η` itself, characterised by the property
that `F ⟶ K_X(F) ⟶ j_{η, *} F_η` is the unit of `j_η^* ⊣ j_{η, *}`, together with the reduction
of its invertibility to the restriction to each affine open and the proof of part (2) in full, is
in `StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Globalization` as
`AlgebraicGeometry.genericPointComparisonPi`. Consequently the direct-sum decomposition and the
quasi-coherence of `K_X(F)` both follow from the product decomposition via the lemmas below. No
`@[stacks]` tag is placed here, because the tagged theorems are the ones in `Globalization`.

## Main definitions

* `AlgebraicGeometry.genericPointStalkKModule`: the generic-point contribution
  `j_{η, *} j_η^* F` read as a sheaf of modules over the sheaf of total quotient rings, which is
  what makes the comparison morphism in `Globalization` exist.

## Main results

* `AlgebraicGeometry.nonempty_sigmaIsoPi_genericPointStalkModuleOf`: the coproduct of the
  generic-point contributions is their product.
* `AlgebraicGeometry.isQuasicoherent_genericPointStalkModuleOf`,
  `AlgebraicGeometry.isQuasicoherent_pi_genericPointStalkModuleOf`: each contribution of a
  quasi-coherent module is quasi-coherent, and so is their product.
* `AlgebraicGeometry.nonempty_meromorphicSections_iso_coproduct_iff_product` and
  `AlgebraicGeometry.meromorphicSections_isQuasicoherent_of_nonempty_iso_product`: the
  direct-sum decomposition and the quasi-coherence of `K_X(F)` follow from the product
  decomposition.

## Implementation notes

`Stacks.AlgebraicGeometry.GenericPointDecomposition.meromorphicSections` is
`AlgebraicGeometry.meromorphicSectionSheafAsModule` with its type ascribed at `X.Modules`, as
`AlgebraicGeometry.meromorphicSections_eq` records. The second name
is needed because products, coproducts and quasi-coherence are taken in `X.Modules`, which is a
plain `def` and therefore carries a syntactically different `Category` instance from the one on
`SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf X.sheaf)` that instance search will not
cross. For the
same reason `specStalkRingCatSheaf` restates `(Spec 𝒪_{X, η}).ringCatSheaf` at the type
`Sheaf (Opens.grothendieckTopology _) RingCat`: `TopCat.Sheaf` is a `def`, so a sheaf of rings
presented through it is not recognised as one over which `SheafOfModules` has a category.

The generic-point contribution `genericPointStalkKModule`, read as a sheaf of modules over
`K_X`, is built so that a morphism out of `K_X(F)` into it is the same thing as an `𝒪_X`-linear
morphism out of `F` into a module carrying a `K_X`-action: pushforward of sheaves of modules
along `j_η` factors as pushforward over the ring sheaf `j_{η, *} 𝒪_{Spec 𝒪_{X, η}}` followed by
restriction of scalars along `𝒪_X ⟶ j_{η, *} 𝒪_{Spec 𝒪_{X, η}}`, and that map of ring sheaves
factors through `K_X` by
`AlgebraicGeometry.toTotalQuotientSheaf_comp_toStalkSpecPushforwardSheaf`. Since
`SheafOfModules.pushforwardComp` is the identity isomorphism, the two factorisations agree on
the nose once the two ring maps are identified, which is
`restrictScalars_genericPointStalkKModule`. This identification is what
`AlgebraicGeometry.genericPointComparison` in `Globalization` uses to land its hand-built
comparison morphism in `genericPointStalkModuleOf` rather than in `genericPointStalkKModule`
directly.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.GenericPointDecomposition
  (genericPointStalkModuleOf meromorphicSections)

universe u

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The two sides of the decomposition -/

/-- Meromorphic sections read in `X.Modules` are the sheaf of meromorphic sections read as a
sheaf of modules over the structure sheaf. -/
lemma meromorphicSections_eq (X : Scheme.{u}) (F : X.Modules) :
    meromorphicSections X F = meromorphicSectionSheafAsModule X F := rfl

/-! ### Sections over an empty open set -/

private lemma eq_zero_of_isTerminal {A : AddCommGrpCat.{u}} (h : IsTerminal A)
    (x : ToType A) : x = 0 := by
  have hid : (𝟙 A) = 0 := h.hom_ext _ _
  have h2 := ConcreteCategory.congr_hom hid x
  simp only [ConcreteCategory.id_apply] at h2
  rw [h2]
  simp

/-- A sheaf of modules on a scheme has no sections over an empty open set: the sheaf condition
for the empty covering of `⊥` makes that module of sections a terminal abelian group. -/
lemma subsingleton_sections_of_eq_bot {Y : Scheme.{u}} (N : Y.Modules) {U : Y.Opens}
    (hU : U = ⊥) : Subsingleton (ToType Γ(N, U)) := by
  have hterm : IsTerminal (((SheafOfModules.toSheaf Y.ringCatSheaf).obj N).obj.obj (op U)) :=
    TopCat.Sheaf.isTerminalOfEqEmpty _ hU
  exact ⟨fun a b ↦ (eq_zero_of_isTerminal hterm a).trans
    (eq_zero_of_isTerminal hterm b).symm⟩

/-! ### The generic-point contributions form a locally finite family -/

/-- The generic-point contribution of a module at a generic point outside an open set restricts
to a zero module on that open set: the spectrum of the local ring there does not meet the open
set, so the pullback has no sections over its preimage. -/
lemma isZero_restrict_genericPointStalkModuleOf {V : X.Opens} (F : X.Modules)
    (η : genericPoints X) (hη : (η : X) ∉ V) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (genericPointStalkModuleOf X F η)) := by
  refine isZero_of_subsingleton_sections fun U ↦ ?_
  have hnot : (η : X) ∉ V.ι ''ᵁ U := fun hmem ↦ hη (V.ι_image_le U hmem)
  have hbot : X.fromSpecStalk η.1 ⁻¹ᵁ (V.ι ''ᵁ U) = ⊥ := fromSpecStalk_preimage_eq_bot η.2 hnot
  exact subsingleton_sections_of_eq_bot
    ((Scheme.Modules.pullback (X.fromSpecStalk η.1)).obj F) hbot

/-- The coproduct of the generic-point contributions of a sheaf of modules is their product,
when every quasi-compact open has finitely many irreducible components: on an affine open only
the finitely many generic points lying in it contribute, the others restricting to zero
objects. -/
theorem nonempty_sigmaIsoPi_genericPointStalkModuleOf (X : Scheme.{u}) (F : X.Modules)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Nonempty ((∐ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) ≅
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) := by
  let _ : DecidableEq (genericPoints X) := Classical.decEq _
  have : IsIso (sigmaPiComparison fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) :=
    isIso_sigmaPiComparison_of_locallyFinite _ (fun V : X.affineOpens ↦ (V : X.Opens))
      (IsOpenCover.mk (iSup_affineOpens_eq_top X))
      (fun V η ↦ (η : X) ∈ (V : X.Opens))
      (fun V ↦ finite_genericPoints_mem_of_isCompact X _ V.2.isCompact hfinite)
      (fun _ η hη ↦ isZero_restrict_genericPointStalkModuleOf F η hη)
  exact ⟨asIso (sigmaPiComparison fun η : genericPoints X ↦ genericPointStalkModuleOf X F η)⟩

/-! ### Quasi-coherence of the generic-point contributions -/

/-- The generic-point contribution of a quasi-coherent module is quasi-coherent: the pullback of
a quasi-coherent module is quasi-coherent, and `j_η` is an affine morphism. -/
instance isQuasicoherent_genericPointStalkModuleOf (F : X.Modules) [F.IsQuasicoherent]
    (η : genericPoints X) : (genericPointStalkModuleOf X F η).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom
    (X.fromSpecStalk η.1) _

/-- The product over the generic points of the irreducible components of the generic-point
contributions of a quasi-coherent module is quasi-coherent, when every quasi-compact open has
finitely many irreducible components: on an affine open only finitely many factors have any
sections, and a finite product of quasi-coherent modules on an affine scheme is
quasi-coherent. -/
theorem isQuasicoherent_pi_genericPointStalkModuleOf (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    (∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η).IsQuasicoherent := by
  refine Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens
    (∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) fun V ↦ ?_
  obtain ⟨V, hV⟩ := V
  have hfin : Finite {η : genericPoints X // (η : X) ∈ V} :=
    finite_genericPoints_mem_of_isCompact X V hV.isCompact hfinite
  have h1 : (∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η).restrict V.ι ≅
      ∏ᶜ fun η : genericPoints X ↦ (genericPointStalkModuleOf X F η).restrict V.ι :=
    restrictPiIso V.ι _
  have h2 : (∏ᶜ fun η : genericPoints X ↦ (genericPointStalkModuleOf X F η).restrict V.ι) ≅
      ∏ᶜ fun s : {η : genericPoints X // (η : X) ∈ V} ↦
        (genericPointStalkModuleOf X F s.1).restrict V.ι :=
    piSubtypeIsoOfSubsingletonHom _ (fun η : genericPoints X ↦ (η : X) ∈ V)
      fun η hη W ↦ ⟨fun f g ↦ (isZero_restrict_genericPointStalkModuleOf F η hη).eq_of_tgt f g⟩
  have h3 : (∏ᶜ fun s : {η : genericPoints X // (η : X) ∈ V} ↦
      (genericPointStalkModuleOf X F s.1).restrict V.ι).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isQuasicoherent_pi _ fun s ↦
      Scheme.Modules.isQuasicoherent_restrictFunctor V.ι (genericPointStalkModuleOf X F s.1)
  exact Stacks.Descent.isQuasicoherent_of_iso (h1 ≪≫ h2).symm h3

/-! ### The comparison morphism -/

/-- The structure sheaf of the spectrum of a stalk, read in `RingCat` at the type
`Sheaf (Opens.grothendieckTopology _) RingCat` rather than through `TopCat.Sheaf`, so that it is
recognised as a sheaf of rings over which `SheafOfModules` has a category. -/
abbrev specStalkRingCatSheaf (X : Scheme.{u}) (x : X) :
    Sheaf (Opens.grothendieckTopology ((Spec (X.presheaf.stalk x)) : TopCat)) RingCat.{u} :=
  (Spec (X.presheaf.stalk x)).ringCatSheaf

/-- The comparison map `K_X ⟶ j_{η, *} 𝒪_{Spec 𝒪_{X, η}}` of sheaves of rings, read in
`RingCat` as a structure map for pushforward of sheaves of modules along `j_η`. -/
abbrev toStalkSpecPushforwardRingCatSheafHom (η : genericPoints X) :
    Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.totalQuotientSheaf
      ⟶
      ((Opens.map (X.fromSpecStalk η.1).base).sheafPushforwardContinuous RingCat.{u} _ _).obj
        (specStalkRingCatSheaf X η.1) :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).map
    (toStalkSpecPushforwardSheaf η)

/-- The structure map of `j_η` factors through the sheaf of total quotient rings. -/
lemma toTotalQuotientRingSheaf_comp_toStalkSpecPushforwardRingCatSheafHom
    (η : genericPoints X) :
    toTotalQuotientRingSheaf X ≫ toStalkSpecPushforwardRingCatSheafHom η =
      (X.fromSpecStalk η.1).toRingCatSheafHom :=
  ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat.{u})).map_comp X.toTotalQuotientSheaf
        (toStalkSpecPushforwardSheaf η)).symm.trans
    (congrArg (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat.{u})).map
        (toTotalQuotientSheaf_comp_toStalkSpecPushforwardSheaf η))

/-- The generic-point contribution `j_{η, *} j_η^* F`, read as a sheaf of modules over the sheaf
of total quotient rings: the pushforward along `j_η` taken over the ring sheaf
`j_{η, *} 𝒪_{Spec 𝒪_{X, η}}` and then restricted along `K_X ⟶ j_{η, *} 𝒪_{Spec 𝒪_{X, η}}`. -/
abbrev genericPointStalkKModule (F : X.Modules) (η : genericPoints X) :
    SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf) :=
  (SheafOfModules.pushforward (toStalkSpecPushforwardRingCatSheafHom η)).obj
    ((Scheme.Modules.pullback (X.fromSpecStalk η.1)).obj F)

/-- Restricting scalars along `𝒪_X ⟶ K_X` returns the generic-point contribution: pushforward
along `j_η` is pushforward over `j_{η, *} 𝒪_{Spec 𝒪_{X, η}}` followed by restriction of scalars,
and the two structure maps agree. -/
lemma restrictScalars_genericPointStalkKModule (F : X.Modules) (η : genericPoints X) :
    (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
        (genericPointStalkKModule F η) = genericPointStalkModuleOf X F η := by
  rw [show (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
      (genericPointStalkKModule F η) =
    (SheafOfModules.pushforward
        (toTotalQuotientRingSheaf X ≫ toStalkSpecPushforwardRingCatSheafHom η)).obj
      ((Scheme.Modules.pullback (X.fromSpecStalk η.1)).obj F) from rfl,
    toTotalQuotientRingSheaf_comp_toStalkSpecPushforwardRingCatSheafHom η]
  rfl

/-- The change-of-rings adjunction along `𝒪_X ⟶ K_X`, whose unit is
`AlgebraicGeometry.toMeromorphicSectionSheafAsModule`. -/
abbrev totalQuotientChangeOfRingsAdjunction (X : Scheme.{u}) :=
  Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
    (Opens.grothendieckTopology X) X.toTotalQuotientSheaf.hom
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf).property

/-! ### Where the comparison morphism lives

The comparison morphism `K_X(F) ⟶ j_{η, *} F_η` and its product form are
`AlgebraicGeometry.genericPointComparison` (Globalization.lean:394) and
`AlgebraicGeometry.genericPointComparisonPi` (Globalization.lean:402), in
`StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Globalization`. They are
built there by hand from the presheaf-level comparison
`AlgebraicGeometry.genericPointComparisonPresheaf` rather than from the two adjunctions used
above, because a hand-built comparison has computable sections; the sectionwise statement that
makes that pay is `AlgebraicGeometry.bijective_genericPointComparisonSectionsPi`. -/

/-! ### Transfer between the two decompositions -/

/-- The direct-sum and the product decomposition of the sheaf of meromorphic sections of a module
imply one another, when every quasi-compact open has finitely many irreducible components. This
is the first sentence of the proof of the source: a locally finite direct sum of sheaves of
modules is its product. -/
theorem nonempty_meromorphicSections_iso_coproduct_iff_product (X : Scheme.{u}) (F : X.Modules)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Nonempty (meromorphicSections X F ≅
        ∐ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) ↔
      Nonempty (meromorphicSections X F ≅
        ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) :=
  ⟨fun ⟨e⟩ ↦ ⟨e ≪≫ (nonempty_sigmaIsoPi_genericPointStalkModuleOf X F hfinite).some⟩,
    fun ⟨e⟩ ↦ ⟨e ≪≫ (nonempty_sigmaIsoPi_genericPointStalkModuleOf X F hfinite).some.symm⟩⟩

/-- The sheaf of meromorphic sections of a quasi-coherent module is quasi-coherent as soon as it
is the product of the generic-point contributions, when every quasi-compact open has finitely
many irreducible components. This is the quasi-coherence clause of part (2) of the source,
reduced to the displayed decomposition. -/
theorem meromorphicSections_isQuasicoherent_of_nonempty_iso_product (X : Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (h : Nonempty (meromorphicSections X F ≅
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η)) :
    (meromorphicSections X F).IsQuasicoherent :=
  Stacks.Descent.isQuasicoherent_of_iso h.some.symm
    (isQuasicoherent_pi_genericPointStalkModuleOf X F hfinite)

end AlgebraicGeometry
