module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QuasiCoherentPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.SupportedSerreQuotient
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.InverseImage

/-!
# An explicit form of the restriction square of Gabriel–Rosenberg reconstruction

Let `X` and `Y` be quasi-compact and quasi-separated schemes, let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence, let `U ⊆ X` and `V ⊆ Y` be quasi-compact opens
whose closed complements `Z` and `T` are matched by `e`, and consider the square whose top row is
`e`, whose bottom row is a functor `F : QCoh(𝒪_U) ⥤ QCoh(𝒪_V)` and whose two columns are
restriction to `U` and restriction to `V`.

Step 6 of [Stacks, Tag 0GPJ] produces the bottom functor `F` from the universal property of the
two Serre localizations of [Stacks, Tag 0GPH]; the functor it produces is
`CategoryTheory.LocalizerMorphism.localizedFunctor` and has therefore no description on
sections.  This file replaces that by an explicit construction:

`F = (U.ι)_* ⋙ e ⋙ (· restricted to V)`,

that is: *extend* a quasi-coherent module on `U` to `X` by pushing it forward along the open
immersion `U.ι`, apply `e`, and restrict to `V`.  Both outer functors have a formula on
sections, so `F` does too.

The extension is canonical, not a choice: `(U.ι)_*` is a fully faithful right adjoint of
restriction, so it is a section of restriction up to the canonical isomorphism
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`, and independence of the
extension is the statement that the unit `M ⟶ (U.ι)_* (M|_U)` becomes invertible after applying
`e` and restricting to `V`.  That is proved here: the unit becomes invertible under restriction
to `U`, hence lies in the class `(quasicoherentSupportedOn X Z).isoModSerre` because restriction
to `U` is the Serre localization at that class, hence its image under `e` lies in the
corresponding class for `T`, which restriction to `V` inverts.

## Main definitions

* `AlgebraicGeometry.qcohUnderlying` and `AlgebraicGeometry.qcohUnderlyingHom` — an object and a
  morphism of quasi-coherent modules, in the `AlgebraicGeometry.Scheme.Modules` spelling.
* `AlgebraicGeometry.quasicoherentRestrictionUnit` — the unit `M ⟶ j_* (M|_V)` on quasi-coherent
  modules, given on sections by `M.presheaf.map (homOfLE (j.image_preimage_le W)).op`.
* `AlgebraicGeometry.restrictionSquareFunctor` — the explicit bottom functor `F` of step 6.
* `AlgebraicGeometry.restrictionSquareIso` — the explicit commuting isomorphism for the square,
  whose component at `M` is `e` and restriction to `V` applied to the unit at `M`.
* `AlgebraicGeometry.restrictionSquareFunctorIsoLocalizedFunctor` — the comparison with the
  functor produced by the universal property of the two localizations.

## Main results

* `AlgebraicGeometry.restrictionSquareFunctor_sections` and
  `AlgebraicGeometry.restrictionSquareFunctor_map_app` — the formula on sections.
* `AlgebraicGeometry.isIso_map_unit_of_supportedCorrespondence`,
  `AlgebraicGeometry.isIso_app_map_unit_of_supportedCorrespondence` and
  `AlgebraicGeometry.isIso_app_map_unit_of_le` — independence of the extension, as a functor
  isomorphism, on the sections over an open of `V`, and on the sections over an open of `Y`
  contained in `V`.
* `AlgebraicGeometry.restrictionSquareFunctor_isEquivalence` — `F` is an equivalence.
* `AlgebraicGeometry.isEquivalence_and_restrictionSquare` — step 6 with the bottom functor
  explicit.

## Implementation notes

The unit is defined componentwise from `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`
through `CategoryTheory.ObjectProperty.homMk`, rather than by transporting the adjunction along
the two fully faithful inclusions with `CategoryTheory.Adjunction.restrictFullyFaithful`: the
transported unit is not given by a formula, whereas the componentwise definition makes the
section-level formula a `rfl`.

The category of quasi-coherent modules is taken as a full subcategory of
`SheafOfModules X.ringCatSheaf`, while sections and the action of a morphism on sections are
stated for `AlgebraicGeometry.Scheme.Modules`.  The two are the same category but not
*reducibly* so, and field notation resolves against the head symbol of a type rather than up to
unfolding, so `AlgebraicGeometry.qcohUnderlying` and `AlgebraicGeometry.qcohUnderlyingHom` name
the underlying object and morphism in the second spelling; every section-level statement below
goes through them.

Exactness and additivity of `AlgebraicGeometry.quasicoherentRestriction` are proved here because
the corresponding facts in the file proving [Stacks, Tag 0GPH] are private to it.  They are
needed to recognize the kernel of restriction as the Serre class of supported modules, through
`CategoryTheory.ObjectProperty.SerreClassLocalization.isZero_obj_iff`, and to apply
`CategoryTheory.Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms`.

Quasi-compactness of `U` enters as the instance `[CompactSpace U.toScheme]` rather than as a
hypothesis `IsCompact (U : Set X)`, because `QuasiCompact U.ι` and `QuasiSeparated U.ι` have to
be available while the *statements* mentioning `AlgebraicGeometry.quasicoherentPushforward U.ι`
are elaborated.  The two forms are interchangeable by `isCompact_iff_compactSpace`.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 56.6.4 (Tag 0GPH)](https://stacks.math.columbia.edu/tag/0GPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism with an invertible right factor in a factorization of the identity is itself
invertible.  Stated with the factorization as a hypothesis rather than as an instance so that no
rewriting of the composite is needed to use it: both morphisms are read off the hypothesis. -/
theorem isIso_of_comp_eq_id {C : Type*} [Category C] {A B : C} (f : A ⟶ B) (g : B ⟶ A)
    (h : f ≫ g = 𝟙 A) [IsIso g] : IsIso f := by
  rw [IsIso.eq_inv_of_inv_hom_id h]
  infer_instance

/-! ### The underlying module of a quasi-coherent module -/

section Underlying

variable {Y : Scheme.{u}}

/-- **The underlying `𝒪_Y`-module of a quasi-coherent module**, in the
`AlgebraicGeometry.Scheme.Modules` spelling.  Sections and the action on sections are stated for
that spelling, while the category of quasi-coherent modules is a full subcategory of
`SheafOfModules Y.ringCatSheaf`; the two are the same category, but field notation resolves
against the head symbol of a type, so the two spellings must be named apart. -/
abbrev qcohUnderlying (M : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) :
    Y.Modules :=
  M.obj

/-- **The underlying morphism of `𝒪_Y`-modules of a morphism of quasi-coherent modules**, in the
`AlgebraicGeometry.Scheme.Modules` spelling.  See `AlgebraicGeometry.qcohUnderlying`. -/
abbrev qcohUnderlyingHom
    {M N : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    qcohUnderlying M ⟶ qcohUnderlying N :=
  φ.hom

end Underlying

/-! ### Exactness of restriction on quasi-coherent modules -/

section Restriction

variable {V Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j]

/-- **Restriction of quasi-coherent modules along an open immersion is left exact.**  The
inclusion of the quasi-coherent modules is exact and reflects isomorphisms, so left exactness is
inherited from restriction of all modules. -/
instance quasicoherentRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (quasicoherentRestriction j) := by
  have : PreservesFiniteLimits
      (quasicoherentRestriction j ⋙ (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι) := by
    change PreservesFiniteLimits ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙
      Scheme.Modules.restrictFunctor j)
    exact @comp_preservesFiniteLimits _ _ _ _ _ _
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι (Scheme.Modules.restrictFunctor j)
      (ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _)
      (Scheme.Modules.restrictFunctor_preservesFiniteLimits j)
  exact preservesFiniteLimits_of_reflects_of_preserves (quasicoherentRestriction j)
    (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι

/-- **Restriction of quasi-coherent modules along an open immersion is right exact.** -/
instance quasicoherentRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (quasicoherentRestriction j) := by
  have : PreservesFiniteColimits
      (quasicoherentRestriction j ⋙ (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι) := by
    change PreservesFiniteColimits ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙
      Scheme.Modules.restrictFunctor j)
    exact @comp_preservesFiniteColimits _ _ _ _ _ _
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι (Scheme.Modules.restrictFunctor j)
      (ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _)
      (inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor j)))
  exact preservesFiniteColimits_of_reflects_of_preserves (quasicoherentRestriction j)
    (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι

/-- Restriction of quasi-coherent modules along an open immersion is additive: on morphisms it
is restriction of all modules, which is additive. -/
instance quasicoherentRestriction_additive : (quasicoherentRestriction j).Additive := by
  constructor
  intro A B g h
  apply (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι.map_injective
  change (Scheme.Modules.restrictFunctor j).map (g.hom + h.hom) =
    (Scheme.Modules.restrictFunctor j).map g.hom + (Scheme.Modules.restrictFunctor j).map h.hom
  exact CategoryTheory.Functor.map_add (Scheme.Modules.restrictFunctor j)

/-- **The sections of a restricted quasi-coherent module.**  Restriction of quasi-coherent
modules is `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, so its sections over an open `W`
of the source are the sections of the original module over the image of `W`. -/
theorem quasicoherentRestriction_sections
    (M : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) (W : V.Opens) :
    Γ(qcohUnderlying ((quasicoherentRestriction j).obj M), W) = Γ(qcohUnderlying M, j ''ᵁ W) :=
  rfl

/-- **A morphism of quasi-coherent modules restricted to an open, on sections.** -/
theorem quasicoherentRestriction_map_app
    {M N : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory} (φ : M ⟶ N)
    (W : V.Opens) :
    (qcohUnderlyingHom ((quasicoherentRestriction j).map φ)).app W =
      (qcohUnderlyingHom φ).app (j ''ᵁ W) :=
  rfl

end Restriction

/-! ### The sections of a quasi-coherent pushforward -/

section Pushforward

variable {V Y : Scheme.{u}} (j : V ⟶ Y) [QuasiCompact j] [QuasiSeparated j]

/-- **The sections of the pushforward of a quasi-coherent module.** -/
theorem quasicoherentPushforward_sections
    (M : (SheafOfModules.isQuasicoherent V.ringCatSheaf).FullSubcategory) (W : Y.Opens) :
    Γ(qcohUnderlying ((quasicoherentPushforward j).obj M), W) =
      Γ(qcohUnderlying M, j ⁻¹ᵁ W) :=
  rfl

/-- **A morphism of quasi-coherent modules pushed forward, on sections.** -/
theorem quasicoherentPushforward_map_app
    {M N : (SheafOfModules.isQuasicoherent V.ringCatSheaf).FullSubcategory} (φ : M ⟶ N)
    (W : Y.Opens) :
    (qcohUnderlyingHom ((quasicoherentPushforward j).map φ)).app W =
      (qcohUnderlyingHom φ).app (j ⁻¹ᵁ W) :=
  rfl

end Pushforward

/-! ### The canonical extension and its unit -/

section Unit

variable {V Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]

/-- **The unit of the extension of quasi-coherent modules along an open immersion.**  For `M` a
quasi-coherent `𝒪_Y`-module, this is the canonical map `M ⟶ j_* (M|_V)`, given on sections over
an open `W` of `Y` by the restriction map `Γ(M, W) ⟶ Γ(M, j(j⁻¹ W))`.

This is the unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, read in the full
subcategory of quasi-coherent modules, where morphisms are morphisms of all modules. -/
def quasicoherentRestrictionUnit :
    𝟭 (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ⟶
      quasicoherentRestriction j ⋙ quasicoherentPushforward j where
  app M := ObjectProperty.homMk ((Scheme.Modules.restrictAdjunction j).unit.app
    (qcohUnderlying M))
  naturality _ _ f := by
    apply ObjectProperty.hom_ext
    exact (Scheme.Modules.restrictAdjunction j).unit.naturality (qcohUnderlyingHom f)

/-- **The unit of the extension, on sections**: it is the restriction map of the module from `W`
to the open `j (j⁻¹ W)` contained in it. -/
@[simp] theorem quasicoherentRestrictionUnit_app_app
    (M : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) (W : Y.Opens) :
    (qcohUnderlyingHom ((quasicoherentRestrictionUnit j).app M)).app W =
      (qcohUnderlying M).presheaf.map (homOfLE (j.image_preimage_le W)).op :=
  rfl

/-- **The unit of the extension becomes invertible after restricting to the open.**  This is the
triangle identity of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` together with the
invertibility of its counit. -/
instance isIso_map_quasicoherentRestrictionUnit
    (M : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) :
    IsIso ((quasicoherentRestriction j).map ((quasicoherentRestrictionUnit j).app M)) := by
  have h : IsIso ((Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.restrictAdjunction j).unit.app (qcohUnderlying M))) :=
    isIso_of_comp_eq_id _ _
      ((Scheme.Modules.restrictAdjunction j).left_triangle_components (qcohUnderlying M))
  exact (ObjectProperty.isIso_hom_iff _).1 h

end Unit

/-! ### Invertibility modulo the supported Serre class -/

section Localization

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- Recognizing membership in the class of isomorphisms modulo the Serre class of modules
supported on `Z` as invertibility after restriction to the complementary quasi-compact open.
Restriction to that open is the Serre localization at that class ([Stacks, Tag 0GPH]), so its
kernel is that Serre class
(`CategoryTheory.ObjectProperty.SerreClassLocalization.isZero_obj_iff`), and restriction is
exact, so `CategoryTheory.Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms` applies. -/
theorem isoModSerre_of_isIso_map_quasicoherentRestriction (Z : Set X) (U : X.Opens)
    (hUZ : (U : Set X) = Zᶜ) (hU : IsCompact (U : Set X))
    {M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (f : M ⟶ N)
    (hf : IsIso ((quasicoherentRestriction U.ι).map f)) :
    (quasicoherentSupportedOn X Z).isoModSerre f := by
  have hloc := quasicoherentRestriction_isLocalization X Z U hUZ hU
  have hker : (quasicoherentRestriction U.ι).kernel = quasicoherentSupportedOn X Z := by
    ext A
    exact ObjectProperty.SerreClassLocalization.isZero_obj_iff (quasicoherentRestriction U.ι)
      (quasicoherentSupportedOn X Z) A
  have hW : (quasicoherentRestriction U.ι).kernel.isoModSerre =
      (quasicoherentSupportedOn X Z).isoModSerre := by
    ext A B g
    simp [ObjectProperty.isoModSerre, hker]
  rwa [← hW, Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]

end Localization

/-! ### The explicit bottom functor of the square -/

section SquareFunctor

variable {X Y : Scheme.{u}} [QuasiSeparatedSpace X]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
  (U : X.Opens) [CompactSpace U.toScheme] (V : Y.Opens)

/-- **The explicit bottom functor of the restriction square of step 6 of [Stacks, Tag 0GPJ].**
Given an equivalence `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)`, a quasi-compact open `U ⊆ X` and an open
`V ⊆ Y`, this is the composite

`QCoh(𝒪_U) --(U.ι)_*--> QCoh(𝒪_X) --e--> QCoh(𝒪_Y) --restrict--> QCoh(𝒪_V)`,

that is: extend a quasi-coherent module on `U` to `X` canonically by pushing forward along the
open immersion, apply `e`, and restrict to `V`.  Unlike
`CategoryTheory.LocalizerMorphism.localizedFunctor`, the functor step 6 produces from the
universal property of the two Serre localizations, this has a formula on sections. -/
def restrictionSquareFunctor :
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory :=
  quasicoherentPushforward U.ι ⋙ e.functor ⋙ quasicoherentRestriction V.ι

/-- `AlgebraicGeometry.restrictionSquareFunctor` on objects: extend, apply `e`, restrict. -/
theorem restrictionSquareFunctor_obj
    (M : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory) :
    (restrictionSquareFunctor e U V).obj M =
      (quasicoherentRestriction V.ι).obj
        (e.functor.obj ((quasicoherentPushforward U.ι).obj M)) :=
  rfl

/-- `AlgebraicGeometry.restrictionSquareFunctor` on morphisms. -/
theorem restrictionSquareFunctor_map
    {M N : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    (restrictionSquareFunctor e U V).map φ =
      (quasicoherentRestriction V.ι).map
        (e.functor.map ((quasicoherentPushforward U.ι).map φ)) :=
  rfl

/-- **The formula on sections of `AlgebraicGeometry.restrictionSquareFunctor`.**  The sections
over an open `W ⊆ V` are the sections of `e` applied to the pushforward of `M`, over the image of
`W` in `Y`; and the sections of that pushforward over an open `W'` of `X` are the sections of `M`
over `U.ι ⁻¹ᵁ W'` (`AlgebraicGeometry.quasicoherentPushforward_sections`).  Composing the two
describes `F` on sections in terms of the section-level data of `e` alone. -/
theorem restrictionSquareFunctor_sections
    (M : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory)
    (W : V.toScheme.Opens) :
    Γ(qcohUnderlying ((restrictionSquareFunctor e U V).obj M), W) =
      Γ(qcohUnderlying (e.functor.obj ((quasicoherentPushforward U.ι).obj M)), V.ι ''ᵁ W) :=
  rfl

/-- **The formula on sections of `AlgebraicGeometry.restrictionSquareFunctor` on morphisms.** -/
theorem restrictionSquareFunctor_map_app
    {M N : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory} (φ : M ⟶ N)
    (W : V.toScheme.Opens) :
    (qcohUnderlyingHom ((restrictionSquareFunctor e U V).map φ)).app W =
      (qcohUnderlyingHom (e.functor.map ((quasicoherentPushforward U.ι).map φ))).app
        (V.ι ''ᵁ W) :=
  rfl

end SquareFunctor

/-! ### The explicit square -/

section Matched

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
  (U : X.Opens) [CompactSpace U.toScheme] (V : Y.Opens) (Z : Set X) (T : Set Y)
  (hcorr : ∀ E, quasicoherentSupportedOn X Z E ↔
    quasicoherentSupportedOn Y T (e.functor.obj E))
  (hUZ : (U : Set X) = Zᶜ) (hVT : (V : Set Y) = Tᶜ) (hV : IsCompact (V : Set Y))

include hcorr hUZ hVT hV

/-- **The unit of the extension along `U ↪ X` becomes invertible after applying `e` and
restricting to `V`.**  This is the independence of the extension: the unit is invertible after
restriction to `U`, hence lies in the class of isomorphisms modulo the Serre class of modules
supported on `Z`; `e` carries that class to the corresponding class for `T` by `hcorr`, and
restriction to `V` inverts that class because it is the Serre localization at it. -/
theorem isIso_map_unit_of_supportedCorrespondence
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsIso ((quasicoherentRestriction V.ι).map
      (e.functor.map ((quasicoherentRestrictionUnit U.ι).app M))) := by
  have hlocV := quasicoherentRestriction_isLocalization Y T V hVT hV
  have h1 : (quasicoherentSupportedOn X Z).isoModSerre
      ((quasicoherentRestrictionUnit U.ι).app M) :=
    isoModSerre_of_isIso_map_quasicoherentRestriction Z U hUZ
      (isCompact_iff_compactSpace.mpr ‹CompactSpace U.toScheme›) _ inferInstance
  rw [ObjectProperty.isoModSerre_eq_inverseImage_of_iff e.functor hcorr] at h1
  exact Localization.inverts (quasicoherentRestriction V.ι)
    (quasicoherentSupportedOn Y T).isoModSerre _ h1

/-- **The comparison of sections over an open of `V`.**  The map on sections induced by `e`
applied to the unit `M ⟶ (U.ι)_* (M|_U)`, restricted to `V`, is invertible over every open of
`V`; by `AlgebraicGeometry.quasicoherentRestriction_map_app` that map is the one induced on the
sections over `V.ι ''ᵁ W`.  This is the section-level form of
`AlgebraicGeometry.isIso_map_unit_of_supportedCorrespondence`, and is what a section-level
descent datum for the family of local functors consumes. -/
theorem isIso_app_map_unit_of_supportedCorrespondence
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (W : V.toScheme.Opens) :
    IsIso ((qcohUnderlyingHom ((quasicoherentRestriction V.ι).map
      (e.functor.map ((quasicoherentRestrictionUnit U.ι).app M)))).app W) :=
  have := isIso_map_unit_of_supportedCorrespondence e U V Z T hcorr hUZ hVT hV M
  have : IsIso (qcohUnderlyingHom ((quasicoherentRestriction V.ι).map
      (e.functor.map ((quasicoherentRestrictionUnit U.ι).app M)))) :=
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).ι.map_isIso
      ((quasicoherentRestriction V.ι).map
        (e.functor.map ((quasicoherentRestrictionUnit U.ι).app M)))
  inferInstance

/-- **The comparison of sections over an open of `Y` contained in `V`.**  For `W ⊆ V` an open of
`Y`, the map `Γ(e M, W) ⟶ Γ(e ((U.ι)_* (M|_U)), W)` induced by `e` applied to the unit is
invertible.  This is `AlgebraicGeometry.isIso_app_map_unit_of_supportedCorrespondence` read over
an open of `Y` rather than of `V`, which is the form a descent datum indexed by the opens of `Y`
consumes: the transition between two charts `V₁` and `V₂` over an open `W ≤ V₁ ⊓ V₂` is the
composite of one of these isomorphisms with the inverse of the other. -/
theorem isIso_app_map_unit_of_le
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (W : Y.Opens)
    (hW : W ≤ V) :
    IsIso ((qcohUnderlyingHom
      (e.functor.map ((quasicoherentRestrictionUnit U.ι).app M))).app W) := by
  have h : IsIso ((qcohUnderlyingHom
      (e.functor.map ((quasicoherentRestrictionUnit U.ι).app M))).app (V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :=
    isIso_app_map_unit_of_supportedCorrespondence e U V Z T hcorr hUZ hVT hV M (V.ι ⁻¹ᵁ W)
  have hWeq : V.ι ''ᵁ V.ι ⁻¹ᵁ W = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  exact hWeq ▸ h

/-- **The explicit commuting isomorphism of the restriction square of step 6 of
[Stacks, Tag 0GPJ].**  Its component at a quasi-coherent `𝒪_X`-module `M` is `e` followed by
restriction to `V`, applied to the unit `M ⟶ (U.ι)_* (M|_U)`. -/
def restrictionSquareIso :
    e.functor ⋙ quasicoherentRestriction V.ι ≅
      quasicoherentRestriction U.ι ⋙ restrictionSquareFunctor e U V :=
  NatIso.ofComponents
    (fun M ↦ @asIso _ _ _ _
      ((quasicoherentRestriction V.ι).map
        (e.functor.map ((quasicoherentRestrictionUnit U.ι).app M)))
      (isIso_map_unit_of_supportedCorrespondence e U V Z T hcorr hUZ hVT hV M))
    (fun {M N} f ↦ by
      dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, asIso_hom,
        restrictionSquareFunctor]
      simp only [← CategoryTheory.Functor.map_comp]
      exact congrArg (fun g ↦ (quasicoherentRestriction V.ι).map (e.functor.map g))
        ((quasicoherentRestrictionUnit U.ι).naturality f))

/-- The component of `AlgebraicGeometry.restrictionSquareIso`. -/
theorem restrictionSquareIso_hom_app
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (restrictionSquareIso e U V Z T hcorr hUZ hVT hV).hom.app M =
      (quasicoherentRestriction V.ι).map
        (e.functor.map ((quasicoherentRestrictionUnit U.ι).app M)) :=
  rfl

/-- **The explicit functor of step 6 is isomorphic to the one produced by the universal property
of the two Serre localizations.**  Both make the square of step 6 commute and restriction to `U`
is a localization, so `CategoryTheory.Localization.liftNatIso` identifies them.  This is what
makes it legitimate to substitute the explicit functor for
`CategoryTheory.LocalizerMorphism.localizedFunctor` in step 6 of [Stacks, Tag 0GPJ].

The two localization instances are taken as hypotheses because they are needed while the
*statement* is elaborated, `CategoryTheory.LocalizerMorphism.localizedFunctor` consuming them;
they are supplied by `AlgebraicGeometry.quasicoherentRestriction_isLocalization`. -/
def restrictionSquareFunctorIsoLocalizedFunctor
    [(quasicoherentRestriction U.ι).IsLocalization (quasicoherentSupportedOn X Z).isoModSerre]
    [(quasicoherentRestriction V.ι).IsLocalization (quasicoherentSupportedOn Y T).isoModSerre] :
    restrictionSquareFunctor e U V ≅
      (ObjectProperty.localizerMorphismOfIff (P := quasicoherentSupportedOn X Z)
        (Q := quasicoherentSupportedOn Y T) e.functor hcorr).localizedFunctor
        (quasicoherentRestriction U.ι) (quasicoherentRestriction V.ι) :=
  haveI : Localization.Lifting (quasicoherentRestriction U.ι)
      (quasicoherentSupportedOn X Z).isoModSerre (e.functor ⋙ quasicoherentRestriction V.ι)
      (restrictionSquareFunctor e U V) :=
    ⟨(restrictionSquareIso e U V Z T hcorr hUZ hVT hV).symm⟩
  haveI : Localization.Lifting (quasicoherentRestriction U.ι)
      (quasicoherentSupportedOn X Z).isoModSerre (e.functor ⋙ quasicoherentRestriction V.ι)
      ((ObjectProperty.localizerMorphismOfIff (P := quasicoherentSupportedOn X Z)
        (Q := quasicoherentSupportedOn Y T) e.functor hcorr).localizedFunctor
        (quasicoherentRestriction U.ι) (quasicoherentRestriction V.ι)) :=
    ⟨(CatCommSq.iso (ObjectProperty.localizerMorphismOfIff
      (P := quasicoherentSupportedOn X Z) (Q := quasicoherentSupportedOn Y T)
      e.functor hcorr).functor (quasicoherentRestriction U.ι)
      (quasicoherentRestriction V.ι) _).symm⟩
  Localization.liftNatIso (quasicoherentRestriction U.ι)
    (quasicoherentSupportedOn X Z).isoModSerre (e.functor ⋙ quasicoherentRestriction V.ι)
    (e.functor ⋙ quasicoherentRestriction V.ι) _ _ (Iso.refl _)

/-- **The explicit functor of step 6 of [Stacks, Tag 0GPJ] is an equivalence**, being isomorphic
to the localized functor of the equivalence of Serre quotients. -/
theorem restrictionSquareFunctor_isEquivalence :
    (restrictionSquareFunctor e U V).IsEquivalence := by
  have hloc₁ := quasicoherentRestriction_isLocalization X Z U hUZ
    (isCompact_iff_compactSpace.mpr ‹CompactSpace U.toScheme›)
  have hloc₂ := quasicoherentRestriction_isLocalization Y T V hVT hV
  have hΦeq : (ObjectProperty.localizerMorphismOfIff (P := quasicoherentSupportedOn X Z)
      (Q := quasicoherentSupportedOn Y T) e.functor hcorr).IsLocalizedEquivalence :=
    ObjectProperty.isLocalizedEquivalence_localizerMorphismOfIff e.functor hcorr
  exact CategoryTheory.Functor.isEquivalence_of_iso
    (restrictionSquareFunctorIsoLocalizedFunctor e U V Z T hcorr hUZ hVT hV).symm

/-- **Step 6 of [Stacks, Tag 0GPJ], with the bottom functor explicit.**  In the situation of
step 6, `AlgebraicGeometry.restrictionSquareFunctor` is an equivalence `QCoh(𝒪_U) ≌ QCoh(𝒪_V)`
fitting in a commuting square with the two restrictions, and it has a formula on sections. -/
theorem isEquivalence_and_restrictionSquare :
    (restrictionSquareFunctor e U V).IsEquivalence ∧
      Nonempty (e.functor ⋙ quasicoherentRestriction V.ι ≅
        quasicoherentRestriction U.ι ⋙ restrictionSquareFunctor e U V) :=
  ⟨restrictionSquareFunctor_isEquivalence e U V Z T hcorr hUZ hVT hV,
    ⟨restrictionSquareIso e U V Z T hcorr hUZ hVT hV⟩⟩

end Matched

end AlgebraicGeometry

end
