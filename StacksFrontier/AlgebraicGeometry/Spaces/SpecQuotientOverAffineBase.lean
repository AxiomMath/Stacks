module

public import StacksFrontier.AlgebraicGeometry.Scheme.SpecQuotientInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapFlatTargetSituation

/-!
# The closed subscheme cut out by an ideal of functions on an affine base

Let `S` be an affine scheme contained in a big fppf site `B`, and let `I` be an ideal of its
ring `Γ(S, ⊤)` of global functions.  This file produces the closed subscheme
`Z = \Spec(Γ(S, ⊤)/I) ⊆ S` as an *object of the big fppf category over `S`*, computes the
kernel of its structure morphism on global functions, and factors through it every object of the
category whose own kernel contains `I`.  For a finitely generated `I` the structure morphism is
of finite presentation.

## Main definitions

* `AlgebraicGeometry.specQuotientToBase`: the closed immersion
  `\Spec(Γ(S, ⊤)/I) ⟶ S`, namely the one cut out by `I` composed with the inverse of
  `AlgebraicGeometry.Scheme.isoSpec`.
* `AlgebraicGeometry.Space.specQuotientOver`: that closed subscheme as an object of
  `AlgebraicGeometry.BigFppfOver`.
* `AlgebraicGeometry.Space.specQuotientTest`: the same, read as a test scheme over the final
  algebraic space, which is the form in which the vanishing loci of Stacks 083F consume it.
* `AlgebraicGeometry.Space.specQuotientOverSite` and
  `AlgebraicGeometry.Space.specQuotientSiteHom`: the same closed subscheme cut out inside an
  arbitrary **affine object `V` of the category** rather than inside the base, together with its
  closed immersion into `V` as a morphism of the category.  The ideal is then an ideal of
  `Γ(V, ⊤)`.

## Main results

* `AlgebraicGeometry.ker_appTop_specQuotientToBase`: the kernel of the structure morphism
  of `Z` on global functions is `I` itself.
* `AlgebraicGeometry.Space.exists_hom_specQuotientOver`: an object of the big fppf category over
  `S` whose kernel on global functions contains `I` admits a morphism to `Z`.  A morphism of the
  big fppf category over `S` *is* a morphism over `S` — `CategoryTheory.Over.w` — so this is the
  factorisation of `T ⟶ S` through `Z` that the conclusion of Stacks 083K asks for.
* `AlgebraicGeometry.locallyOfFinitePresentation_specQuotientToBase` and
  `AlgebraicGeometry.quasiCompact_specQuotientToBase`: for finitely generated `I` the
  structure morphism of `Z` is locally of finite presentation, and it is always affine, hence
  quasi-compact and quasi-separated.
* `AlgebraicGeometry.Space.ker_appTop_specQuotientSiteHom`,
  `AlgebraicGeometry.Space.exists_comp_eq_specQuotientSiteHom` and
  `AlgebraicGeometry.Space.le_ker_appTop_of_comp_eq_specQuotientSiteHom`: the kernel
  computation and **both directions** of the factorisation over an affine object `V` of the
  category — a morphism `T ⟶ V` factors through the closed subscheme cut out by `I`, over `V`,
  exactly when `I` lies in the kernel of `Γ(V, ⊤) ⟶ Γ(T, ⊤)`.  Nothing is assumed of `T`.

## Implementation notes

The base `S` of the big fppf site plays the role of the source's `S = \Spec R`, so `R` is
`Γ(S, ⊤)` and the closed subscheme has to be transported along
`AlgebraicGeometry.Scheme.isoSpec` to sit over `S` rather than over `\Spec Γ(S, ⊤)`.  That
transport is the only content of the definitions: `AlgebraicGeometry.specQuotientMk`,
`AlgebraicGeometry.BigFppfSite.contains_specQuotient` and
`AlgebraicGeometry.locallyOfFinitePresentation_specQuotientMk` already supply the closed
immersion over `\Spec Γ(S, ⊤)`, its membership of the site and its finite presentation.

The kernel computation is the naturality of `AlgebraicGeometry.Scheme.ΓSpecIso`: pulling
functions back along `\Spec` of the quotient map is the quotient map itself, read through the
two copies of that isomorphism, and the inverse of `isoSpec` on global functions is the inverse
of `ΓSpecIso` because the two compose to the identity.  So the kernel is the kernel of
`Ideal.Quotient.mk I`, which is `I`.

The factorisation is `AlgebraicGeometry.Space.exists_comp_eq_of_ker_le`, whose hypothesis is an
inclusion of kernel ideal sheaves; the base is affine, so
`AlgebraicGeometry.Scheme.ker_le_ker_iff_of_isAffine` turns it into the inclusion of kernels on
global functions, which is the hypothesis stated here.  Both morphisms are taken to the final
object of the big fppf category over `S`, whose underlying scheme is `S`, so that the
factorisation is a morphism *of the category* — which is what the conclusion of Stacks 083K
asks for, the test scheme factoring through the closed subscheme over the base.

Together with `StacksFrontier/RingTheory/Flat/MakeMapZeroIdeal.lean`, which produces the ideal,
this is clause (a) of Stacks 083K and its finite-presentation refinement.  Nothing here carries
the tag: clause (b), the vanishing of `u_Z`, is about a map of modules and no module appears
below.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section SchemeLevel

variable (S : Scheme.{u}) [IsAffine S]

/-- **The closed subscheme of the affine base cut out by an ideal of its global functions.**
`\Spec(Γ(S, ⊤)/I) ⟶ S`, the closed immersion of `AlgebraicGeometry.specQuotientMk` carried over
to `S` along `AlgebraicGeometry.Scheme.isoSpec`. -/
abbrev specQuotientToBase (I : Ideal Γ(S, ⊤)) : Spec (.of (Γ(S, ⊤) ⧸ I)) ⟶ S :=
  specQuotientMk I ≫ S.isoSpec.inv

/-- The morphism `AlgebraicGeometry.specQuotientToBase S I` is a closed immersion. -/
instance isClosedImmersion_specQuotientToBase (I : Ideal Γ(S, ⊤)) :
    IsClosedImmersion (specQuotientToBase S I) :=
  inferInstance

/-- The morphism `AlgebraicGeometry.specQuotientToBase S I` is affine. -/
instance isAffineHom_specQuotientToBase (I : Ideal Γ(S, ⊤)) :
    IsAffineHom (specQuotientToBase S I) :=
  inferInstance

/-- The morphism `AlgebraicGeometry.specQuotientToBase S I` is quasi-compact. -/
instance quasiCompact_specQuotientToBase (I : Ideal Γ(S, ⊤)) :
    QuasiCompact (specQuotientToBase S I) :=
  inferInstance

/-- Pulling global functions back along the inverse of `AlgebraicGeometry.Scheme.isoSpec` is the
inverse of `AlgebraicGeometry.Scheme.ΓSpecIso`: the two morphisms of schemes compose to the
identity, so the two maps on global functions do too, and `ΓSpecIso` is an isomorphism. -/
theorem isoSpec_inv_appTop :
    S.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(S, ⊤)).inv := by
  rw [← cancel_mono (Scheme.ΓSpecIso Γ(S, ⊤)).hom, Iso.inv_hom_id, ← Scheme.toSpecΓ_appTop,
    ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, S.isoSpec.hom_inv_id, Scheme.Hom.id_appTop]

/-- **The kernel of the structure morphism of the closed subscheme cut out by `I` is `I`.** -/
theorem ker_appTop_specQuotientToBase (I : Ideal Γ(S, ⊤)) :
    RingHom.ker (specQuotientToBase S I).appTop.hom = I := by
  have happ : (specQuotientToBase S I).appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        (Scheme.ΓSpecIso (.of (Γ(S, ⊤) ⧸ I))).inv := by
    rw [Scheme.Hom.comp_appTop, isoSpec_inv_appTop]
    exact (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk I) : Γ(S, ⊤) ⟶ .of (Γ(S, ⊤) ⧸ I))).symm
  rw [happ, CommRingCat.hom_comp]
  exact (RingHom.ker_comp_of_injective _ fun x y hxy => by
    simpa using congrArg (Scheme.ΓSpecIso (.of (Γ(S, ⊤) ⧸ I))).hom.hom hxy).trans Ideal.mk_ker

/-- **The closed immersion cut out by a finitely generated ideal of functions on the affine base
is locally of finite presentation.**  The closed immersion is affine, hence quasi-compact and
quasi-separated, so this is the full "of finite presentation" the conclusion of Stacks 083K
asks of `Z ⟶ S`. -/
theorem locallyOfFinitePresentation_specQuotientToBase {I : Ideal Γ(S, ⊤)} (hI : I.FG) :
    LocallyOfFinitePresentation (specQuotientToBase S I) :=
  MorphismProperty.comp_mem @LocallyOfFinitePresentation (specQuotientMk I) S.isoSpec.inv
    (locallyOfFinitePresentation_specQuotientMk hI) inferInstance

end SchemeLevel

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of an object of the big fppf category over `S`, read as a morphism
to the final object of that category.  Taken this way rather than as the unique morphism out of
`CategoryTheory.Over.mkIdTerminal`, so that its underlying morphism of schemes is the structure
morphism *by definition*; `rw` cannot be used to identify the two, because a goal mentioning the
underlying morphism of a constructed morphism of the category is not type-correct at implicit
transparency. -/
def toBaseTerminal (T : BigFppfOver B S hS) :
    T ⟶ Over.mk (CategoryStruct.id (B.obj hS)) :=
  Over.homMk T.hom (Category.comp_id _)

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.toBaseTerminal B S hS T` is
the structure morphism of `T`. -/
@[simp]
theorem toScheme_map_toBaseTerminal (T : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).map (toBaseTerminal B S hS T) =
      B.inclusion.map T.hom := rfl

section Affine

variable [IsAffine S]

include hS in
/-- `\Spec Γ(S, ⊤)` lies in the site, because it is isomorphic to `S`: a quasi-compact
monomorphism does not increase the size of a scheme. -/
theorem contains_specGammaTop : B.Contains (Spec Γ(S, ⊤)) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact S.isoSpec.inv) hS

/-- The closed subscheme of the affine base cut out by an ideal of its global functions, as an
object of the big fppf category over `S`. -/
def specQuotientOver (I : Ideal Γ(S, ⊤)) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS
    (B.contains_specQuotient (contains_specGammaTop B S hS) I) (specQuotientToBase S I)

/-- The underlying scheme of `AlgebraicGeometry.Space.specQuotientOver B S hS I` is
`\Spec(Γ(S, ⊤)/I)`. -/
@[simp]
theorem toScheme_obj_specQuotientOver (I : Ideal Γ(S, ⊤)) :
    (BigFppfOver.toScheme B S hS).obj (specQuotientOver B S hS I) =
      Spec (.of (Γ(S, ⊤) ⧸ I)) := rfl

/-- The structure morphism of `AlgebraicGeometry.Space.specQuotientOver`, read as a morphism of
schemes, is the closed immersion cut out by the ideal. -/
theorem inclusion_map_specQuotientOver_hom (I : Ideal Γ(S, ⊤)) :
    B.inclusion.map (specQuotientOver B S hS I).hom = specQuotientToBase S I := rfl

/-- **An object of the big fppf category over `S` whose kernel on global functions contains `I`
factors through the closed subscheme cut out by `I`.**

The base is affine, so `AlgebraicGeometry.Scheme.ker_le_ker_iff_of_isAffine` turns the stated
inclusion of kernels on global functions into the inclusion of kernel ideal sheaves that
`AlgebraicGeometry.Space.exists_comp_eq_of_ker_le` consumes.  A morphism of the big fppf
category over `S` is a morphism over `S`, so the morphism produced is the factorisation
of `T ⟶ S` through `Z` of the conclusion of Stacks 083K. -/
theorem exists_hom_specQuotientOver (I : Ideal Γ(S, ⊤)) (T : BigFppfOver B S hS)
    (hle : I ≤ RingHom.ker (B.inclusion.map T.hom).appTop.hom) :
    Nonempty (T ⟶ specQuotientOver B S hS I) := by
  have : IsAffine
      ((BigFppfOver.toScheme B S hS).obj (Over.mk (CategoryStruct.id (B.obj hS)))) :=
    ‹IsAffine S›
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map
        (toBaseTerminal B S hS (specQuotientOver B S hS I))) :=
    isClosedImmersion_specQuotientToBase S I
  obtain ⟨ψ, -⟩ := exists_comp_eq_of_ker_le B S hS
    (toBaseTerminal B S hS (specQuotientOver B S hS I)) (toBaseTerminal B S hS T) hci
    ((Scheme.ker_le_ker_iff_of_isAffine _ _).2
      ((ker_appTop_specQuotientToBase S I).le.trans hle))
  exact ⟨ψ⟩

end Affine

/-! ### The same closed subscheme over an affine object of the site

The section above is the case `V = AlgebraicGeometry.Space.baseTerminal` of this one, whose
underlying scheme is the base `S`.  Nothing of it is changed: the declarations there are the
ones the finite-presentation clause of Stacks 083K consumes, and the construction below is a
second one, over an arbitrary affine object `V` of the category rather than over the base.  The
two have the same underlying closed immersion at `V = baseTerminal`, which is
`AlgebraicGeometry.Space.toScheme_map_specQuotientSiteHom_baseTerminal` and holds by definition.

**The ring is the ring of functions on `V`, never that of the base.**  Over `V` the ideal has to
be an ideal of `Γ(V, ⊤)`: the closed subscheme produced is a closed subscheme *of `V`*, and the
factorisation characterises it by the kernel of `Γ(V, ⊤) ⟶ Γ(T, ⊤)` for a morphism `T ⟶ V` of
the category.  An ideal of `Γ(S, ⊤)` would cut out a closed subscheme of the base instead, whose
preimage in `V` is in general strictly smaller than every closed subscheme of `V` one needs — and
the vanishing-locus consumers of this construction are stated over `Γ(V, ⊤)` for the same
reason, recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRingLevelZeroLocusOverAffine.lean`. -/

section AffineSiteObject

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

/-- `\Spec Γ(V, ⊤)` lies in the site for an affine object `V` of the category, because it is
isomorphic to the scheme of `V`, which lies in the site: a quasi-compact monomorphism does not
increase the size of a scheme.

This is `AlgebraicGeometry.Space.contains_specGammaTop` with the base replaced by the scheme of
an affine object of the category, whose membership of the site is what being an object of the
size-bounded category of schemes says. -/
theorem contains_specGammaTop_obj :
    B.Contains (Spec Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :=
  lt_of_le_of_lt
    (Scheme.size_le_of_mono_quasiCompact ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv)
    (show B.Contains ((BigFppfOver.toScheme B S hS).obj V) from V.left.property)

/-- **The closed subscheme of an affine object `V` of the big fppf category over `S` cut out by
an ideal of its global functions, as an object of that category.**  Its scheme is
`\Spec(Γ(V, ⊤)/I)` and its structure morphism to the base is the closed immersion into the
scheme of `V` followed by the structure morphism of `V`.

This is `AlgebraicGeometry.Space.specQuotientOver` relativised: there the closed subscheme is
cut out in the base, here in an arbitrary affine object of the category. -/
def specQuotientOverSite (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    BigFppfOver B S hS :=
  BigFppfOver.mk B S hS
    (B.contains_specQuotient (contains_specGammaTop_obj B S hS V) I)
    (specQuotientToBase ((BigFppfOver.toScheme B S hS).obj V) I ≫ B.inclusion.map V.hom)

/-- The underlying scheme of `AlgebraicGeometry.Space.specQuotientOverSite B S hS V I` is
`\Spec(Γ(V, ⊤)/I)`. -/
@[simp]
theorem toScheme_obj_specQuotientOverSite
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (BigFppfOver.toScheme B S hS).obj (specQuotientOverSite B S hS V I) =
      Spec (.of (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ I)) := rfl

/-- **The closed immersion of the closed subscheme cut out by `I` into `V`, as a morphism of the
big fppf category over `S`.**  It is a morphism of the category because the structure morphism
of `AlgebraicGeometry.Space.specQuotientOverSite` was defined to factor through that of `V`. -/
def specQuotientSiteHom (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    specQuotientOverSite B S hS V I ⟶ V :=
  Over.homMk
    (ObjectProperty.homMk (specQuotientToBase ((BigFppfOver.toScheme B S hS).obj V) I))
    (by apply ObjectProperty.hom_ext; rfl)

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.specQuotientSiteHom B S hS V I`
is `AlgebraicGeometry.specQuotientToBase` at the scheme of `V`. -/
@[simp]
theorem toScheme_map_specQuotientSiteHom
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (BigFppfOver.toScheme B S hS).map (specQuotientSiteHom B S hS V I) =
      specQuotientToBase ((BigFppfOver.toScheme B S hS).obj V) I := rfl

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.specQuotientSiteHom B S hS V I`
is a closed immersion. -/
instance isClosedImmersion_specQuotientSiteHom
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (specQuotientSiteHom B S hS V I)) :=
  isClosedImmersion_specQuotientToBase ((BigFppfOver.toScheme B S hS).obj V) I

/-- **The kernel on global functions of the closed immersion into `V` cut out by `I` is `I`.**
This is `AlgebraicGeometry.ker_appTop_specQuotientToBase` at the scheme of `V`. -/
theorem ker_appTop_specQuotientSiteHom
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    RingHom.ker ((BigFppfOver.toScheme B S hS).map
        (specQuotientSiteHom B S hS V I)).appTop.hom = I :=
  ker_appTop_specQuotientToBase ((BigFppfOver.toScheme B S hS).obj V) I

/-- **A morphism of the big fppf category over `S` to an affine object `V` whose kernel on
global functions contains `I` factors through the closed subscheme of `V` cut out by `I`**, and
the factorisation is over `V`.

The scheme of `V` is affine, so `AlgebraicGeometry.Scheme.ker_le_ker_iff_of_isAffine` turns the
stated inclusion of kernels on global functions into the inclusion of kernel ideal sheaves that
`AlgebraicGeometry.Space.exists_comp_eq_of_ker_le` consumes.  No hypothesis is placed on the
source `T`: it is an arbitrary object of the category, not necessarily affine or
quasi-compact. -/
theorem exists_comp_eq_specQuotientSiteHom
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {T : BigFppfOver B S hS} (k : T ⟶ V)
    (hle : I ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom) :
    ∃ ψ : T ⟶ specQuotientOverSite B S hS V I,
      ψ ≫ specQuotientSiteHom B S hS V I = k :=
  exists_comp_eq_of_ker_le B S hS (specQuotientSiteHom B S hS V I) k inferInstance
    ((Scheme.ker_le_ker_iff_of_isAffine _ _).2
      ((ker_appTop_specQuotientSiteHom B S hS V I).le.trans hle))

/-- **Conversely, a morphism to `V` factoring through the closed subscheme cut out by `I` has
`I` in its kernel on global functions.**  Pulling functions back along the factorisation
followed by the closed immersion kills `I`, because the closed immersion does by
`AlgebraicGeometry.Space.ker_appTop_specQuotientSiteHom`. -/
theorem le_ker_appTop_of_comp_eq_specQuotientSiteHom
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {T : BigFppfOver B S hS} (k : T ⟶ V)
    (ψ : T ⟶ specQuotientOverSite B S hS V I)
    (hψ : ψ ≫ specQuotientSiteHom B S hS V I = k) :
    I ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom := by
  rw [← hψ, Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, ← RingHom.comap_ker]
  exact (ker_appTop_specQuotientSiteHom B S hS V I).ge.trans (Ideal.ker_le_comap _)

/-- **The closed immersion cut out by a finitely generated ideal of functions on an affine object
of the category is locally of finite presentation.**  This is
`AlgebraicGeometry.locallyOfFinitePresentation_specQuotientToBase` at the scheme of `V`. -/
theorem locallyOfFinitePresentation_specQuotientSiteHom
    {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (hI : I.FG) :
    LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (specQuotientSiteHom B S hS V I)) :=
  locallyOfFinitePresentation_specQuotientToBase ((BigFppfOver.toScheme B S hS).obj V) hI

end AffineSiteObject

/-- The scheme of the final object of the big fppf category over `S` is the base, so it is
affine as soon as the base is.  Not found by instance search, which does not unfold the
underlying scheme of the final object. -/
instance isAffine_toScheme_obj_baseTerminal [IsAffine S] :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (baseTerminal B S hS)) :=
  ‹IsAffine S›

/-- **The relative construction at the final object of the category has the same underlying
closed immersion as the construction over the base.**  The scheme of
`AlgebraicGeometry.Space.baseTerminal` is `S`, so
`AlgebraicGeometry.Space.specQuotientSiteHom` there is
`AlgebraicGeometry.specQuotientToBase` of the base — which is, by
`AlgebraicGeometry.Space.inclusion_map_specQuotientOver_hom`, the structure morphism of
`AlgebraicGeometry.Space.specQuotientOver`.  Both sides hold by definition, so the relative
construction is a genuine generalisation of the one over the base and not a differently shaped
object. -/
theorem toScheme_map_specQuotientSiteHom_baseTerminal [IsAffine S] (I : Ideal Γ(S, ⊤)) :
    (BigFppfOver.toScheme B S hS).map
        (specQuotientSiteHom B S hS (baseTerminal B S hS) I) =
      specQuotientToBase S I := rfl

/-- The closed subscheme of the affine base cut out by an ideal of its global functions, read as
a test scheme over the final algebraic space over `S`: that target is terminal, so the structure
morphism is the unique one. -/
def ModuleMapFlatTargetSituation.specQuotientTest [IsAffine S]
    (D : ModuleMapFlatTargetSituation B S hS) (I : Ideal Γ(S, ⊤)) :
    (D.toModuleMapSituation B S hS).SchemesOver :=
  CostructuredArrow.mk
    ((terminalSpace_isTerminal B S hS).from
      ((schemeSpaceFunctor B S hS).obj (specQuotientOver B S hS I)))

end AlgebraicGeometry.Space

end
