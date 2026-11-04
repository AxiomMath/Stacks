module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorSheafVanishing

/-!
# The sections of a crystalline sheafification over an object of `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `A = (U, T, δ)` of the small
crystalline site `Cris(X/S)`.  The covering families of `Cris(X/S)` are the Zariski coverings of
the ambient divided power schemes, so the restrictions of `A` to the opens of `T` form a functor
`T.Opens ⥤ Cris(X/S)` which is both continuous and cocontinuous
(`...SmallSite.CrystallineThickening.restrictOpenFunctor_isContinuous` and
`..._isCocontinuous`).  Continuity says that restriction along it carries crystalline sheaves to
Zariski sheaves on `T`.  This file supplies what cocontinuity says:

**the restriction to `T` of a crystalline sheafification is the Zariski sheafification of the
restriction.**

Precisely, if `η : P ⟶ Q` is a morphism of abelian presheaves on `Cris(X/S)` which exhibits `Q` as
the sheafification of `P` — that is, `η` is locally injective and locally surjective for the
crystalline topology, which is what the unit `CategoryTheory.toSheafify` is — then the restricted
morphism `P|_T ⟶ Q|_T` is locally injective and locally surjective for the Zariski topology on
`T`, and `Q|_T` is a Zariski sheaf; so `P|_T ⟶ Q|_T` exhibits `Q|_T` as the Zariski
sheafification of `P|_T`.

The sections of `Q|_T` over an open `W` of `T` are by construction the sections of `Q` over the
restricted object `A|_W`, so this does identify the sections of a crystalline sheafification over
the objects `A|_W`: they are the sections of a Zariski sheafification on `T`.

## Main results

Everything below lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`.

* `isLocallyInjective_whiskerLeft_restrictOpenFunctor` and
  `isLocallySurjective_whiskerLeft_restrictOpenFunctor` — restriction to the ambient scheme of an
  object preserves local injectivity and local surjectivity of a morphism of abelian presheaves.
* `w_whiskerLeft_restrictOpenFunctor` — **the identification**: the restriction of a crystalline
  sheafification unit is a Zariski-local equivalence on the ambient scheme, i.e. precomposition
  with it is a bijection on morphisms into every Zariski sheaf.  Together with
  `...CrystallineThickening.isSheaf_restriction` this is the universal property that makes the
  restricted sheaf *the* Zariski sheafification of the restricted presheaf.
* `restrictOpenSheafifyDesc`, `whiskerLeft_comp_restrictOpenSheafifyDesc` and
  `restrictOpenSheafify_hom_ext` — that universal property in usable form: a morphism from the
  restricted presheaf to a Zariski sheaf extends uniquely over the restricted sheafification.
* `restrictOpenSheafifyIso` — **the comparison criterion**: a Zariski sheaf `Z` on `T` receiving a
  locally bijective morphism from the restricted presheaf is isomorphic to the restriction of the
  crystalline sheafification, compatibly with the two morphisms out of the presheaf.  This is the
  shape in which a candidate description of the sections is to be recognised.
* `w_restrictOpen_tensorDifferentialFormsSheaf` — the identification for the coefficient sheaf of
  [Stacks, Tag 07LF]: the restriction to `T` of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` is the Zariski
  sheafification of `W ↦ F(A|_W) ⊗_{Γ(T|_W, 𝒪_T)} Ω^i_{X/S}(A|_W)`, read at the coefficient
  universe `u + 1`.

## What is and is not proved

The identification above is proved, in full, with **no hypothesis on the presheaf** beyond the one
naming the sheafification.  Nothing else is: in particular this file proves no instance of
[Stacks, Tag 07JJ], no surjectivity of transition maps, and places no tag attribute.

This bears on the inputs listed in the module documentation of
`SmallSite/TensorSheafVanishing.lean`, as follows.

The identification of the sections of a crystalline sheafification over an object is available
for a general abelian presheaf as `w_whiskerLeft_restrictOpenFunctor` below and for the tensor
sheaf as `w_restrictOpen_tensorDifferentialFormsSheaf`.

That sheafifying the restricted presheaf tensor product gives the tensor product of those two
sheaves is [Stacks, Tag 05NA], proved as
`Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorSheafificationComparison.lean`, for presheaves
of modules over any site with a sheaf of commutative rings.

What remains for input (1) of [Stacks, Tag 07LF] is therefore a single step: the passage between the `ModuleCat`-valued picture in
which [Stacks, Tag 05NA] is stated and the universe-lifted `AddCommGrpCat.{u + 1}`-valued presheaf
that the coefficient sheaf of [Stacks, Tag 07LF] is a sheafification of.  Only with that does
[Stacks, Tag 01X9] apply, which is the hypothesis of
`vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology` below.  That residue is a
universe bridge, not a piece of mathematics.

Two further inputs are already in the library.

That a tensor product of quasi-coherent modules on an affine is quasi-coherent holds in
general: `AlgebraicGeometry.tensorSheaf_isQuasicoherent`,
[Stacks, Tag 01CE], an instance over any ringed space, with
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite` the form for a
general site.  The sections identification on an affine is
`AlgebraicGeometry.isQuasicoherentTensorSectionsIso` of
`StacksFrontier/AlgebraicGeometry/TildeTensor/Basic.lean`, whose object `specTensorSheaf` is itself
the sheafification of the sectionwise tensor product, so it is that identification and not a
weaker relative of it.

The exterior-power form of [Stacks, Tag 07KM] part (1) is
`Crystalline.GlobalCrystallineSituation.crysDifferentialForms_isLocallyQuasiCoherent` of
`SmallSite/DifferentialFormsLocallyQuasicoherent.lean`, which is general in the degree `i` and
carries no hypothesis, so clause (1) is available beyond `Ω_{X/S}` itself.  Its
consequence for the restriction, `isQuasicoherentOnSite_crysDifferentialFormsRestriction`, is also
general in `i`, and `SmallSite.isQuasicoherentOnSite_tensorRestrictionSheaf` of
`SmallSite/TensorRestrictionVanishing.lean` already proves the Zariski sheafification of the
restricted presheaf tensor product quasi-coherent on hypothesis (1) of [Stacks, Tag 07JN] alone.

One caveat survives all of this and is worth stating, because a plausible-looking version of the
identification is false.  The right-hand side must be the sections of the *sheaves*: `F_T` is a
Zariski sheaf, since `restrictOpenFunctor` is continuous, but the restricted `Ω^i` is only a
presheaf, so a statement of the form `Γ(F_T ⊗ Ω^i|_T) ≅ Γ(F_T) ⊗ Γ(Ω^i|_T)` reading the
*presheaf's* sections on the right does not hold in general.  It must be `Γ((Ω^i|_T)^#)`.

Input (2) still needs the `H¹` argument of `SmallSite/FMapGlobalSurjectivity.lean`, whose
hypothesis is an epimorphism of sheaves of `𝒪_T`-modules with quasi-coherent kernel — the same
quasi-coherence, not the sections identification.  Nothing about input (2) is proved here.

So this file removes the *shared* obstruction the two inputs were stuck behind, and discharges
neither of them.

## Implementation notes

The two Mathlib inputs are `CategoryTheory.Presheaf.isLocallyInjective_whisker` and
`CategoryTheory.Presheaf.isLocallySurjective_whisker`: precomposition with a cocontinuous functor
preserves local injectivity and local surjectivity.  Passing from local bijectivity to the
universal property is `CategoryTheory.GrothendieckTopology.W_of_isLocallyBijective`, which asks
for `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` on the Zariski site of `T` at
the coefficient universe `u + 1`.

That typeclass is *not* available from Mathlib's instances at these universes.  `T.Opens` is a
`Type u` with `Category.{u}`, while the coefficient category is `AddCommGrpCat.{u + 1}`; Mathlib's
`CategoryTheory.Presheaf.isLocallyInjective_toSheafify'` and the `WEqualsLocallyBijective`
instance of `Mathlib/CategoryTheory/Sites/LocallyBijective.lean` both require the concrete
category's carrier to be `Type (max u v)` for the site's own universes, which here means
`Type u`.  The repair is the route already taken in this repository for the associated sheaf of a
module: the Zariski site of a space is essentially small, so
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` transports the
typeclass from a small model where the universes do match.  That is
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`, stated there for a ringed space;
`wEqualsLocallyBijective_ambient` below is its instance for the ambient scheme of an object.
Following the precedent of that file, these are theorems rather than instances and are introduced
with `haveI` where needed, which is why the statements below are phrased through
`CategoryTheory.GrothendieckTopology.W` rather than through the Zariski sheafification functor.

No transparency cliff of the kind the `crisRing`/`structurePresheaf` identification causes is met
here: nothing in this file touches the structure presheaf, the coefficients being abelian groups
throughout.

## References

* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 01X9](https://stacks.math.columbia.edu/tag/01X9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- **The crystalline sheafification unit of an abelian presheaf is locally injective**, at the
coefficient universe `u + 1`.

This is Mathlib's instance `CategoryTheory.Presheaf.IsLocallyInjective` for
`CategoryTheory.toSheafify`, named.  It has to be named.  The import closure of this file contains
`sheafifyLocallyInjectiveWide` and `sheafifyLocallySurjectiveWide` of
`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/RegularIdealSheaves.lean`, whose coefficient
universe is `max u v w` for a universe `w` appearing nowhere else in their statements; instance
search reaches those first and is then left with the unsolvable constraint
`max (u + 1) ?w = u + 1`.  Going through
`CategoryTheory.GrothendieckTopology.W_toSheafify` leaves no universe undetermined. -/
theorem isLocallyInjective_toSheafify
    (P : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallyInjective (smallTopology S) (toSheafify (smallTopology S) P) :=
  GrothendieckTopology.W.isLocallyInjective ((smallTopology S).W_toSheafify P)

/-- **The crystalline sheafification unit of an abelian presheaf is locally surjective**, at the
coefficient universe `u + 1`.  See `isLocallyInjective_toSheafify` for why this is named rather
than inferred. -/
theorem isLocallySurjective_toSheafify
    (P : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallySurjective (smallTopology S) (toSheafify (smallTopology S) P) :=
  GrothendieckTopology.W.isLocallySurjective ((smallTopology S).W_toSheafify P)

namespace CrystallineThickening

variable {P Q : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}

/-- **On the Zariski site of the ambient scheme of an object of `Cris(X/S)`, the morphisms of
abelian presheaves which become isomorphisms after sheafification are exactly the locally
bijective ones**, at the coefficient universe `u + 1`.

This is `Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective` for the ringed space
underlying the ambient scheme.  It is a theorem rather than an instance, following the precedent
of that declaration: Mathlib's own instance would need the coefficient category's carrier to live
in the site's universe `u`, and the fix is a transport along the essential smallness of the site
rather than a wider instance. -/
theorem wEqualsLocallyBijective_ambient (A : CrystallineThickening S) :
    (Opens.grothendieckTopology A.obj.thickening.target.scheme).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u + 1}
    A.obj.thickening.target.scheme.toLocallyRingedSpace.toRingedSpace

/-- **Restriction to the ambient scheme of an object of `Cris(X/S)` preserves local injectivity**
of a morphism of abelian presheaves, because the restrictions of the object to the opens of its
ambient scheme form a cocontinuous functor. -/
theorem isLocallyInjective_whiskerLeft_restrictOpenFunctor (A : CrystallineThickening S)
    (η : P ⟶ Q) [Presheaf.IsLocallyInjective (smallTopology S) η] :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (Functor.whiskerLeft (restrictOpenFunctor A).op η) :=
  have := restrictOpenFunctor_isCocontinuous A
  Presheaf.isLocallyInjective_whisker
    (Opens.grothendieckTopology A.obj.thickening.target.scheme) (smallTopology S)
    (restrictOpenFunctor A) η

/-- **Restriction to the ambient scheme of an object of `Cris(X/S)` preserves local
surjectivity** of a morphism of abelian presheaves, because the restrictions of the object to the
opens of its ambient scheme form a cocontinuous functor. -/
theorem isLocallySurjective_whiskerLeft_restrictOpenFunctor (A : CrystallineThickening S)
    (η : P ⟶ Q) [Presheaf.IsLocallySurjective (smallTopology S) η] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (Functor.whiskerLeft (restrictOpenFunctor A).op η) :=
  have := restrictOpenFunctor_isCocontinuous A
  Presheaf.isLocallySurjective_whisker
    (Opens.grothendieckTopology A.obj.thickening.target.scheme) (smallTopology S)
    (restrictOpenFunctor A) η

/-- **The restriction to the ambient scheme of an object of `Cris(X/S)` of a crystalline
sheafification is the Zariski sheafification of the restriction.**

Let `η : P ⟶ Q` be a morphism of abelian presheaves on `Cris(X/S)` which is locally injective and
locally surjective for the crystalline topology — the unit `CategoryTheory.toSheafify` of the
sheafification of `P` is such a morphism, and so is any morphism exhibiting `Q` as a
sheafification of `P`.  Then for every object `A` with ambient divided power scheme `T`, the
restricted morphism `P|_T ⟶ Q|_T` is a local equivalence for the Zariski topology on `T`:
precomposition with it is a bijection

`Hom(Q|_T, Z) ≃ Hom(P|_T, Z)`

for every Zariski sheaf `Z` on `T`.  Since `Q|_T` is itself a Zariski sheaf whenever `Q` is a
crystalline sheaf, by `...CrystallineThickening.isSheaf_restriction`, this is exactly the
universal property of the Zariski sheafification of `P|_T`, and it identifies the sections of the
crystalline sheafification over the restricted objects `A|_W` with the sections of a Zariski
sheafification on `T`.

No hypothesis on `P` or `Q` is carried beyond the two naming `η` as a sheafification morphism. -/
theorem w_whiskerLeft_restrictOpenFunctor (A : CrystallineThickening S) (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective (smallTopology S) η]
    [Presheaf.IsLocallySurjective (smallTopology S) η] :
    (Opens.grothendieckTopology A.obj.thickening.target.scheme).W
      (Functor.whiskerLeft (restrictOpenFunctor A).op η) :=
  have := wEqualsLocallyBijective_ambient A
  have := isLocallyInjective_whiskerLeft_restrictOpenFunctor A η
  have := isLocallySurjective_whiskerLeft_restrictOpenFunctor A η
  GrothendieckTopology.W_of_isLocallyBijective _ _

section Desc

variable (A : CrystallineThickening S) (η : P ⟶ Q)
  [Presheaf.IsLocallyInjective (smallTopology S) η]
  [Presheaf.IsLocallySurjective (smallTopology S) η]
  {Z : (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}

/-- **A morphism from the restricted presheaf to a Zariski sheaf extends over the restricted
sheafification.**  This is the universal property of
`w_whiskerLeft_restrictOpenFunctor` read as a construction; the extension is unique, by
`restrictOpenSheafify_hom_ext`, and factors the given morphism, by
`whiskerLeft_comp_restrictOpenSheafifyDesc`. -/
def restrictOpenSheafifyDesc
    (hZ : Presheaf.IsSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) Z)
    (ψ : (restrictOpenFunctor A).op ⋙ P ⟶ Z) :
    (restrictOpenFunctor A).op ⋙ Q ⟶ Z :=
  (ObjectProperty.isLocal.homEquiv (w_whiskerLeft_restrictOpenFunctor A η) Z hZ).symm ψ

/-- `restrictOpenSheafifyDesc` factors the morphism it extends. -/
@[reassoc]
theorem whiskerLeft_comp_restrictOpenSheafifyDesc
    (hZ : Presheaf.IsSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) Z)
    (ψ : (restrictOpenFunctor A).op ⋙ P ⟶ Z) :
    Functor.whiskerLeft (restrictOpenFunctor A).op η ≫ restrictOpenSheafifyDesc A η hZ ψ = ψ :=
  (ObjectProperty.isLocal.homEquiv (w_whiskerLeft_restrictOpenFunctor A η) Z hZ).apply_symm_apply ψ

/-- **Two morphisms from the restricted sheafification to a Zariski sheaf which agree on the
restricted presheaf are equal.** -/
theorem restrictOpenSheafify_hom_ext
    (hZ : Presheaf.IsSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) Z)
    {θ₁ θ₂ : (restrictOpenFunctor A).op ⋙ Q ⟶ Z}
    (h : Functor.whiskerLeft (restrictOpenFunctor A).op η ≫ θ₁ =
      Functor.whiskerLeft (restrictOpenFunctor A).op η ≫ θ₂) :
    θ₁ = θ₂ :=
  (w_whiskerLeft_restrictOpenFunctor A η Z hZ).1 h

/-- **The comparison criterion for the sections of a crystalline sheafification.**  A Zariski
sheaf `Z` on the ambient scheme `T` of an object `A`, together with a morphism `ψ` from the
restriction `P|_T` which is locally injective and locally surjective for the Zariski topology, is
isomorphic to the restriction `Q|_T` of the crystalline sheafification, compatibly with `ψ` and
with the restricted sheafification morphism: see
`whiskerLeft_comp_restrictOpenSheafifyIso_hom`.

Both `Q|_T` and `Z` are Zariski sheafifications of `P|_T`, so the extension of `ψ` provided by
`restrictOpenSheafifyDesc` is a local equivalence between two sheaves, hence an isomorphism.
The hypotheses carried are exactly: `η` names `Q` as the crystalline sheafification of `P`, `hQ`
says `Q` is a crystalline sheaf, `hZ` says `Z` is a Zariski sheaf, and `ψ` is Zariski-locally
bijective. -/
def restrictOpenSheafifyIso
    (hZ : Presheaf.IsSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) Z)
    (hQ : Presheaf.IsSheaf (smallTopology S) Q)
    (ψ : (restrictOpenFunctor A).op ⋙ P ⟶ Z)
    [Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) ψ]
    [Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) ψ] :
    (restrictOpenFunctor A).op ⋙ Q ≅ Z :=
  haveI := wEqualsLocallyBijective_ambient A
  haveI : IsIso (restrictOpenSheafifyDesc A η hZ ψ) := by
    refine (ObjectProperty.isLocal_iff_isIso _ (restrictOpenSheafifyDesc A η hZ ψ)
      (isSheaf_restriction A Q hQ) hZ).1
      (MorphismProperty.of_precomp _ _ _ (w_whiskerLeft_restrictOpenFunctor A η) ?_)
    rw [whiskerLeft_comp_restrictOpenSheafifyDesc]
    exact GrothendieckTopology.W_of_isLocallyBijective _ ψ
  asIso (restrictOpenSheafifyDesc A η hZ ψ)

/-- The isomorphism `restrictOpenSheafifyIso` is compatible with the two morphisms out of the
restricted presheaf. -/
@[reassoc]
theorem whiskerLeft_comp_restrictOpenSheafifyIso_hom
    (hZ : Presheaf.IsSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) Z)
    (hQ : Presheaf.IsSheaf (smallTopology S) Q)
    (ψ : (restrictOpenFunctor A).op ⋙ P ⟶ Z)
    [Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) ψ]
    [Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) ψ] :
    Functor.whiskerLeft (restrictOpenFunctor A).op η ≫
        (restrictOpenSheafifyIso A η hZ hQ ψ).hom = ψ :=
  whiskerLeft_comp_restrictOpenSheafifyDesc A η hZ ψ

end Desc

end CrystallineThickening

/-! ### The coefficient sheaf of Stacks 07LF -/

/-- **The abelian presheaf whose crystalline sheafification is
`...SmallSite.tensorDifferentialFormsSheaf F i`**: the underlying abelian presheaf of the tensor
product `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of presheaves of modules, lifted to the coefficient universe
`u + 1`.  Its sections over an object `(U, T, δ)` are
`F(U, T, δ) ⊗_{Γ(T, 𝒪_T)} Ω^i_{X/S}(U, T, δ)` by
`...SmallSite.tensorDifferentialForms_obj`. -/
abbrev tensorDifferentialFormsPresheaf (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (PresheafOfModules.toPresheaf _).obj
      (tensorDifferentialForms
        (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- `...SmallSite.tensorDifferentialFormsSheaf F i` is the crystalline sheafification of
`tensorDifferentialFormsPresheaf F i`. -/
theorem tensorDifferentialFormsSheaf_obj (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    (tensorDifferentialFormsSheaf F i).obj =
      sheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i) :=
  rfl

/-- **The restriction to the ambient scheme of an object of the coefficient sheaf of
[Stacks, Tag 07LF] is a Zariski sheafification.**  For a sheaf of `𝒪_{X/S}`-modules `F`, an
`i : ℕ` and an object `A = (U, T, δ)` of `Cris(X/S)`, the restriction to `T` of the sheafification
morphism of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` is a local equivalence for the Zariski topology on `T`; so
the restriction to `T` of `...SmallSite.tensorDifferentialFormsSheaf F i` is the Zariski
sheafification of `W ↦ F(A|_W) ⊗_{Γ(T|_W, 𝒪_T)} Ω^i_{X/S}(A|_W)`, read at the coefficient
universe `u + 1`.

No hypothesis on `F` is carried.  `...CrystallineThickening.restrictOpenSheafifyIso` turns this
into an identification of that restriction with any Zariski sheaf on `T` admitting a locally
bijective morphism from the restricted presheaf tensor product. -/
theorem w_restrictOpen_tensorDifferentialFormsSheaf
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) (A : CrystallineThickening S) :
    (Opens.grothendieckTopology A.obj.thickening.target.scheme).W
      (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i))) := by
  have := isLocallyInjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  have := isLocallySurjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  exact CrystallineThickening.w_whiskerLeft_restrictOpenFunctor A _

/-- **The conclusion of [Stacks, Tag 07JJ] for `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`, reduced to a statement
about Zariski sheaves on affine schemes.**  Suppose that for every object `A = (U, T, δ)` of
`Cris(X/S)` whose ambient divided power scheme `T` is affine there is a Zariski sheaf `Z` of
abelian groups on `T`, together with a morphism `ψ` from the restriction to `T` of the presheaf
tensor product `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` which is Zariski-locally injective and Zariski-locally
surjective, whose Zariski Čech complex on the basic opens of a standard open cover of `T` has
vanishing positive-degree homology.  Then `...SmallSite.Vanishing07JJ` holds for
`...SmallSite.tensorDifferentialFormsSheaf F i`.

This is the chain the module documentation describes, assembled: the identification
`...CrystallineThickening.restrictOpenSheafifyIso` turns such a `Z` into the restriction of the
tensor sheaf to `T`, so the two Čech complexes are isomorphic;
`...SmallSite.hasStandardCechVanishing_of_isZero_ambientCechHomology` and
`...SmallSite.vanishing07JJ_of_hasStandardCechVanishing` do the rest.

**No tag attribute is placed**, the hypothesis `h` not being a hypothesis of the tag, and nothing
here proves `h`.  What `h` asks for is [Stacks, Tag 01X9] on an affine scheme, and the way to get
it is to take `Z` quasi-coherent.  Its two factors are quasi-coherent — the restriction `F_T` by
hypothesis (1) of [Stacks, Tag 07JN] and the associated sheaf of the restriction of `Ω^i_{X/S}` by
the exterior-power form of [Stacks, Tag 07KM] part (1), which the library does not have for
`i ≠ 1` — and that sheafifying the restricted presheaf tensor product gives the tensor product of
those two sheafifications is [Stacks, Tag 05NA], which the library does have; see the module
documentation for what the three remaining pieces are. -/
theorem vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)
    (h : ∀ A : CrystallineThickening S, IsAffine A.obj.thickening.target.scheme →
      ∃ (Z : (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
        (ψ : (CrystallineThickening.restrictOpenFunctor A).op ⋙
          tensorDifferentialFormsPresheaf F i ⟶ Z),
        Presheaf.IsSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) Z ∧
        Presheaf.IsLocallyInjective
          (Opens.grothendieckTopology A.obj.thickening.target.scheme) ψ ∧
        Presheaf.IsLocallySurjective
          (Opens.grothendieckTopology A.obj.thickening.target.scheme) ψ ∧
        ∀ {n : ℕ} (g : Fin n → Γ(A.obj.thickening.target.scheme, ⊤)),
          PrimeSpectrum.IsStandardOpenCoverOfSpectrum g → ∀ p : ℕ, 0 < p →
            IsZero (((cechComplexFunctor
              fun j ↦ A.obj.thickening.target.scheme.basicOpen (g j)).obj Z).homology p)) :
    Vanishing07JJ S (tensorDifferentialFormsSheaf F i) := by
  refine vanishing07JJ_of_hasStandardCechVanishing _
    (hasStandardCechVanishing_of_isZero_ambientCechHomology _ ?_)
  intro A hA n g hg p hp
  obtain ⟨Z, ψ, hZ, hinj, hsurj, hvan⟩ := h A hA
  have := isLocallyInjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  have := isLocallySurjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  exact (hvan g hg p hp).of_iso (HomologicalComplex.homologyMapIso
    ((cechComplexFunctor fun j ↦ A.obj.thickening.target.scheme.basicOpen (g j)).mapIso
      (CrystallineThickening.restrictOpenSheafifyIso A
        (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)) hZ
        (tensorDifferentialFormsSheaf F i).property ψ)) p)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
