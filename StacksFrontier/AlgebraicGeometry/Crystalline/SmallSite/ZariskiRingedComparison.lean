module

public import Mathlib.Data.ZMod.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiDirectImage

/-!
# The ring comparison along `u_{X/S}`, and `Ru_{X/S, *}` of a module

Fix a global crystalline situation `(p, (S, I, γ), X)`.  The morphism of topoi
`u_{X/S} : (X/S)_cris ⟶ Sh(X_Zar)` of [Stacks, Tag 07IL] is carried on abelian sheaves by
`Crystalline.GlobalCrystallineSituation.SmallSite.zariskiDirectImage` and derived there.  This
file asks what it takes to carry it on *modules*, i.e. to make `u_{X/S}` a morphism of **ringed**
topoi `((X/S)_cris, 𝒪_{X/S}) ⟶ (X_Zar, 𝒪_X)`, and it records three things: the ring comparison
that exists, the ring comparison that does **not** exist, and `Ru_{X/S, *}` of a sheaf of
`𝒪_{X/S}`-modules in the coefficients in which it does exist.

## The direction of the ring comparison

A morphism of ringed topoi `((X/S)_cris, 𝒪_{X/S}) ⟶ (X_Zar, 𝒪_X)` is a structure map
`𝒪_X ⟶ u_{X/S, *}𝒪_{X/S}`, equivalently `u_{X/S}^{-1}𝒪_X ⟶ 𝒪_{X/S}`.  The canonical map between
these two sheaves of rings runs the *other* way.  An object `(U, T, δ)` of `Cris(X/S)` has
`𝒪_{X/S}(U, T, δ) = Γ(T, 𝒪_T)` and `(u_{X/S}^{-1}𝒪_X)(U, T, δ) = Γ(U, 𝒪_U)`, and the canonical
ring map between them is restriction along the closed immersion `U ↪ T`,

  `Γ(T, 𝒪_T) ⟶ Γ(U, 𝒪_U)`,  i.e.  `𝒪_{X/S} ⟶ u_{X/S}^{-1}𝒪_X`,

which is `structureToZariskiInverseImage` below.  A map in the opposite direction would be a
*ring-theoretic splitting* of every divided power thickening in the site, and no such thing
exists: already for `p` a prime, `U = Spec 𝔽_p` and `T = Spec ℤ/p²` there is no unital ring map
`𝔽_p ⟶ ℤ/p²`, which is `isEmpty_ringHom_zmod_sq`.  So `u_{X/S}` is **not** a morphism of ringed
topoi over `𝒪_X`, and `Ru_{X/S, *}` of an `𝒪_{X/S}`-module is **not** a complex of
`𝒪_X`-modules.  This matches the literature: `Ru_{X/S, *}𝒪_{X/S}` is computed by a de Rham
complex (the shape of [Stacks, Tag 07LM]), whose differentials are not `𝒪_X`-linear.

What the requirement *is*, made checkable, is `ZariskiStructureMap`: a morphism of presheaves of
rings `u_{X/S}^{-1}𝒪_X ⟶ 𝒪_{X/S}`.  `ZariskiStructureMap.liftRingHom` extracts from one, at each
object `(U, T, δ)`, a ring map `Γ(X, U) ⟶ Γ(T, 𝒪_T)`, and
`ZariskiStructureMap.liftRingHom_comp_comparison` says that a map compatible with the canonical
comparison splits the thickening on sections.  Nothing below assumes such a map exists.

## The second, independent obstruction: the ring universe

Even the *statement* `𝒪_X ⟶ u_{X/S, *}𝒪_{X/S}` cannot be written at the universes this chapter
works in, and this is why the requirement above is phrased in its adjoint form.  The direct image
of a presheaf of rings along `u_{X/S}` is the right Kan extension along `(forgetToOpens S).op`
([Stacks, Tag 00XK]), computed by limits indexed by `StructuredArrow (op V) (forgetToOpens S).op`,
whose objects lie in `Type (u + 1)` and whose morphisms lie in `Type u`.  So
`(forgetToOpens S).op.HasPointwiseRightKanExtension (crisRing S)` needs
`CategoryTheory.Limits.HasLimitsOfSize.{u, u + 1} RingCat.{u}`, i.e. `max u (u + 1) ≤ u`, which is
false.  The abelian side escapes this only because its coefficients are already
`AddCommGrpCat.{u + 1}`.

This is a universe obstruction, not a `RingCat`-versus-`CommRingCat` one: the structure sheaf of
the small crystalline site is available in both flavours —
`Crystalline.GlobalCrystallineSituation.SmallSite.structureSheaf` is `RingCat.{u}`-valued and
`Crystalline.GlobalCrystallineSituation.SmallSite.commStructureSheaf` is `CommRingCat.{u}`-valued,
both with sections in `Type u` — and the failing instance is the same for either.  Raising the
ring coefficients to `RingCat.{u + 1}` would repair this obstruction and leave the previous one
untouched; it would also replace `𝒪_{X/S}` by a universe lift of itself, which the module
documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ModuleCohomology.lean` already rejects.

The comparison of this file therefore lives at the level of presheaves of rings on `Cris(X/S)`,
where no Kan extension is involved and the ring universe stays `u`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `zariskiInverseImageCommRing` and `zariskiInverseImageRing` — `u_{X/S}^{-1}𝒪_X` as a presheaf of
  commutative rings, respectively of rings, on `Cris(X/S)`: restriction along the forgetful
  functor of [Stacks, Tag 07IH].
* `opensFreeStructureIso` — the sections of `𝒪_{X/S}` over the trivial thickening `(V, V, ∅)` of
  [Stacks, Tag 07I8] are the sections of `𝒪_X` over `V`.
* `structureToZariskiInverseImage` and `crisRingToZariskiInverseImage` — **the ring comparison
  `𝒪_{X/S} ⟶ u_{X/S}^{-1}𝒪_X`**, in commutative rings and in rings.
* `ZariskiStructureMap` and `HasZariskiStructureMap` — the data, and the assertion of its
  existence, that would make `u_{X/S}` a morphism of ringed topoi over `𝒪_X`.
* `moduleZariskiDirectImage`, `moduleHigherZariskiDirectImage` and
  `moduleDerivedZariskiDirectImage` — `u_{X/S, *}F`, `R^j u_{X/S, *}F` and `Ru_{X/S, *}F` for `F`
  a sheaf of `𝒪_{X/S}`-modules at the universe the chapter's crystal and quasi-coherence
  predicates are stated at, valued in abelian sheaves on `X_Zar`.

## Main results

* `structureToZariskiInverseImage_app` — the component of the ring comparison at `(U, T, δ)` is
  restriction along the counit `(U, T, δ)` of [Stacks, Tag 07I8], read through
  `opensFreeStructureIso`.
* `ZariskiStructureMap.liftRingHom` — a structure map gives a ring map `Γ(X, U) ⟶ Γ(T, 𝒪_T)` for
  every object of the site, and `ZariskiStructureMap.liftRingHom_comp_comparison` — a compatible
  one splits the thickening on sections.
* `isEmpty_ringHom_zmod_sq` — there is no unital ring map `ℤ/n ⟶ ℤ/n²` for `n > 1`; the ring-level
  reason the structure map does not exist.
* `moduleZariskiDirectImage_obj` and `moduleDerivedZariskiDirectImage_obj` — these functors are the
  abelian direct images of
  `Crystalline.GlobalCrystallineSituation.SmallSite.abelianSheaf F`, by `rfl`, so they are
  statements about the very abelian sheaf the chapter's abelian-valued assertions use.
* `moduleDerivedGlobalSectionsIso` — [Stacks, Tag 015M] for a module:
  `RΓ(Cris(X/S), F) ≅ RΓ(X_Zar, Ru_{X/S, *}F)`.

## What is and is not proved

What is proved is that the canonical ring comparison along `u_{X/S}` exists in the direction
`𝒪_{X/S} ⟶ u_{X/S}^{-1}𝒪_X` and is a morphism of presheaves of commutative rings and of rings;
that the opposite direction, which is what a morphism of ringed topoi over `𝒪_X` would be, is a
ring-theoretic splitting of every divided power thickening in the site; that no such splitting
exists at the level of rings, by `isEmpty_ringHom_zmod_sq`; and that `u_{X/S, *}F`,
`R^j u_{X/S, *}F` and `Ru_{X/S, *}F` are defined for `F` a sheaf of `𝒪_{X/S}`-modules, valued in
abelian sheaves on `X_Zar` and in `D⁺(Ab(X_Zar))`, and factor derived crystalline global sections
as [Stacks, Tag 015M].  Every statement is unconditional: no declaration here carries a hypothesis
beyond the global crystalline situation itself and the choice of derived category models.

What is **not** proved here:

* **The direct image of `𝒪_{X/S}`-modules as `𝒪_X`-modules is not constructed, and cannot be.**
  The two obstructions are set out above: the structure map `𝒪_X ⟶ u_{X/S, *}𝒪_{X/S}` does not
  exist, and the sheaf `u_{X/S, *}𝒪_{X/S}` cannot even be formed at the ring universe `u`.

  The *second* of those two is only about the universe, and it is now lifted:
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ZariskiModuleDirectImage.lean` forms
  `u_{X/S, *}𝒪^{ULift}_{X/S}` at `RingCat.{u + 1}`, where the Kan extension exists, and builds
  `u_{X/S, *}`, `R^j u_{X/S, *}` and `Ru_{X/S, *}` of a sheaf of `𝒪_{X/S}`-modules **as sheaves
  of modules** over it, with source the chapter's own `ModuleSheaf S`.  The *first* obstruction
  is untouched and remains decisive: nothing there is an `𝒪_X`-module, and the module-valued
  functors of this file, which land in abelian sheaves, stay the right reading whenever the
  `𝒪_X`-side is what is wanted.  The machinery that would consume the structure map is present
  in the library —
  `Stacks.SheafOfModules.pushforwardCocontinuous` builds `f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` from a
  cocontinuous functor of sites and a map `f^♯ : 𝒪_Y ⟶ {}_sw 𝒪_X` — so what is missing is exactly
  its `f^♯`, which is `ZariskiStructureMap` here.  Nothing is weakened to get around this: the
  module-valued statements below are about the *abelian* sheaf underlying a module, which is what
  they say.
* **`isEmpty_ringHom_zmod_sq` is a statement about rings, not about a crystalline situation.**  It
  exhibits the ring-theoretic obstruction, and `ZariskiStructureMap.liftRingHom` exhibits that the
  structure map would have to overcome it at every object; what is not formalized is a global
  crystalline situation containing the thickening `Spec 𝔽_p ↪ Spec ℤ/p²` as an object, which is
  what a Lean refutation of `HasZariskiStructureMap` for a specific `S` would need.  So
  `HasZariskiStructureMap` is stated and left open rather than refuted.
* **No comparison of `u_{X/S, *}` with the restriction to trivial thickenings** is made.  The
  trivial thickenings of [Stacks, Tag 07I8] assemble into `opensFree`, the left adjoint of
  `forgetToOpens`, and restriction along `(opensFree S).op` is a second functor
  `Sh(Cris(X/S)) ⟶ Sh(X_Zar)`; it is the *left* adjoint of `u_{X/S}^{-1}` rather than its right
  adjoint, so it is `u_{X/S, !}` and not `u_{X/S, *}`, and it is not what this file is about.  It
  enters only through `opensFreeStructureIso`, which identifies the sections of `𝒪_{X/S}` over a
  trivial thickening.
* **No de Rham computation of `Ru_{X/S, *}` is performed here**, so [Stacks, Tag 07LM] is not
  stated in this file.  The leading
  assertion of that tag at `F = 𝒪_{X/S}` is proved, as
  `...SmallSite.isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamPlusTruncation` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Vanishing07LMProof.lean` — and in
  `D⁺(Ab(X_Zar))`, of abelian sheaves, which is this bullet's point: nothing reads that
  isomorphism as one of complexes of `𝒪_X`-modules, for want of the structure map discussed
  above.
* Nothing here carries a `@[stacks]` attribute.  The assertions of [Stacks, Tag 07IL] about the
  forgetful functor and the morphism of topoi are carried in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ZariskiToposMorphism.lean`, and this module
  only adds coefficients to that morphism.

## References

* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 07I8](https://stacks.math.columbia.edu/tag/07I8)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe w w' w'' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### `u_{X/S}^{-1}𝒪_X` as a presheaf of rings on `Cris(X/S)` -/

/-- **The inverse image `u_{X/S}^{-1}𝒪_X` of the structure sheaf of `X`, as a presheaf of
commutative rings on the small crystalline site.**  Its sections over an object `(U, T, δ)` are
the sections `Γ(X, U)` of `𝒪_X` over the open image of `U` in `X`, the forgetful functor of
[Stacks, Tag 07IH] being `(U, T, δ) ↦ U`.  No sheafification is involved: this is restriction
along `(forgetToOpens S).op`, which is the inverse image of [Stacks, Tag 00XO] read on
presheaves. -/
def zariskiInverseImageCommRing : (CrystallineThickening S)ᵒᵖ ⥤ CommRingCat.{u} :=
  (forgetToOpens S).op ⋙ S.X.presheaf

/-- The sections of `u_{X/S}^{-1}𝒪_X` over an object `(U, T, δ)` of `Cris(X/S)` are the sections
of `𝒪_X` over the open image of `U` in `X`. -/
@[simp]
theorem zariskiInverseImageCommRing_obj (A : CrystallineThickening S) :
    (zariskiInverseImageCommRing S).obj (op A) = Γ(S.X, (forgetToOpens S).obj A) := rfl

/-- **The inverse image `u_{X/S}^{-1}𝒪_X`, as a presheaf of rings**, the coefficients in which the
structure sheaf `Crystalline.GlobalCrystallineSituation.SmallSite.structureSheaf` of the small
crystalline site is stated. -/
def zariskiInverseImageRing : (CrystallineThickening S)ᵒᵖ ⥤ RingCat.{u} :=
  zariskiInverseImageCommRing S ⋙ forget₂ CommRingCat.{u} RingCat.{u}

/-! ### The ring comparison `𝒪_{X/S} ⟶ u_{X/S}^{-1}𝒪_X` -/

/-- **The sections of `𝒪_{X/S}` over the trivial thickening `(V, V, ∅)` are the sections of `𝒪_X`
over `V`.**  The ambient scheme of the object `(V, V, ∅)` of [Stacks, Tag 07I8] attached to an
open `V` of `X` is the open subscheme `V` itself, so this is the identification of the global
sections of an open subscheme with the sections of the ambient scheme over that open,
`AlgebraicGeometry.Scheme.restrictFunctorΓ`. -/
def opensFreeStructureIso : (opensFree S).op ⋙ structurePresheaf S ≅ S.X.presheaf :=
  Scheme.restrictFunctorΓ

/-- **The ring comparison `𝒪_{X/S} ⟶ u_{X/S}^{-1}𝒪_X` of the morphism of topoi
[Stacks, Tag 07IL].**  Its component at an object `(U, T, δ)` of `Cris(X/S)` is restriction along
the closed immersion `U ↪ T`, that is the ring map `Γ(T, 𝒪_T) ⟶ Γ(X, U)`; it is read off the
counit of the adjunction `opensFree ⊣ forgetToOpens` of [Stacks, Tag 07I8], whose component at
`(U, T, δ)` is the morphism `(U, U, ∅) ⟶ (U, T, δ)` given by that closed immersion.

This is the direction in which the comparison exists.  The opposite direction, which is what a
morphism of ringed topoi `((X/S)_cris, 𝒪_{X/S}) ⟶ (X_Zar, 𝒪_X)` would be, is
`ZariskiStructureMap`, and it does not exist; see the module documentation. -/
def structureToZariskiInverseImage :
    structurePresheaf S ⟶ zariskiInverseImageCommRing S where
  app A := (structurePresheaf S).map ((opensFreeForgetAdjunction S).counit.app A.unop).op ≫
    (opensFreeStructureIso S).hom.app (op ((forgetToOpens S).obj A.unop))
  naturality A B f := by
    have hε : (opensFree S).map ((forgetToOpens S).map f.unop) ≫
          (opensFreeForgetAdjunction S).counit.app A.unop =
        (opensFreeForgetAdjunction S).counit.app B.unop ≫ f.unop :=
      (opensFreeForgetAdjunction S).counit.naturality f.unop
    have h : f ≫ ((opensFreeForgetAdjunction S).counit.app B.unop).op =
        ((opensFreeForgetAdjunction S).counit.app A.unop).op ≫
          ((opensFree S).map ((forgetToOpens S).map f.unop)).op :=
      Quiver.Hom.unop_inj hε.symm
    have hiso := (opensFreeStructureIso S).hom.naturality ((forgetToOpens S).op.map f)
    simp only [Functor.comp_obj, Functor.comp_map, Functor.op_obj, Functor.op_map,
      Quiver.Hom.unop_op] at hiso
    change (structurePresheaf S).map f ≫
        (structurePresheaf S).map ((opensFreeForgetAdjunction S).counit.app B.unop).op ≫
          (opensFreeStructureIso S).hom.app (op ((forgetToOpens S).obj B.unop)) =
      ((structurePresheaf S).map ((opensFreeForgetAdjunction S).counit.app A.unop).op ≫
          (opensFreeStructureIso S).hom.app (op ((forgetToOpens S).obj A.unop))) ≫
        S.X.presheaf.map ((forgetToOpens S).map f.unop).op
    rw [Category.assoc, ← hiso, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, h]

/-- The component of the ring comparison `𝒪_{X/S} ⟶ u_{X/S}^{-1}𝒪_X` at an object of
`Cris(X/S)`, by definition. -/
theorem structureToZariskiInverseImage_app (A : (CrystallineThickening S)ᵒᵖ) :
    (structureToZariskiInverseImage S).app A =
      (structurePresheaf S).map ((opensFreeForgetAdjunction S).counit.app A.unop).op ≫
        (opensFreeStructureIso S).hom.app (op ((forgetToOpens S).obj A.unop)) := rfl

/-- **The component of the ring comparison at `(U, T, δ)` is restriction along the morphism of
ambient schemes of the counit `(U, U, ∅) ⟶ (U, T, δ)`**, that is along the closed immersion
`U ↪ T`, followed by the identification of `Γ(U, 𝒪_U)` with `Γ(X, U)`.  This is the concrete form
of `structureToZariskiInverseImage`. -/
theorem structureToZariskiInverseImage_app_appTop (A : CrystallineThickening S) :
    (structureToZariskiInverseImage S).app (op A) =
      ((opensFreeForgetAdjunction S).counit.app A).hom.targetHom.hom.appTop ≫
        (opensFreeStructureIso S).hom.app (op ((forgetToOpens S).obj A)) := rfl

/-- **The ring comparison `𝒪_{X/S} ⟶ u_{X/S}^{-1}𝒪_X` read in rings**, the coefficients of
`Crystalline.GlobalCrystallineSituation.SmallSite.structureSheaf`. -/
def crisRingToZariskiInverseImage : crisRing S ⟶ zariskiInverseImageRing S :=
  Functor.whiskerRight (structureToZariskiInverseImage S) (forget₂ CommRingCat.{u} RingCat.{u})

/-! ### What a morphism of ringed topoi over `𝒪_X` would require -/

/-- **The data that would make `u_{X/S}` a morphism of ringed topoi
`((X/S)_cris, 𝒪_{X/S}) ⟶ (X_Zar, 𝒪_X)`**: a morphism of presheaves of commutative rings
`u_{X/S}^{-1}𝒪_X ⟶ 𝒪_{X/S}` on the small crystalline site.

This is the adjoint form of the structure map `𝒪_X ⟶ u_{X/S, *}𝒪_{X/S}`, and the adjoint form is
the one written because the direct image `u_{X/S, *}𝒪_{X/S}` cannot be formed at the ring universe
`u` at all: see the module documentation.  No such morphism exists; `liftRingHom` says what one
would give at each object of the site, and `isEmpty_ringHom_zmod_sq` says why that cannot be
had. -/
abbrev ZariskiStructureMap := zariskiInverseImageCommRing S ⟶ structurePresheaf S

/-- **The assertion that `u_{X/S}` is a morphism of ringed topoi over `𝒪_X`.**  Stated, not
proved, and not expected to be provable; see the module documentation. -/
def HasZariskiStructureMap : Prop := Nonempty (ZariskiStructureMap S)

namespace ZariskiStructureMap

variable {S}

/-- **A structure map lifts sections of `𝒪_X` to sections of the ambient scheme.**  At an object
`(U, T, δ)` of `Cris(X/S)` it is a ring map `Γ(X, U) ⟶ Γ(T, 𝒪_T)`, going against the closed
immersion `U ↪ T`.  This is the checkable requirement that the module-valued direct image along
`u_{X/S}` comes down to. -/
def liftRingHom (ψ : ZariskiStructureMap S) (A : CrystallineThickening S) :
    Γ(S.X, (forgetToOpens S).obj A) ⟶ Γ(A.obj.thickening.target.scheme, ⊤) :=
  ψ.app (op A)

/-- **A structure map compatible with the canonical comparison splits every divided power
thickening of the site on sections.**  Compatibility is that the composite
`u_{X/S}^{-1}𝒪_X ⟶ 𝒪_{X/S} ⟶ u_{X/S}^{-1}𝒪_X` be the identity; the conclusion is that at each
object `(U, T, δ)` the ring map `Γ(X, U) ⟶ Γ(T, 𝒪_T)` of `liftRingHom` is a section of the
restriction `Γ(T, 𝒪_T) ⟶ Γ(X, U)` along the closed immersion `U ↪ T`. -/
theorem liftRingHom_comp_comparison (ψ : ZariskiStructureMap S)
    (h : ψ ≫ structureToZariskiInverseImage S = 𝟙 _) (A : CrystallineThickening S) :
    ψ.liftRingHom A ≫ (structureToZariskiInverseImage S).app (op A) = 𝟙 _ :=
  congr_app h (op A)

end ZariskiStructureMap

/-- **There is no unital ring map `ℤ/n ⟶ ℤ/n²` for `n > 1`.**  A ring map sends the natural number
`n`, which is zero in `ℤ/n`, to `n` in `ℤ/n²`, where it is nonzero.

This is the ring-level reason a `ZariskiStructureMap` does not exist: for `p` a prime,
`Spec 𝔽_p ↪ Spec ℤ/p²` is a divided power thickening over `(Spec ℤ_{(p)}, (p), γ)`, so it is an
object `(U, T, δ)` of a small crystalline site, and `ZariskiStructureMap.liftRingHom` would supply
a ring map `𝔽_p ⟶ ℤ/p²` there. -/
theorem isEmpty_ringHom_zmod_sq {n : ℕ} (hn : 1 < n) : IsEmpty (ZMod n →+* ZMod (n ^ 2)) := by
  refine ⟨fun f => ?_⟩
  have h : ((n : ℕ) : ZMod (n ^ 2)) = 0 := by
    rw [← map_natCast f n, ZMod.natCast_self, map_zero]
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd (zero_lt_one.trans hn) h)
    (not_le.2 (by simpa [pow_two] using Nat.lt_mul_iff_one_lt_left (zero_lt_one.trans hn) |>.2 hn))

/-! ### `u_{X/S, *}` and `Ru_{X/S, *}` of a sheaf of `𝒪_{X/S}`-modules -/

/-- **The direct image `u_{X/S, *}F` of a sheaf of `𝒪_{X/S}`-modules**, valued in abelian sheaves
on the small Zariski site of `X`.  The module is taken at the universe at which the chapter's
crystal and quasi-coherence predicates are stated; the functor lifts it with
`Crystalline.GlobalCrystallineSituation.SmallSite.moduleULift`, passes to the underlying abelian
sheaf and applies the abelian direct image.

The target is abelian sheaves and not `𝒪_X`-modules, and that is not a weakening: `u_{X/S}` is not
a morphism of ringed topoi over `𝒪_X`, so there is no `𝒪_X`-module structure to carry.  See the
module documentation. -/
def moduleZariskiDirectImage :
    SheafOfModules.{u} (structureSheaf S) ⥤ Sheaf (opensTopology S) AddCommGrpCat.{u + 1} :=
  moduleULift S ⋙ toAbelianSheaf S ⋙ zariskiDirectImage S

/-- **`u_{X/S, *}F` is the abelian direct image of the abelian sheaf
`Crystalline.GlobalCrystallineSituation.SmallSite.abelianSheaf F`**, the one the chapter's
abelian-valued assertions are about, by `rfl`. -/
theorem moduleZariskiDirectImage_obj (F : SheafOfModules.{u} (structureSheaf S)) :
    (moduleZariskiDirectImage S).obj F = (zariskiDirectImage S).obj (abelianSheaf F) := rfl

/-- **The higher direct image `R^j u_{X/S, *}F` of a sheaf of `𝒪_{X/S}`-modules**, valued in
abelian sheaves on the small Zariski site of `X`. -/
def moduleHigherZariskiDirectImage (j : ℤ)
    [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] :
    SheafOfModules.{u} (structureSheaf S) ⥤ Sheaf (opensTopology S) AddCommGrpCat.{u + 1} :=
  moduleULift S ⋙ toAbelianSheaf S ⋙ higherZariskiDirectImage S j

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- **The derived direct image `Ru_{X/S, *}F ∈ D⁺(Ab(X_Zar))` of a sheaf of `𝒪_{X/S}`-modules**,
the object the distinguished triangle of [Stacks, Tag 07Q9] is written in terms of. -/
def moduleDerivedZariskiDirectImage :
    SheafOfModules.{u} (structureSheaf S) ⥤
      DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) :=
  moduleULift S ⋙ toAbelianSheaf S ⋙ derivedZariskiDirectImage S

/-- **`Ru_{X/S, *}F` is the derived abelian direct image of
`Crystalline.GlobalCrystallineSituation.SmallSite.abelianSheaf F`**, by `rfl`. -/
theorem moduleDerivedZariskiDirectImage_obj (F : SheafOfModules.{u} (structureSheaf S)) :
    (moduleDerivedZariskiDirectImage S).obj F =
      (derivedZariskiDirectImage S).obj (abelianSheaf F) := rfl

/-- **[Stacks, Tag 015M] for a sheaf of `𝒪_{X/S}`-modules:
`RΓ(Cris(X/S), F) ≅ RΓ(X_Zar, Ru_{X/S, *}F)`.**  This is the abelian factorization
`...SmallSite.derivedGlobalSectionsIsoDerivedZariskiDirectImageObj` of
`SmallSite/ZariskiDirectImage.lean`, at the abelian sheaf underlying `F`. -/
def moduleDerivedGlobalSectionsIso [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
    (F : SheafOfModules.{u} (structureSheaf S)) :
    (derivedGlobalSections S).obj (abelianSheaf F) ≅
      (derivedZariskiGlobalSectionsFunctor S).obj
        ((moduleDerivedZariskiDirectImage S).obj F) :=
  (derivedGlobalSectionsIsoDerivedZariskiDirectImageObj S).app (abelianSheaf F)

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
