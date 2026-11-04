module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleGlobalCohomology
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `𝐆_a` is the associated sheaf of the structure module

Let `X` be a scheme.  On the small étale site of `X` the sheaf `𝐆_a` of [Stacks, Tag 0A3J] —
sections over an étale `X`-scheme `U` being the global functions `Γ(U, 𝒪_U)` — is the associated
abelian sheaf `(𝒪_X)ᵃ` of [Stacks, Tag 03DU] of the structure sheaf of `X` read as a module over
itself.  This is [Stacks, Tag 03P6], the remark the source makes in order to feed `𝐆_a` into the
comparison theorem [Stacks, Tag 03P2]; this file proves it and draws the consequence the remark
is made for: over an **affine** scheme the small étale cohomology of `𝐆_a` vanishes in positive
degree.

The content is a single natural identification.  The associated sheaf
`AlgebraicGeometry.smallEtaleAssociatedSheaf` of a quasi-coherent module `F` has sections
`Γ(T, f^* F)` over an object `f : T ⟶ X` of the site, so at `F = 𝒪_X` the comparison with `𝐆_a`
is the canonical isomorphism `f^* 𝒪_X ≅ 𝒪_T` of modules on `T`, read on global sections and
natural in `T`.  That isomorphism is Mathlib's
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit`, available for schemes as
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`; naturality is its compatibility with
composition, `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq`, together with the
description of the transition maps of the presheaf of [Stacks, Tag 03DS] as pullbacks of
sections, `AlgebraicGeometry.pullbackSectionsMap_eq_comp`.

## Main definitions

* `AlgebraicGeometry.additivePresheafBase` and `AlgebraicGeometry.additiveSheafBase`: `𝐆_a` on
  the small étale site of `X` with its coefficients at `AddCommGrpCat.{u}`, that is, with
  sections over `U` the global functions `Γ(U.left, ⊤)` on the nose and not raised by `ULift`.
* `AlgebraicGeometry.additiveSheafBaseUliftIso`: raising the coefficients gives
  `Stacks.ArtinSchreier.additiveSheaf`, the `𝐆_a` the Artin–Schreier sequence is built from.
* `AlgebraicGeometry.associatedPresheafToAdditivePresheafBase`: the comparison, as a morphism of
  abelian presheaves on the small étale site.
* `AlgebraicGeometry.additiveSheafBaseIsoSmallEtaleAssociatedSheaf`: **[Stacks, Tag 03P6]**, the
  identification `𝐆_a ≅ (𝒪_X)ᵃ` of abelian sheaves on the small étale site of `X`.

## Main results

* `AlgebraicGeometry.pullbackUnitIso_hom_app_top_pullbackSectionsMap`: naturality of the
  comparison, over the whole category of schemes over `X` and not only the small étale site.
* `AlgebraicGeometry.isIso_associatedPresheafToAdditivePresheafBase`: the comparison is an
  isomorphism.
* `AlgebraicGeometry.subsingleton_sheafH_additiveSheafBase_of_isAffine`: **the positive-degree
  small étale cohomology of `𝐆_a` over an affine scheme vanishes.**

## Implementation notes

The coefficient universe is `AddCommGrpCat.{u}`, not the `AddCommGrpCat.{u + 1}` of
`Stacks.ArtinSchreier.additiveSheaf`, and that is forced by the right-hand side:
`AlgebraicGeometry.smallEtaleAssociatedSheaf` lives at the morphism universe `u` of the small
étale site, that being where [Stacks, Tag 03P2] is proved and where Mathlib's
`CategoryTheory.Sheaf.H'` pins its coefficients.  So `𝐆_a` is rebuilt here one universe down
rather than reused, which costs nothing: the sheaf condition is the same representability
argument as `Stacks.ArtinSchreier.isSheaf_additivePresheaf`, with the `Equiv.ulift.symm` factor
dropped from the natural equivalence.  `AlgebraicGeometry.additiveSheafBaseUliftIso` relates the
two, the underlying presheaves differing only by associativity of `⋙`.

Naturality is proved for every morphism of schemes over `X` and not only for the morphisms of the
small étale site, because nothing in it is étale-specific; the presheaf morphism on the site is
its restriction along `AlgebraicGeometry.Scheme.Etale.forget`.  It is stated elementwise, and the
three steps composing it are `have`s of the same shape rather than a `rw` chain: as the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/SectionsPullbackComparison/PullbackSection.lean` record,
`Γ((Scheme.Modules.pullback f).obj M, ⊤)` and the type `AlgebraicGeometry.pullbackSectionsMap`
carries are definitionally but not syntactically equal, and a rewrite whose motive mentions both
is rejected at `implicit` transparency.

`CategoryTheory.IsGrothendieckAbelian.hasExt` has its priority raised for the vanishing theorem,
exactly as in `SmallEtaleGlobalCohomology.lean` and `SmallEtaleQuasiCoherentCohomology.lean`:
`AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology` gives `HasExt.{u + 1}` and is declared later,
so it otherwise wins the search for the étale `Ext` universe, and the statement cannot pin it
because instance search runs before unification with the expected type.  The Zariski-side
`CategoryTheory.HasExt` that
`AlgebraicGeometry.subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup` carries is
`Stacks.Topology.hasExt_sheafOpens`, a theorem and not an instance, supplied here as a local one.

**No `@[stacks]` attribute is attached.**  [Stacks, Tag 03P6] is a remark whose content is the
identification below together with the observation that [Stacks, Tag 03P2] then applies to
`𝐆_a`, and its two halves are separate declarations here; the vanishing half is in any case
`AlgebraicGeometry.subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup` transported
along the identification, not a new argument.

## References

* [Stacks Project, Tag 03P6](https://stacks.math.columbia.edu/tag/03P6)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The presheaf of global functions on the small étale site, at coefficients
`AddCommGrpCat.{u}`.**  Its sections over an étale `X`-scheme `U` are the global functions
`Γ(U.left, 𝒪)` themselves, with no `ULift`: this is `Stacks.ArtinSchreier.additivePresheaf` with
the universe-raising factor of `Stacks.ArtinSchreier.additiveCoefficients` omitted. -/
def additivePresheafBase (X : Scheme.{u}) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} :=
  Stacks.ArtinSchreier.globalFunctionsPresheaf X ⋙ forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat

/-- Sections of `AlgebraicGeometry.additivePresheafBase` over `U` are the global functions on
`U`. -/
theorem additivePresheafBase_obj (X : Scheme.{u}) (U : X.Etale) :
    ToType ((additivePresheafBase X).obj (op U)) = Γ(U.left, ⊤) :=
  rfl

/-- **The underlying presheaf of types of `AlgebraicGeometry.additivePresheafBase` is a sheaf.**
It is the functor of points of the additive group scheme over `X` restricted to the small étale
site, hence a sheaf: that functor is representable and the small étale site is subcanonical over
`Over X`.

This is the proof of `Stacks.ArtinSchreier.isSheaf_forget_additivePresheaf` with the
`Equiv.ulift.symm` factor dropped from the natural equivalence, the coefficients here not being
raised. -/
theorem isSheaf_forget_additivePresheafBase (X : Scheme.{u}) :
    Presieve.IsSheaf X.smallEtaleTopology
      (additivePresheafBase X ⋙ CategoryTheory.forget AddCommGrpCat) := by
  have hrep : Presieve.IsSheaf X.smallEtaleTopology
      ((Scheme.Etale.forget X).op ⋙ globalSectionsAdditive X ⋙ forget GrpCat) :=
    have : (globalSectionsAdditive X ⋙ forget GrpCat).IsRepresentable :=
      (additiveGroupBaseChangeRepresentableBy X).isRepresentable
    Scheme.isSheaf_smallEtale_comp_of_isRepresentable X _
  exact (Presieve.isSheaf_iff_of_nat_equiv
    (P₂ := additivePresheafBase X ⋙ CategoryTheory.forget AddCommGrpCat)
    (fun {_} => Multiplicative.toAdd) (fun _ _ _ _ => rfl)).1 hrep

/-- **`𝐆_a` on the small étale site of a scheme, at coefficients `AddCommGrpCat.{u}`.**  The
sheaf of abelian groups whose sections over an étale `X`-scheme `U` are the global functions
`Γ(U.left, 𝒪)`.

This is `Stacks.ArtinSchreier.additiveSheaf` one coefficient universe down, which is the universe
the quasi-coherent comparison of [Stacks, Tag 03P2] is stated at; the two are related by
`AlgebraicGeometry.additiveSheafBaseUliftIso`. -/
def additiveSheafBase (X : Scheme.{u}) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  ⟨additivePresheafBase X, Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget _ _
    (isSheaf_forget_additivePresheafBase X)⟩

/-- **Raising the coefficients of `AlgebraicGeometry.additiveSheafBase` gives
`Stacks.ArtinSchreier.additiveSheaf`.**

`Stacks.ArtinSchreier.additiveCoefficients.{u, u + 1}` already ends in
`AddCommGrpCat.uliftFunctor.{u + 1, u}`, so the two underlying presheaves differ only by
associativity of `⋙` and the isomorphism is the identity. -/
def additiveSheafBaseUliftIso (X : Scheme.{u}) :
    (CategoryTheory.sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (additiveSheafBase X) ≅ Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} X :=
  (CategoryTheory.fullyFaithfulSheafToPresheaf _ _).preimageIso (CategoryTheory.Iso.refl _)

/-- Equal morphisms of modules have equal components at every open. -/
private theorem modules_hom_app_congr {X : Scheme.{u}} {M N : X.Modules} {φ ψ : M ⟶ N}
    (h : φ = ψ) (U : X.Opens) : φ.app U = ψ.app U :=
  congrArg (fun χ => Scheme.Modules.Hom.app χ U) h

/-- **Pulling a section back is natural in the module.**  For `f : Y ⟶ X` and `φ : M ⟶ N` of
modules on `X`, pulling a section of `M` back to `Y` and then applying `f^* φ` is the same as
applying `φ` first.

This is naturality of the unit of `f^* ⊣ f_*` at `φ`, followed by naturality of `f^* φ` for the
restriction from `f ⁻¹ᵁ U` to `V`. -/
theorem pullbackSectionHom_comp_pullback_map_app {X Y : Scheme.{u}} (f : Y ⟶ X) {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    pullbackSectionHom f M U V h ≫ ((Scheme.Modules.pullback f).map φ).app V =
      φ.app U ≫ pullbackSectionHom f N U V h := by
  have hnat : ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ≫
      ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ U) =
      φ.app U ≫ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U := by
    have h1 := modules_hom_app_congr
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ) U
    simp only [Scheme.Modules.Hom.comp_app, Functor.comp_map, Functor.id_map,
      Scheme.Modules.pushforward_map_app] at h1
    exact h1.symm
  have hres : ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op ≫
      ((Scheme.Modules.pullback f).map φ).app V =
      ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ U) ≫
        ((Scheme.Modules.pullback f).obj N).presheaf.map (homOfLE h).op := by
    ext x
    exact Scheme.Modules.Hom.app_presheaf_map _ (homOfLE h) x
  calc pullbackSectionHom f M U V h ≫ ((Scheme.Modules.pullback f).map φ).app V
      = ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ≫
        ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op ≫
          ((Scheme.Modules.pullback f).map φ).app V := Category.assoc _ _ _
    _ = ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ≫
        ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ U) ≫
          ((Scheme.Modules.pullback f).obj N).presheaf.map (homOfLE h).op :=
        congrArg _ hres
    _ = (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ≫
          ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ U)) ≫
          ((Scheme.Modules.pullback f).obj N).presheaf.map (homOfLE h).op :=
        (Category.assoc _ _ _).symm
    _ = (φ.app U ≫ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U) ≫
          ((Scheme.Modules.pullback f).obj N).presheaf.map (homOfLE h).op :=
        congrArg (fun k => k ≫ _) hnat
    _ = φ.app U ≫ pullbackSectionHom f N U V h := Category.assoc _ _ _

/-- **The transition maps of the presheaf of [Stacks, Tag 03DS] are pullbacks of sections.**  For
a morphism `g` of schemes over `X`, `AlgebraicGeometry.pullbackSectionsMap` pulls a global
section back along `g.left` and then transports it along the comparison of the iterated pullback
with the pullback along the composite.

This is `AlgebraicGeometry.pullbackSectionsMap_eq_comp` with the two comparison components
collected into one morphism of modules, which is the shape
`AlgebraicGeometry.pullbackUnitIso_comparison` is stated at. -/
theorem pullbackSectionsMap_apply_eq {X : Scheme.{u}} (F : X.Modules) {V W : Over X} (g : W ⟶ V)
    (h : (⊤ : W.left.Opens) ≤ g.left ⁻¹ᵁ ⊤)
    (s : Γ((Scheme.Modules.pullback V.hom).obj F, ⊤)) :
    pullbackSectionsMap F g s =
      ((Scheme.Modules.pullbackComp g.left V.hom).hom.app F ≫
          (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F).app ⊤
        (pullbackSectionHom g.left ((Scheme.Modules.pullback V.hom).obj F) ⊤ ⊤ h s) :=
  pullbackSectionsMap_eq_comp F g h s

/-- **The identifications `f^* 𝒪 ≅ 𝒪` are compatible with the comparison of iterated
pullbacks.**  For a morphism `g` of schemes over `X`, transporting along the comparison of
`g.left^* V.hom^* 𝒪_X` with `W.hom^* 𝒪_X` and then identifying with `𝒪_{W.left}` is the same as
identifying `V.hom^* 𝒪_X` with `𝒪_{V.left}` first.

This is `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq` with the comparison moved to
the other side of the equation. -/
theorem pullbackUnitIso_comparison {X : Scheme.{u}} {V W : Over X} (g : W ⟶ V) :
    ((Scheme.Modules.pullbackComp g.left V.hom).hom.app (Scheme.unitModule X) ≫
        (Scheme.Modules.pullbackCongr (Over.w g)).hom.app (Scheme.unitModule X)) ≫
      (Scheme.Modules.pullbackUnitIso W.hom).hom =
      (Scheme.Modules.pullback g.left).map (Scheme.Modules.pullbackUnitIso V.hom).hom ≫
        (Scheme.Modules.pullbackUnitIso g.left).hom := by
  conv_lhs => rw [← Scheme.Modules.pullbackUnitIso_comp_eq g.left V.hom W.hom (Over.w g)]
  simp

/-- **Under `f^* 𝒪_X ≅ 𝒪_Y` the pullback of a global function is its restriction.**  For
`f : Y ⟶ X`, the global section of `f^* 𝒪_X` obtained by pulling a global function on `X` back
corresponds to its image under `AlgebraicGeometry.Scheme.Hom.appTop`.

The identification transposes to `AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit` across
the pullback--pushforward adjunction, by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_homEquiv`, and that morphism acts on sections
as `f` itself.  The restriction from `f ⁻¹ᵁ ⊤` to `⊤` is the identity, those two opens being
equal. -/
theorem pullbackUnitIso_hom_app_top_pullbackSectionHom {X Y : Scheme.{u}} (f : Y ⟶ X)
    (h : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ ⊤) (x : Γ(Scheme.unitModule X, ⊤)) :
    (Scheme.Modules.pullbackUnitIso f).hom.app ⊤
        (pullbackSectionHom f (Scheme.unitModule X) ⊤ ⊤ h x) = f.appTop x := by
  have h1 : (Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (Scheme.unitModule X)).app ⊤ x) =
      (Scheme.Modules.unitToPushforwardUnit f).app ⊤ x := by
    have h0 := Scheme.Modules.pullbackUnitIso_homEquiv f
    rw [Adjunction.homEquiv_unit] at h0
    have h0' := modules_hom_app_congr h0 (⊤ : X.Opens)
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h0'
    exact congr($h0' x)
  have h2 : (Scheme.Modules.pullbackUnitIso f).hom.app ⊤
        (pullbackSectionHom f (Scheme.unitModule X) ⊤ ⊤ h x) =
      (Scheme.unitModule Y).presheaf.map (homOfLE h).op
        ((Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ ⊤)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            (Scheme.unitModule X)).app ⊤ x)) :=
    Scheme.Modules.Hom.app_presheaf_map _ (homOfLE h) _
  have h3 : (Scheme.unitModule Y).presheaf.map (homOfLE h).op = 𝟙 _ :=
    Eq.trans (congrArg (Scheme.unitModule Y).presheaf.map (Subsingleton.elim _ _))
      ((Scheme.unitModule Y).presheaf.map_id (op (⊤ : Y.Opens)))
  exact h2.trans (Eq.trans (congr($h3 _)) h1)

/-- **The comparison `(𝒪_X)ᵃ ⟶ 𝐆_a` is natural**, over the whole category of schemes over `X`.
For a morphism `g : W ⟶ V` of schemes over `X`, identifying the global sections of `V.hom^* 𝒪_X`
with the global functions on `V.left` carries the transition map of the presheaf of
[Stacks, Tag 03DS] to the restriction of functions along `g.left`.

The three steps are `AlgebraicGeometry.pullbackSectionsMap_apply_eq`, which writes the transition
map as a pullback of sections followed by the comparison of iterated pullbacks;
`AlgebraicGeometry.pullbackUnitIso_comparison` and
`AlgebraicGeometry.pullbackSectionHom_comp_pullback_map_app`, which move the identification
`V.hom^* 𝒪_X ≅ 𝒪_{V.left}` past both; and
`AlgebraicGeometry.pullbackUnitIso_hom_app_top_pullbackSectionHom`, which evaluates what is
left. -/
theorem pullbackUnitIso_hom_app_top_pullbackSectionsMap {X : Scheme.{u}} {V W : Over X}
    (g : W ⟶ V) (s : Γ((Scheme.Modules.pullback V.hom).obj (Scheme.unitModule X), ⊤)) :
    (Scheme.Modules.pullbackUnitIso W.hom).hom.app ⊤
        (pullbackSectionsMap (Scheme.unitModule X) g s) =
      g.left.appTop ((Scheme.Modules.pullbackUnitIso V.hom).hom.app ⊤ s) := by
  have h : (⊤ : W.left.Opens) ≤ g.left ⁻¹ᵁ ⊤ := by simp
  have e1 : pullbackSectionsMap (Scheme.unitModule X) g s =
      ((Scheme.Modules.pullbackComp g.left V.hom).hom.app (Scheme.unitModule X) ≫
          (Scheme.Modules.pullbackCongr (Over.w g)).hom.app (Scheme.unitModule X)).app ⊤
        (pullbackSectionHom g.left ((Scheme.Modules.pullback V.hom).obj
          (Scheme.unitModule X)) ⊤ ⊤ h s) :=
    pullbackSectionsMap_apply_eq (Scheme.unitModule X) g h s
  have e2 : (Scheme.Modules.pullbackUnitIso W.hom).hom.app ⊤
        (((Scheme.Modules.pullbackComp g.left V.hom).hom.app (Scheme.unitModule X) ≫
            (Scheme.Modules.pullbackCongr (Over.w g)).hom.app (Scheme.unitModule X)).app ⊤
          (pullbackSectionHom g.left ((Scheme.Modules.pullback V.hom).obj
            (Scheme.unitModule X)) ⊤ ⊤ h s)) =
      (Scheme.Modules.pullbackUnitIso g.left).hom.app ⊤
        (((Scheme.Modules.pullback g.left).map
            (Scheme.Modules.pullbackUnitIso V.hom).hom).app ⊤
          (pullbackSectionHom g.left ((Scheme.Modules.pullback V.hom).obj
            (Scheme.unitModule X)) ⊤ ⊤ h s)) :=
    congr($(modules_hom_app_congr (pullbackUnitIso_comparison g) (⊤ : W.left.Opens)) _)
  have e3 : ((Scheme.Modules.pullback g.left).map
        (Scheme.Modules.pullbackUnitIso V.hom).hom).app ⊤
      (pullbackSectionHom g.left ((Scheme.Modules.pullback V.hom).obj
        (Scheme.unitModule X)) ⊤ ⊤ h s) =
      pullbackSectionHom g.left (Scheme.unitModule V.left) ⊤ ⊤ h
        ((Scheme.Modules.pullbackUnitIso V.hom).hom.app ⊤ s) :=
    congr($(pullbackSectionHom_comp_pullback_map_app g.left
      (Scheme.Modules.pullbackUnitIso V.hom).hom ⊤ ⊤ h) s)
  exact (congrArg ((Scheme.Modules.pullbackUnitIso W.hom).hom.app ⊤) e1).trans
    (e2.trans ((congrArg ((Scheme.Modules.pullbackUnitIso g.left).hom.app ⊤) e3).trans
      (pullbackUnitIso_hom_app_top_pullbackSectionHom g.left h _)))

/-- **The comparison `(𝒪_X)ᵃ ⟶ 𝐆_a` of abelian presheaves on the small étale site of `X`.**  Its
component at an étale `X`-scheme `U` is the identification of the global sections of
`U.hom^* 𝒪_X` with the global functions on `U.left`, and naturality is
`AlgebraicGeometry.pullbackUnitIso_hom_app_top_pullbackSectionsMap`, which holds over all of
`Over X`. -/
def associatedPresheafToAdditivePresheafBase (X : Scheme.{u}) :
    (Scheme.Etale.forget X).op ⋙ quasiCoherentPresheafFunctor X (Scheme.unitModule X) ⟶
      additivePresheafBase X where
  app U := (Scheme.Modules.pullbackUnitIso ((Scheme.Etale.forget X).obj U.unop).hom).hom.app ⊤
  naturality {A B} h := by
    ext s
    exact pullbackUnitIso_hom_app_top_pullbackSectionsMap ((Scheme.Etale.forget X).map h.unop) s

/-- **The comparison is an isomorphism**, each component being the action on sections of the
isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`. -/
theorem isIso_associatedPresheafToAdditivePresheafBase (X : Scheme.{u}) :
    IsIso (associatedPresheafToAdditivePresheafBase X) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  exact inferInstanceAs (IsIso ((Scheme.Modules.pullbackUnitIso
    ((Scheme.Etale.forget X).obj U.unop).hom).hom.app ⊤))

/-- **[Stacks, Tag 03P6]: `𝐆_a` is the associated abelian sheaf of the structure module.**  On
the small étale site of a scheme `X` the sheaf `𝐆_a` of global functions agrees with
`AlgebraicGeometry.smallEtaleAssociatedSheaf` at the structure sheaf of `X` read as a module over
itself.

The two underlying presheaves are compared by
`AlgebraicGeometry.associatedPresheafToAdditivePresheafBase`, so this is
`AlgebraicGeometry.isIso_associatedPresheafToAdditivePresheafBase` carried across
`CategoryTheory.fullyFaithfulSheafToPresheaf`.  `CategoryTheory.asIso` is applied with its
`CategoryTheory.IsIso` argument given explicitly, instance search not finding it at the natural
transformation. -/
def additiveSheafBaseIsoSmallEtaleAssociatedSheaf (X : Scheme.{u}) :
    additiveSheafBase X ≅ smallEtaleAssociatedSheaf X (Scheme.unitModule X) :=
  ((fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
    (X := smallEtaleAssociatedSheaf X (Scheme.unitModule X)) (Y := additiveSheafBase X)
    (@asIso _ _ _ _ (associatedPresheafToAdditivePresheafBase X)
      (isIso_associatedPresheafToAdditivePresheafBase X))).symm

attribute [local instance] Stacks.Topology.hasExt_sheafOpens

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **The small étale cohomology of `𝐆_a` over an affine scheme vanishes in positive degree.**
This is the consequence [Stacks, Tag 03P6] is drawn for: the identification of `𝐆_a` with the
associated sheaf of the structure module turns the comparison
`AlgebraicGeometry.subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup` of
[Stacks, Tag 03P2] into a vanishing statement, whose Zariski-side hypothesis is Serre vanishing
on an affine scheme, [Stacks, Tag 01XB].

Cohomology is transported along `AlgebraicGeometry.additiveSheafBaseIsoSmallEtaleAssociatedSheaf`
by hand rather than through `CategoryTheory.Sheaf.functorH`: `CategoryTheory.Sheaf.H.map` of the
inverse is a retraction of `CategoryTheory.Sheaf.H.map` of the isomorphism, which is all a
`Subsingleton` transfer needs. -/
@[sga "1 XI 6.9" "partial"]
theorem subsingleton_sheafH_additiveSheafBase_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (CategoryTheory.Sheaf.H.{u, u} (additiveSheafBase X) q) := by
  have hvan : Limits.IsZero (Hgroup X.ringCatSheaf ⊤ q (Scheme.unitModule X)) :=
    Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X (Scheme.unitModule X) ⊤
      (isAffineOpen_top X) q hq
  have h0 := subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup X
    (Scheme.unitModule X) q hq hvan
  have key : ∀ y : CategoryTheory.Sheaf.H.{u, u} (additiveSheafBase X) q,
      y = Sheaf.H.map (additiveSheafBaseIsoSmallEtaleAssociatedSheaf X).inv q
        (Sheaf.H.map (additiveSheafBaseIsoSmallEtaleAssociatedSheaf X).hom q y) := by
    intro y
    rw [← Sheaf.H.map_comp_apply, (additiveSheafBaseIsoSmallEtaleAssociatedSheaf X).hom_inv_id,
      Sheaf.H.map_id_apply]
  refine ⟨fun a b => ?_⟩
  rw [key a, key b, h0.elim (Sheaf.H.map _ q a) (Sheaf.H.map _ q b)]

end AlgebraicGeometry

end
