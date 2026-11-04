module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleCohomologyColimit
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiSeparated.AffineOneHypercover
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.GlobalSectionsOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.GlobalSectionsOfColimitOfFiniteSitesHypercover

/-!
# Stacks 09YQ: the colimit of étale cohomology at quasi-compact quasi-separated levels

This module carries the declarations that extend
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimit`,
which is the base text, unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.EtaleCohomology.QcqsLimitCohomology

open AlgebraicGeometry Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem

section Opens

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine open of an object of the small affine etale site is again an object of it.** The
structure morphism is the open immersion followed by that of the ambient object: etale because an
open immersion is etale and etale morphisms compose, with source in the big site because it is an
open subscheme of a scheme that is (`Stacks.EtaleCohomology.contains_toScheme_obj`).

`objOfAffineOpen` is the case of an affine open of `S` itself. This version is what the Cech step
needs: the objects of the site are affine, but the preimage in one of them of an affine open of
`S` is only an open of an affine scheme, so it has to be covered by affine opens of that object
before it can be used inside the site.

The ambient object is given by a bare etale morphism `p : Y ⟶ S` rather than by an object of the
site, because the consumer of the *separated* case takes its affine opens inside a
quasi-compact separated etale `Y` which is not affine and so is not an object of the small affine
etale site at all. An object of either site supplies its structure morphism; nothing else is
used. -/
def objOfAffineOpenOver {Y : Scheme.{u}} (hY : B.Contains Y) (p : Y ⟶ S)
    [AlgebraicGeometry.Etale p] (O : Y.Opens) (hO : AlgebraicGeometry.IsAffineOpen O) :
    AlgebraicGeometry.SmallAffineEtale B S hS :=
  haveI : IsAffine (O : Scheme.{u}) := hO
  ⟨mkObj B hS (O : Scheme.{u}) (O.ι ≫ p)
      (Scheme.size_lt_of_isOpenImmersion O.ι hY) inferInstance,
    by change AlgebraicGeometry.IsAffine (O : Scheme.{u}); infer_instance⟩

/-- The structure morphism of the object attached to an affine open of `Y`. -/
@[simp]
lemma structMap_objOfAffineOpenOver {Y : Scheme.{u}} (hY : B.Contains Y) (p : Y ⟶ S)
    [AlgebraicGeometry.Etale p] (O : Y.Opens) (hO : AlgebraicGeometry.IsAffineOpen O) :
    structMap B S hS (objOfAffineOpenOver B S hS hY p O hO) = O.ι ≫ p :=
  hom_mkObj B hS _ _ _ _

/-- The open immersion of an affine open of `Z` into `Z`, as a morphism of the site. -/
def toAmbient (Z : AlgebraicGeometry.SmallAffineEtale B S hS)
    (O : ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) :
    objOfAffineOpenOver B S hS (contains_toScheme_obj B hS Z.obj)
      (structMap B S hS Z) O hO ⟶ Z :=
  ObjectProperty.homMk (mkHom B hS O.ι (by
    show O.ι ≫ structMap B S hS Z =
      structMap B S hS (objOfAffineOpenOver B S hS (contains_toScheme_obj B hS Z.obj)
        (structMap B S hS Z) O hO)
    rw [structMap_objOfAffineOpenOver]))

/-- **An affine open of `Z` landing inside an affine open `U` of `S` maps to the object of `U`.**
This is the morphism of the site that the one-hypercover condition asks for, and it is where
`CategoryTheory.Scheme.Hom.resLE` does the work: a morphism into an open immersion factors
through it. -/
def toAffineOpenOfLE (Z : AlgebraicGeometry.SmallAffineEtale B S hS)
    (O : ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (U : S.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) (e : O ≤ (structMap B S hS Z) ⁻¹ᵁ U) :
    objOfAffineOpenOver B S hS (contains_toScheme_obj B hS Z.obj) (structMap B S hS Z) O hO ⟶
      objOfAffineOpen B S hS U hU :=
  ObjectProperty.homMk (mkHom B hS ((structMap B S hS Z).resLE U O e) (by
    show (structMap B S hS Z).resLE U O e ≫ structMap B S hS (objOfAffineOpen B S hS U hU) =
      structMap B S hS (objOfAffineOpenOver B S hS (contains_toScheme_obj B hS Z.obj)
        (structMap B S hS Z) O hO)
    rw [structMap_objOfAffineOpen, structMap_objOfAffineOpenOver, Scheme.Hom.resLE_comp_ι]))

/-- A point of `Z` whose image lies in an open `W` of `S` lies in an affine open of `Z` carried
into `W`. -/
private theorem exists_affineOpen_le_preimage_of_mem
    (Z : AlgebraicGeometry.SmallAffineEtale B S hS) (W : S.Opens)
    (x : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z)
    (hx : (structMap B S hS Z).base x ∈ W) :
    ∃ O : ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).Opens,
      AlgebraicGeometry.IsAffineOpen O ∧ x ∈ O ∧ O ≤ (structMap B S hS Z) ⁻¹ᵁ W := by
  obtain ⟨-, ⟨O, hO, rfl⟩, hxO, hle⟩ :=
    ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).isBasis_affineOpens
      |>.exists_subset_of_mem_open (show x ∈ ((structMap B S hS Z) ⁻¹ᵁ W : _) from hx)
        ((structMap B S hS Z) ⁻¹ᵁ W).isOpen
  exact ⟨O, hO, hxO, hle⟩

/-- **The affine opens of an object subordinate to a cover of `S` cover that object.** For a
family of opens of `S` covering `S` and an object `Z` of the small affine etale site, every point
of `Z` lies in an affine open of `Z` carried into some member of the family. -/
theorem exists_affineOpen_le_preimage {κ : Type*} (U : κ → S.Opens)
    (hUtop : (⨆ k, U k) = ⊤) (Z : AlgebraicGeometry.SmallAffineEtale B S hS)
    (x : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z) :
    ∃ (k : κ) (O : ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).Opens),
      AlgebraicGeometry.IsAffineOpen O ∧ x ∈ O ∧ O ≤ (structMap B S hS Z) ⁻¹ᵁ (U k) := by
  have hmem : (structMap B S hS Z).base x ∈ (⨆ k, U k : S.Opens) := by
    rw [hUtop]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  obtain ⟨O, hO, hxO, hle⟩ := exists_affineOpen_le_preimage_of_mem B S hS Z (U k) x hk
  exact ⟨k, O, hO, hxO, hle⟩

/-- **The covering family of an object subordinate to a family of affine opens of `S`.** If the
structure morphism of `Z` carries every point into some member of the family, then `Z` has a
covering family -- an honest presieve of the small affine etale precoverage -- each of whose
members maps to the object of some member.

This is the core of both one-hypercover obligations, and it needs no cardinal reasoning:
`mem_smallAffineEtale_precoverage_iff` discharges the bound `#I₀ ≤ B.coveringBound` once and
for all,
so what is left is finiteness -- from quasi-compactness of the affine `Z` -- together with joint
surjectivity and "an open immersion is etale". Note that the index `ι` of the family of opens
need not be finite: the covering family is indexed by finitely many *points* of `Z`. -/
theorem exists_presieve_subordinate {ι : Type u} (V : ι → S.Opens)
    (hVaff : ∀ m, AlgebraicGeometry.IsAffineOpen (V m))
    (Z : AlgebraicGeometry.SmallAffineEtale B S hS)
    (hZ : ∀ x, ∃ m, (structMap B S hS Z).base x ∈ V m) :
    ∃ R : Presieve Z, R ∈ AlgebraicGeometry.SmallAffineEtale.precoverage B S hS Z ∧
      ∀ ⦃Y : AlgebraicGeometry.SmallAffineEtale B S hS⦄ (q : Y ⟶ Z), R q →
        ∃ m, Nonempty (Y ⟶ objOfAffineOpen B S hS (V m) (hVaff m)) := by
  classical
  obtain ⟨mm, OO, hOOaff, hOOmem, hOOle⟩ :
      ∃ (mm : _ → ι) (OO : ∀ x, ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).Opens),
        (∀ x, AlgebraicGeometry.IsAffineOpen (OO x)) ∧ (∀ x, x ∈ OO x) ∧
          ∀ x, OO x ≤ (structMap B S hS Z) ⁻¹ᵁ (V (mm x)) := by
    have hpt : ∀ x, ∃ (m : ι)
        (O : ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).Opens),
        AlgebraicGeometry.IsAffineOpen O ∧ x ∈ O ∧ O ≤ (structMap B S hS Z) ⁻¹ᵁ (V m) := by
      intro x
      obtain ⟨m, hm⟩ := hZ x
      obtain ⟨O, hO, hxO, hle⟩ := exists_affineOpen_le_preimage_of_mem B S hS Z (V m) x hm
      exact ⟨m, O, hO, hxO, hle⟩
    choose mm OO h1 h2 h3 using hpt
    exact ⟨mm, OO, h1, h2, h3⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (OO x : Set ↥((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z)))
    (fun x => (OO x).isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hOOmem x⟩
  let E : PreZeroHypercover.{u + 1} Z :=
    { I₀ := ULift.{u + 1} {x // x ∈ t}
      X := fun i => objOfAffineOpenOver B S hS (contains_toScheme_obj B hS Z.obj)
        (structMap B S hS Z) (OO i.down.1) (hOOaff i.down.1)
      f := fun i => toAmbient B S hS Z (OO i.down.1) (hOOaff i.down.1) }
  refine ⟨E.presieve₀, ?_, ?_⟩
  · refine (mem_smallAffineEtale_precoverage_iff B S hS Z _).mpr
      ⟨Precoverage.ofArrows_mem_finite _ _, ?_⟩
    rw [← PreZeroHypercover.presieve₀_map]
    refine (Scheme.presieve₀_mem_precoverage_iff _).mpr ⟨fun x => ?_, fun i => ?_⟩
    · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
      exact ⟨ULift.up ⟨y, hy⟩, ⟨x, hxy⟩, rfl⟩
    · show AlgebraicGeometry.Etale (OO i.down.1).ι
      infer_instance
  · rintro Y q ⟨i⟩
    exact ⟨mm i.down.1, ⟨toAffineOpenOfLE B S hS Z (OO i.down.1) (hOOaff i.down.1)
      (V (mm i.down.1)) (hVaff _) (hOOle i.down.1)⟩⟩

/-- **A family of affine opens covering `S` covers the terminal sheaf of the small affine etale
site.** The first obligation of `IsTopOneHypercoverOn`. -/
theorem coversTop_objOfAffineOpen {κ : Type u} (U : κ → S.Opens)
    (hUaff : ∀ k, AlgebraicGeometry.IsAffineOpen (U k)) (hUtop : (⨆ k, U k) = ⊤) :
    (AlgebraicGeometry.SmallAffineEtale.topology B S hS).CoversTop
      (fun k => objOfAffineOpen B S hS (U k) (hUaff k)) := by
  intro Z
  obtain ⟨R, hR, hfac⟩ := exists_presieve_subordinate B S hS U hUaff Z (fun x => by
    have hx : (structMap B S hS Z).base x ∈ (⨆ k, U k : S.Opens) := by rw [hUtop]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx)
  refine (AlgebraicGeometry.SmallAffineEtale.topology B S hS).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hR)
  rintro Y g ⟨W, p, r, hr, rfl⟩
  obtain ⟨k, ⟨b⟩⟩ := hfac r hr
  exact ⟨k, ⟨p ≫ b⟩⟩

/-- A morphism of the site to the object of an affine open `U` factors the structure morphism
through `U.ι`. -/
private theorem toScheme_map_comp_ι (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    (Y : AlgebraicGeometry.SmallAffineEtale B S hS) (h : Y ⟶ objOfAffineOpen B S hS U hU) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map h ≫ U.ι = structMap B S hS Y := by
  rw [← structMap_objOfAffineOpen B S hS U hU]
  exact toScheme_map_comp_structMap B S hS h

/-- **An object of the site receives at most one morphism to the object of an affine open of `S`.**
The structure morphism of `objOfAffineOpen` is the open immersion, hence a monomorphism, and
morphisms of the site are determined by their underlying morphisms of schemes. -/
theorem hom_ext_objOfAffineOpen (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    (Y : AlgebraicGeometry.SmallAffineEtale B S hS)
    (f g : Y ⟶ objOfAffineOpen B S hS U hU) : f = g := by
  exact (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map_injective
    ((cancel_mono U.ι).1
      ((toScheme_map_comp_ι B S hS U hU Y f).trans (toScheme_map_comp_ι B S hS U hU Y g).symm))

/-- **A covering sieve subordinate to a family of affine opens of `S` through which `Z` factors.**
Every member of the sieve maps to the object of some member of the family. -/
theorem exists_covering_sieve_subordinate {ι : Type u} (V : ι → S.Opens)
    (hVaff : ∀ m, AlgebraicGeometry.IsAffineOpen (V m))
    (Z : AlgebraicGeometry.SmallAffineEtale B S hS)
    (hZ : ∀ x, ∃ m, (structMap B S hS Z).base x ∈ V m) :
    ∃ T : Sieve Z, T ∈ AlgebraicGeometry.SmallAffineEtale.topology B S hS Z ∧
      ∀ ⦃Y : AlgebraicGeometry.SmallAffineEtale B S hS⦄ (q : Y ⟶ Z), T.arrows q →
        ∃ (m : ι) (_ : Y ⟶ objOfAffineOpen B S hS (V m) (hVaff m)), True := by
  obtain ⟨R, hR, hfac⟩ := exists_presieve_subordinate B S hS V hVaff Z hZ
  refine ⟨Sieve.generate R, Precoverage.generate_mem_toGrothendieck hR, ?_⟩
  rintro Y q ⟨W, p, r, hr, rfl⟩
  obtain ⟨m, ⟨b⟩⟩ := hfac r hr
  exact ⟨m, p ≫ b, trivial⟩

/-- The inclusion of one affine open of `S` in another, as a morphism of the site. -/
def leOfAffineOpen (V U : S.Opens) (hV : AlgebraicGeometry.IsAffineOpen V)
    (hU : AlgebraicGeometry.IsAffineOpen U) (e : V ≤ U) :
    objOfAffineOpen B S hS V hV ⟶ objOfAffineOpen B S hS U hU :=
  ObjectProperty.homMk (mkHom B hS (S.homOfLE e) (by
    show S.homOfLE e ≫ structMap B S hS (objOfAffineOpen B S hS U hU) =
      structMap B S hS (objOfAffineOpen B S hS V hV)
    rw [structMap_objOfAffineOpen, structMap_objOfAffineOpen, Scheme.homOfLE_ι]))

/-- **An isomorphism over `S` of the underlying schemes is an isomorphism of the site.** The
small affine etale site is a full subcategory of the schemes over `S`, so a morphism of it is
nothing but a morphism of schemes commuting with the structure morphisms, and an isomorphism of
those is an isomorphism of the site.

This is the lifting step of the `hlev` hypothesis of
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`. That
hypothesis is about the transition images `(D.u a).obj (W k)` of a fixed family, which geometry
pins down only as a fibre product -- `transition_isPullback` -- while the family a level supplies
of its own accord consists of the objects of the preimage opens, pinned by
`AlgebraicGeometry.isPullback_morphismRestrict`. Two pullbacks of one cospan are isomorphic
(`CategoryTheory.IsPullback.isoIsPullback`), and that isomorphism is one of SCHEMES; this carries
it into the site, where
`Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn.of_iso` can consume it.

`CategoryTheory.Functor.preimageIso` does not apply: it wants a fully faithful functor, and
`AlgebraicGeometry.SmallAffineEtale.toScheme` is faithful but not full -- a morphism of the site
is a morphism of schemes *over `S`*, which is exactly the hypothesis `hφ` here. The composite to
`Over S` is fully faithful, but it and its `Full` instance are private to
`Stacks.EtaleCohomology.AffineEtaleSites`. -/
def isoOfSchemeIso {W W' : AlgebraicGeometry.SmallAffineEtale B S hS}
    (φ : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj W ≅
      (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj W')
    (hφ : φ.hom ≫ structMap B S hS W' = structMap B S hS W) : W ≅ W' where
  hom := ObjectProperty.homMk (mkHom B hS φ.hom (by
    show φ.hom ≫ structMap B S hS W' = structMap B S hS W
    exact hφ))
  inv := ObjectProperty.homMk (mkHom B hS φ.inv (by
    show φ.inv ≫ structMap B S hS W = structMap B S hS W'
    rw [← hφ, ← Category.assoc, φ.inv_hom_id, Category.id_comp]))
  hom_inv_id := (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map_injective (by
    simp only [Functor.map_comp, Functor.map_id]
    exact φ.hom_inv_id)
  inv_hom_id := (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map_injective (by
    simp only [Functor.map_comp, Functor.map_id]
    exact φ.inv_hom_id)

/-- The underlying isomorphism of schemes of `isoOfSchemeIso` is the given one. -/
@[simp]
theorem toScheme_map_isoOfSchemeIso_hom {W W' : AlgebraicGeometry.SmallAffineEtale B S hS}
    (φ : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj W ≅
      (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj W')
    (hφ : φ.hom ≫ structMap B S hS W' = structMap B S hS W) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map
      (isoOfSchemeIso B S hS φ hφ).hom = φ.hom :=
  rfl

/-- The structure morphism of `Z` lands in an affine open `U` of `S` whenever the site has a
morphism from `Z` to the object of `U`. -/
theorem base_mem_of_hom (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    (Z : AlgebraicGeometry.SmallAffineEtale B S hS) (f : Z ⟶ objOfAffineOpen B S hS U hU)
    (x : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z) :
    (structMap B S hS Z).base x ∈ U := by
  rw [← toScheme_map_comp_ι B S hS U hU Z f]
  exact ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map f |>.base x).2

/-- **An object whose structure morphism is the base change of an affine open is the object of
the preimage of that open.** If the structure morphism of `W` sits in a fibre-product square over
`U.ι` and `g : S ⟶ T`, then `W` is isomorphic, in the site, to the object attached to the affine
open `g ⁻¹ᵁ U` of `S`.

This is the object half of the `hlev` hypothesis of
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`, stated with
no reference to a system of sites: what a system supplies about a transition image is exactly a
square of this shape, `transition_isPullback`, and what a level supplies of its own accord is the
object of the preimage open. The two are identified here once, so that the application to a system
has only to produce the square.

The proof is three named facts and no computation. The preimage open is itself a fibre product
over the same cospan, `AlgebraicGeometry.isPullback_morphismRestrict`; two fibre products over one
cospan are isomorphic, `CategoryTheory.IsPullback.isoIsPullback`, and that isomorphism commutes
with the projections to `S`, `CategoryTheory.IsPullback.isoIsPullback_hom_snd`, which is precisely
being an isomorphism over `S` -- so `Stacks.EtaleCohomology.QcqsLimitCohomology.isoOfSchemeIso`
carries it into the site. -/
noncomputable def isoObjOfPreimage {T : Scheme.{u}} (g : S ⟶ T) [IsAffineHom g] (U : T.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) (W : AlgebraicGeometry.SmallAffineEtale B S hS)
    (p : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj W ⟶ U.toScheme)
    (hsq : IsPullback p (structMap B S hS W) U.ι g) :
    W ≅ objOfAffineOpen B S hS (g ⁻¹ᵁ U) (hU.preimage g) :=
  isoOfSchemeIso B S hS
    (hsq.isoIsPullback _ _ (AlgebraicGeometry.isPullback_morphismRestrict g U))
    (by
      rw [structMap_objOfAffineOpen]
      exact hsq.isoIsPullback_hom_snd _ _ (AlgebraicGeometry.isPullback_morphismRestrict g U))

/-- **An object whose structure morphism is the base change of an affine open of an etale
`Y ⟶ T` is the object of the preimage of that open in the base change of `Y`.** The relative form
of `isoObjOfPreimage`, with the ambient `T` replaced by an etale `Y` over it.

This is what the Cech step of Stacks 09YQ over a quasi-compact *separated* etale object `Y` of a
level needs, and `isoObjOfPreimage` does not supply it: the objects of the datum there are affine
opens of `Y` and not of the level, so their transition images are preimages inside the base change
`Y'` of `Y` and not inside the base change of the level.

The proof is the pasting of two fibre-product squares and nothing else. The preimage of `O` in
`Y'` is a fibre product of `O.ι` and `q` (`AlgebraicGeometry.isPullback_morphismRestrict`), and
`Y'` is a fibre product of `p` and `g` (the hypothesis `hYsq`); pasting them vertically
(`CategoryTheory.IsPullback.paste_vert`) exhibits the object of the preimage open as a fibre
product of `O.ι ≫ p` and `g`, which is the square `hsq` assumed of `W`. Two fibre products of one
cospan are isomorphic over the base, and
`Stacks.EtaleCohomology.QcqsLimitCohomology.isoOfSchemeIso` carries that into the site. -/
noncomputable def isoObjOfPreimageOver {T : Scheme.{u}} (g : S ⟶ T) [IsAffineHom g]
    {Y : Scheme.{u}} (p : Y ⟶ T) [AlgebraicGeometry.Etale p]
    {Y' : Scheme.{u}} (hY' : B.Contains Y') (p' : Y' ⟶ S) [AlgebraicGeometry.Etale p']
    (q : Y' ⟶ Y) [IsAffineHom q] (hYsq : IsPullback q p' p g)
    (O : Y.Opens) (hO : AlgebraicGeometry.IsAffineOpen O)
    (W : AlgebraicGeometry.SmallAffineEtale B S hS)
    (r : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj W ⟶ O.toScheme)
    (hsq : IsPullback r (structMap B S hS W) (O.ι ≫ p) g) :
    W ≅ objOfAffineOpenOver B S hS hY' p' (q ⁻¹ᵁ O) (hO.preimage q) :=
  isoOfSchemeIso B S hS
    (hsq.isoIsPullback _ _
      ((AlgebraicGeometry.isPullback_morphismRestrict q O).paste_vert hYsq))
    (by
      rw [structMap_objOfAffineOpenOver]
      exact hsq.isoIsPullback_hom_snd _ _
        ((AlgebraicGeometry.isPullback_morphismRestrict q O).paste_vert hYsq))

/-- **The preimage of a one-hypercover datum along an affine morphism is one.** The affineness of
the preimages is `AlgebraicGeometry.IsAffineOpen.preimage`, which is what `IsAffineHom` says; the
three lattice identities are that `AlgebraicGeometry.Scheme.Hom.preimage` preserves `⊤`, `⊓` and
`⨆`.

This is the geometric half of the `hlev` hypothesis of
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`: the
transitions of the system of Stacks 0EYL are affine, so a datum chosen at one level restricts to
a datum at every lower level and `isTopOneHypercover_hc` applies there. What it does NOT supply is
the identification of the transition *image* of an object with the object of the preimage open;
that is an isomorphism, not an equality, and is what
`Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn.of_iso` is for.

Nothing here is about sites, so it would sit more naturally beside
`Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens`; it is here because that file
imports only `Mathlib.AlgebraicGeometry.Limits` and so does not have `IsAffineHom` in scope, and
it has three importers, which is not a place to add an import edge for tidiness. -/
theorem preimage_oneHypercover_data {X Y : Scheme.{u}} (g : X ⟶ Y) [IsAffineHom g]
    {κ ν : Type u} (U : κ → Y.Opens) (V : κ → κ → ν → Y.Opens)
    (hUaff : ∀ k, AlgebraicGeometry.IsAffineOpen (U k))
    (hVaff : ∀ k l m, AlgebraicGeometry.IsAffineOpen (V k l m))
    (hUtop : (⨆ k, U k) = ⊤) (hVsup : ∀ k l, (⨆ m, V k l m) = U k ⊓ U l) :
    (∀ k, AlgebraicGeometry.IsAffineOpen (g ⁻¹ᵁ U k)) ∧
      (∀ k l m, AlgebraicGeometry.IsAffineOpen (g ⁻¹ᵁ V k l m)) ∧
      (⨆ k, g ⁻¹ᵁ U k) = ⊤ ∧
      (∀ k l m, g ⁻¹ᵁ V k l m ≤ (g ⁻¹ᵁ U k) ⊓ (g ⁻¹ᵁ U l)) ∧
      ∀ k l, (⨆ m, g ⁻¹ᵁ V k l m) = (g ⁻¹ᵁ U k) ⊓ (g ⁻¹ᵁ U l) := by
  refine ⟨fun k => (hUaff k).preimage g, fun k l m => (hVaff k l m).preimage g, ?_, ?_, ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, hUtop, Scheme.Hom.preimage_top]
  · intro k l m
    rw [← Scheme.Hom.preimage_inf, ← hVsup k l]
    exact Scheme.Hom.preimage_mono _ (le_iSup _ m)
  · intro k l
    rw [← Scheme.Hom.preimage_iSup, hVsup k l, Scheme.Hom.preimage_inf]

variable {κ ν : Type u} (U : κ → S.Opens) (V : κ → κ → ν → S.Opens)
  (hUaff : ∀ k, AlgebraicGeometry.IsAffineOpen (U k))
  (hVaff : ∀ k l m, AlgebraicGeometry.IsAffineOpen (V k l m))
  (hVle : ∀ k l m, V k l m ≤ U k ⊓ U l)

/-- The objects of the one-hypercover: the affine opens `U k`. -/
def hcObj (k : κ) : AlgebraicGeometry.SmallAffineEtale B S hS :=
  objOfAffineOpen B S hS (U k) (hUaff k)

/-- The second layer: the affine opens `V k l m` covering `U k ⊓ U l`. -/
def hcInter (k l : κ) (m : ν) : AlgebraicGeometry.SmallAffineEtale B S hS :=
  objOfAffineOpen B S hS (V k l m) (hVaff k l m)

/-- The first projection of the one-hypercover. -/
def hcFst (k l : κ) (m : ν) :
    hcInter B S hS V hVaff k l m ⟶ hcObj B S hS U hUaff k :=
  leOfAffineOpen B S hS _ _ (hVaff k l m) (hUaff k) ((hVle k l m).trans inf_le_left)

/-- The second projection of the one-hypercover. -/
def hcSnd (k l : κ) (m : ν) :
    hcInter B S hS V hVaff k l m ⟶ hcObj B S hS U hUaff l :=
  leOfAffineOpen B S hS _ _ (hVaff k l m) (hUaff l) ((hVle k l m).trans inf_le_right)

/-- **The parametrised one-hypercover.** A family of affine opens covering `S`, together with
affine opens covering each pairwise intersection, is a one-hypercover of the terminal sheaf of the
small affine etale site of `S`. This is the form the `hlev` and `hC` hypotheses of
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit` consume: they
ask for the notion of a *chosen* family transported to every level of a system and to the colimit
site, so the four pieces of the datum are named definitions rather than lambdas written inside
the structure, and `hlev` can speak of their transition images.

The two obligations are the two statements proved above about the site, which is why this is
short: `coversTop_objOfAffineOpen` for the first, and for the second
`exists_covering_sieve_subordinate` applied to the family covering `U k ⊓ U l`, whose hypothesis
is met because a morphism to the object of an affine open puts the image of the structure morphism
inside that open (`base_mem_of_hom`). The two factorisation equations are then automatic: an
object receives at most ONE morphism to the object of an affine open
(`hom_ext_objOfAffineOpen`, the structure morphism being an open immersion and so a
monomorphism), so any two agree and nothing has to be computed.

A warning about the index binder, which cost a round to find. Declaring `{κ ν : Type*}` here makes
the statement fail to elaborate at all -- `(deterministic) timeout at whnf`, 200000 heartbeats, on
the signature line -- while `{κ ν : Type u}` elaborates in seconds. The auto-bound universes are
what blow the budget, not the size of the terms. Raising the heartbeat limit is not available in
this development, so the binder is the fix; `Type u` is in any case where a family of opens of a
`Scheme.{u}` is indexed. -/
theorem isTopOneHypercover_hc (hUtop : (⨆ k, U k) = ⊤)
    (hVsup : ∀ k l, (⨆ m, V k l m) = U k ⊓ U l) :
    Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn
      (AlgebraicGeometry.SmallAffineEtale.topology B S hS) (hcObj B S hS U hUaff)
      (hcInter B S hS V hVaff) (hcFst B S hS U V hUaff hVaff hVle)
      (hcSnd B S hS U V hUaff hVaff hVle) where
  coversTop := coversTop_objOfAffineOpen B S hS U hUaff hUtop
  locally_factors Z k l f g := by
    obtain ⟨T, hT, hfac⟩ := exists_covering_sieve_subordinate B S hS (V k l) (hVaff k l) Z
      (fun x => by
        have hx : (structMap B S hS Z).base x ∈ U k ⊓ U l :=
          ⟨base_mem_of_hom B S hS (U k) (hUaff k) _ f x,
            base_mem_of_hom B S hS (U l) (hUaff l) _ g x⟩
        rw [← hVsup k l] at hx
        exact TopologicalSpace.Opens.mem_iSup.1 hx)
    refine ⟨T, hT, fun Y q hq => ?_⟩
    obtain ⟨m, b, -⟩ := hfac q hq
    refine ⟨m, b, ?_, ?_⟩
    · apply hom_ext_objOfAffineOpen B S hS (U k) (hUaff k)
    · apply hom_ext_objOfAffineOpen B S hS (U l) (hUaff l)

/-- A fibre-product square over the structure morphism of an object identified with the object of
an affine open `U` is one over `U.ι`, after composing the top map with the identification. -/
private theorem isPullback_comp_toScheme_map_of_iso {A : AlgebraicGeometry.SmallAffineEtale B S hS}
    {U : S.Opens} {hU : AlgebraicGeometry.IsAffineOpen U} (e : A ≅ objOfAffineOpen B S hS U hU)
    {P T : Scheme.{u}} {fst : P ⟶ (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj A}
    {snd : P ⟶ T} {g : T ⟶ S} (h : IsPullback fst snd (structMap B S hS A) g) :
    IsPullback (fst ≫ (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map e.hom) snd
      U.ι g := by
  refine h.of_iso (Iso.refl _) ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).mapIso e)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_ (by simp)
  have h1 := toScheme_map_comp_ι B S hS U hU _ e.hom
  simpa using h1.symm

end Opens

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- **A one-hypercover at a level of the system, from a datum of affine opens of that level's
scheme.** A family of affine opens covering `X_j` together with affine opens covering each
pairwise intersection gives a one-hypercover of the terminal sheaf of the level `j`, on the
objects of the level corresponding to the objects of those opens.

This is the site half of the `hlev` hypothesis of
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`, and it is a
direct composition with nothing missing. `isTopOneHypercover_hc` gives the one-hypercover on the
small affine etale site of `X_j`; `affineEtaleSiteColimit_level_cover` is the correspondence of
covering presieves across `levelEquiv j`, which is exactly the hypothesis of
`Stacks.WeakSites.ColimitGlobalSections.functorPullback_mem_of_map_mem_toPrecoverage`, whose
conclusion is exactly the hypothesis of
`Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn.of_equiv`.

The equivalence used is `levelEquiv j` alone. A level of the system is a category of
representatives of the small affine etale site of `X_j`, and that is the only identification
needed; composing it with a raising of the site would in addition demand the descent of covering
sieves along a `Precoverage.comap`, which is the one step here that would need an induction over
`CategoryTheory.Precoverage.Saturate`. -/
theorem isTopOneHypercover_level (j : (sys D c B hD hX hc).I) {κ ν : Type (max u v)}
    (U : κ → (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj j)).Opens)
    (V : κ → κ → ν →
      (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj j)).Opens)
    (hUaff : ∀ k, AlgebraicGeometry.IsAffineOpen (U k))
    (hVaff : ∀ k l m, AlgebraicGeometry.IsAffineOpen (V k l m))
    (hVle : ∀ k l m, V k l m ≤ U k ⊓ U l) (hUtop : (⨆ k, U k) = ⊤)
    (hVsup : ∀ k l, (⨆ m, V k l m) = U k ⊓ U l) :
    Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn ((sys D c B hD hX hc).J j)
      (fun k => ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv j).inverse.obj
        (hcObj B _ (hD _) U hUaff k))
      (fun k l m => ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv j).inverse.obj
        (hcInter B _ (hD _) V hVaff k l m))
      (fun k l m => ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv j).inverse.map
        (hcFst B _ (hD _) U V hUaff hVaff hVle k l m))
      (fun k l m => ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv j).inverse.map
        (hcSnd B _ (hD _) U V hUaff hVaff hVle k l m)) :=
  (isTopOneHypercover_hc B _ (hD _) U V hUaff hVaff hVle hUtop hVsup).of_equiv
    ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv j)
    (fun Z S hS =>
      Stacks.WeakSites.ColimitGlobalSections.functorPullback_mem_of_map_mem_toPrecoverage
        ((sys D c B hD hX hc).J j)
        ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv j)
        (fun Z' R h => (affineEtaleSiteColimit_level_cover D c B hD hX hc j Z' R).mpr h) Z S hS)

/-- **The square the object half of `hlev` asks for, at a level of the system.** Given an
identification `e` of an object `Y` of the level `i` with the object of an affine open `U` of
`X_i`, the structure morphism of the transition image of `Y` at a level `j` below `i` is the base
change of `U.ι` along the transition morphism of schemes.

This is `transition_isPullback` with `e` pushed into its top-right corner by
`CategoryTheory.IsPullback.of_iso`; the hypothesis that `e` is an identification OVER `X_i`,
which `of_iso` needs for that corner, is `Stacks.EtaleCohomology.toScheme_map_comp_structMap`
against
`Stacks.EtaleCohomology.QcqsLimitCohomology.structMap_objOfAffineOpen`, and holds for any `e`
because a morphism of the site is a morphism over `X_i` by definition.

It is a separate declaration from the isomorphism it feeds. Stating the two together does not
elaborate: `Stacks.EtaleCohomology.QcqsLimitCohomology.isoObjOfPreimage` has to see the preimage
object through the system's spellings of its index, `indexEquiv.functor.obj j` and `hD _`, and the
two spellings are defeq only at default transparency, so the unifier meets them while the squares
corners are still metavariables. Split in two, nothing is left open: this lemma pins every corner,
and the isomorphism then consumes it with no unification to do. -/
theorem isPullback_transitionImage_structMap
    {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) (Y : (sys D c B hD hX hc).C i)
    (U : (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i)).Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U)
    (e : ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor.obj Y ≅
      objOfAffineOpen B _ (hD _) U hU) :
    IsPullback
      (((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app Y ≫
        (AlgebraicGeometry.SmallAffineEtale.toScheme B _ (hD _)).map e.hom)
      (structMap B _ (hD _)
        (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv j).functor.obj
          (((sys D c B hD hX hc).u a).obj Y)))
      U.ι (D.map ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a)) := by
  exact isPullback_comp_toScheme_map_of_iso B _ (hD _) e
    ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Y)

/-- **The transition image of the object of an affine open is the object of the preimage open.**
The object half of the `hlev` hypothesis of
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`, assembled:
`isPullback_transitionImage_structMap` produces the square,
`Stacks.EtaleCohomology.QcqsLimitCohomology.isoObjOfPreimage` turns it into an isomorphism of the
site of `X_j`, and the unit of the level equivalence carries that back to the level. -/
noncomputable def transitionImage_isoObjOfPreimage
    {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) (Y : (sys D c B hD hX hc).C i)
    (U : (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i)).Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U)
    (e : ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor.obj Y ≅
      objOfAffineOpen B _ (hD _) U hU) :
    ((sys D c B hD hX hc).u a).obj Y ≅
      ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv j).inverse.obj
        (objOfAffineOpen B _ (hD _)
          (D.map ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a) ⁻¹ᵁ U)
          (hU.preimage _)) :=
  ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv j).unitIso.app _ ≪≫
    (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv j).inverse.mapIso
      (isoObjOfPreimage B _ (hD _) _ U hU _ _
        (isPullback_transitionImage_structMap D c B hD hX hc a Y U hU e)))

include hc in
/-- **The projections of the limit cone are affine**, at the universes of this development: the
index type is a `Type v` while the schemes are `Scheme.{max u v}`.

Both halves of that matter, and three statements of this fact have to be told apart. Mathlib's
`AlgebraicGeometry.isAffineHom_π_app`, in `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`,
puts the index type, the index morphisms and the schemes all in ONE universe. This repository's
`AlgebraicGeometry.isAffineHom_π_app'`, in `StacksFrontier/AlgebraicGeometry/Limits/
StacksFrontier/AlgebraicGeometry/Limits/IndexHomUniverse.lean`, frees the index morphism universe but leaves the index type at the scheme
universe. Neither fits here. The one used is also THIS REPOSITORY'S, not Mathlib's:
`AlgebraicGeometry.isAffineHom_π_app_of_initiallySmall`, in `StacksFrontier/AlgebraicGeometry/
LimitUniverse/AffineTransitionLimit.lean`, which has all three universes independent and already
had a consumer in `StacksFrontier/AlgebraicGeometry/LimitDescentGlueing/Glueing.lean`.

Its price is `CategoryTheory.InitiallySmall` on the index, which does not synthesize on its own.
The route is recorded for exactly this index in
`StacksFrontier/AlgebraicGeometry/LimitDescentGlueing/Affine.lean`: for the opposite of a directed
preorder `CategoryTheory.LocallySmall` is automatic, the category being thin, and
`CategoryTheory.InitiallySmall` follows -- `essentiallySmall_of_small_of_locallySmall` is an
instance and `initiallySmall_of_essentiallySmall` is one step from it. -/
theorem isAffineHom_limitProjection (i : Iᵒᵖ) : IsAffineHom (c.π.app i) := by
  have : InitiallySmall.{max u v} Iᵒᵖ := initiallySmall_of_essentiallySmall Iᵒᵖ
  exact AlgebraicGeometry.isAffineHom_π_app_of_initiallySmall D c hc i

/-- **The raised site receives at most one morphism to the raised object of an affine open.**
`AsSmall.down` is faithful, being half of an equivalence, so this is `hom_ext_objOfAffineOpen`
with nothing added. The retired raised-site development proved this from the strictness of the
raising; faithfulness is the fact it is an instance of. -/
theorem hom_ext_up_objOfAffineOpen (U : c.pt.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    (Z : limitSite D c B hX)
    (f g : Z ⟶ AsSmall.up.obj (objOfAffineOpen B c.pt hX U hU)) : f = g :=
  (AsSmall.equiv.symm (C := AlgebraicGeometry.SmallAffineEtale B c.pt hX)).functor.map_injective
    (hom_ext_objOfAffineOpen B c.pt hX U hU _ _ _)

include hc in
/-- **The square the object half of `hC` asks for.** The mirror of
`isPullback_transitionImage_structMap` for the functors to the limit: the structure morphism of
the image in the site of `X` of an object identified with the object of an affine open `U` of
`X_{i₀}` is the base change of `U.ι` along the projection `X ⟶ X_{i₀}`.

Identical to the transition case with `toLimit_isPullback` in place of `transition_isPullback` and
`c.π.app` in place of `D.map`; the two fields sit beside each other in
`Stacks.EtaleCohomology.AffineEtaleSiteColimit` for exactly this reason. -/
theorem isPullback_toLimitImage_structMap (i₀ : (sys D c B hD hX hc).I)
    (Y : (sys D c B hD hX hc).C i₀)
    (U : (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀)).Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U)
    (e : ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).functor.obj Y ≅
      objOfAffineOpen B _ (hD _) U hU) :
    IsPullback
      (((affineEtaleSiteColimit D c B hD hX hc).toLimitFst i₀).app Y ≫
        (AlgebraicGeometry.SmallAffineEtale.toScheme B _ (hD _)).map e.hom)
      (structMap B c.pt hX (((affineEtaleSiteColimit D c B hD hX hc).toLimit i₀).obj Y))
      U.ι (c.π.app ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀)) := by
  exact isPullback_comp_toScheme_map_of_iso B _ (hD _) e
    ((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i₀ Y)

include hc in
/-- **The image in the site of `X` of the object of an affine open is the object of the preimage
open.** The object half of `hC`, by the same three facts as the transition case. There is no level
equivalence to undo here: the functors to the limit land in the small affine etale site of `X`
itself.

Affineness of the projection is an instance BINDER rather than taken from
`isAffineHom_limitProjection` inside the proof, because the statement itself needs it: the
conclusion names `hU.preimage _`, which is elaborated before any tactic runs. Nor can
`isAffineHom_limitProjection` be an instance -- it takes `hc : IsLimit c`, which typeclass
synthesis cannot infer, and declaring it so reports exactly that. Callers discharge the binder
with a `have`. -/
noncomputable def toLimitImage_isoObjOfPreimage (i₀ : (sys D c B hD hX hc).I)
    (Y : (sys D c B hD hX hc).C i₀)
    (U : (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀)).Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U)
    (e : ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).functor.obj Y ≅
      objOfAffineOpen B _ (hD _) U hU)
    [IsAffineHom (c.π.app
      ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀))] :
    ((affineEtaleSiteColimit D c B hD hX hc).toLimit i₀).obj Y ≅
      objOfAffineOpen B c.pt hX
        (c.π.app ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀) ⁻¹ᵁ U)
        (hU.preimage _) :=
  isoObjOfPreimage B c.pt hX _ U hU _ _
    (isPullback_toLimitImage_structMap D c B hD hX hc i₀ Y U hU e)

include hc in
/-- **A one-hypercover of the raised site of the limit, from a datum of affine opens of `X`.**
The site half of `hC`. The colimit site of this development is raised through
`CategoryTheory.AsSmall` -- `limitSite`, and that raising is not optional, Stacks 09YP wanting a
small category in the universe of the levels -- so unlike the levels this needs the descent of
covering sieves along a `Precoverage.comap`, which is
`Stacks.WeakSites.ColimitGlobalSections.functorPullback_mem_toGrothendieck_comap_asSmall`. -/
theorem isTopOneHypercover_limitSite {κ ν : Type (max u v)} (U : κ → c.pt.Opens)
    (V : κ → κ → ν → c.pt.Opens)
    (hUaff : ∀ k, AlgebraicGeometry.IsAffineOpen (U k))
    (hVaff : ∀ k l m, AlgebraicGeometry.IsAffineOpen (V k l m))
    (hVle : ∀ k l m, V k l m ≤ U k ⊓ U l) (hUtop : (⨆ k, U k) = ⊤)
    (hVsup : ∀ k l, (⨆ m, V k l m) = U k ⊓ U l) :
    Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn
      (limitSitePrecoverage D c B hX).toGrothendieck
      (fun k => AsSmall.up.obj (hcObj B c.pt hX U hUaff k))
      (fun k l m => AsSmall.up.obj (hcInter B c.pt hX V hVaff k l m))
      (fun k l m => AsSmall.up.map (hcFst B c.pt hX U V hUaff hVaff hVle k l m))
      (fun k l m => AsSmall.up.map (hcSnd B c.pt hX U V hUaff hVaff hVle k l m)) :=
  (isTopOneHypercover_hc B c.pt hX U V hUaff hVaff hVle hUtop hVsup).of_equiv
    AsSmall.equiv.symm
    (fun _ _ hS =>
      Stacks.WeakSites.ColimitGlobalSections.functorPullback_mem_toGrothendieck_comap_asSmall
        (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX) hS)

/-- **A level receives at most one morphism to the level object of an affine open.** The transport
through `levelEquiv n` of `hom_ext_objOfAffineOpen`: the structure morphism of the object of an
affine open is an open immersion, hence a monomorphism, so there is nothing to choose. -/
theorem hom_ext_inverse_objOfAffineOpen (n : (sys D c B hD hX hc).I)
    (U : (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj n)).Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) {Z : (sys D c B hD hX hc).C n}
    (f g : Z ⟶ ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).inverse.obj
      (objOfAffineOpen B _ (hD _) U hU)) : f = g := by
  have h : ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).functor.map f ≫
        (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).counitIso.app _).hom =
      ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).functor.map g ≫
        (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).counitIso.app _).hom :=
    hom_ext_objOfAffineOpen B _ (hD _) U hU _ _ _
  exact ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).functor.map_injective
    ((cancel_mono _).1 h)

/-- The same for any object isomorphic to the level object of an affine open -- which is what a
transition image is, by `transitionImage_isoObjOfPreimage`. -/
theorem hom_ext_of_iso_inverse_objOfAffineOpen (n : (sys D c B hD hX hc).I)
    {A : (sys D c B hD hX hc).C n}
    (U : (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj n)).Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U)
    (φ : A ≅ ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).inverse.obj
      (objOfAffineOpen B _ (hD _) U hU))
    {Z : (sys D c B hD hX hc).C n} (f g : Z ⟶ A) : f = g :=
  (cancel_mono φ.hom).1 (hom_ext_inverse_objOfAffineOpen D c B hD hX hc n U hU _ _)

/-- The same uniqueness on the raised site of the limit, for anything isomorphic to the raised
object of an affine open. -/
theorem hom_ext_of_iso_up_objOfAffineOpen {A : limitSite D c B hX} (U : c.pt.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U)
    (φ : A ≅ AsSmall.up.obj (objOfAffineOpen B c.pt hX U hU))
    {Z : limitSite D c B hX} (f g : Z ⟶ A) : f = g :=
  (cancel_mono φ.hom).1 (hom_ext_up_objOfAffineOpen D c B hX U hU _ _ _)

include hc in
/-- **The covering data of Stacks 09YQ in degree zero, for a quasi-compact quasi-separated
level.** There is a finite family of objects of the level `i₀`, with finitely many objects over
each pair, which is simultaneously a one-hypercover of the terminal sheaf of EVERY level below
`i₀`, in its transition images, and a one-hypercover of the terminal sheaf of the colimit site, in
its image there.

These are the hypotheses `hlev` and `hC` of
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`, and they are
stated together because that theorem needs them for ONE family: the consumer fixes `W₀`, `P₀`,
`q₁`, `q₂` and asks for both, so an existential supplying only one of them supplies nothing it can
use.

The family is what a finite affine cover of `X_{i₀}` and finite affine covers of its pairwise
intersections give. Both halves then run the same three steps off the two fibre-product fields of
`Stacks.EtaleCohomology.AffineEtaleSiteColimit`, which sit beside each other for this reason:
restrict the datum (`preimage_oneHypercover_data`, the transitions and the projections both being
affine), build the one-hypercover where the geometry is (`isTopOneHypercover_level`,
`isTopOneHypercover_limitSite`), and identify the objects with the images
(`transitionImage_isoObjOfPreimage` off `transition_isPullback`,
`toLimitImage_isoObjOfPreimage` off `toLimit_isPullback`).

All four factorisation equations `IsTopOneHypercoverOn.of_iso` asks for -- two per half -- are
discharged outright, with no computation, by the SAME fact: the structure morphism of the object
of an affine open is an open immersion, hence a monomorphism, so an object receives at most one
morphism to it and therefore at most one to anything isomorphic to it. That fact has now
discharged the `locally_factors` obligation of `isTopOneHypercover_hc`, the two equations of the
`hlev` half and the two of the `hC` half. It is the reason the proofs in this file are three and
four lines long, and it is worth knowing before writing another one. -/
theorem exists_hlev_and_hC (i₀ : (sys D c B hD hX hc).I)
    [CompactSpace (D.obj
      ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀))]
    [QuasiSeparatedSpace (D.obj
      ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀))] :
    ∃ (κ' ν' : Type) (_ : Finite κ') (_ : Finite ν') (W₀ : κ' → (sys D c B hD hX hc).C i₀)
      (P₀ : κ' → κ' → ν' → (sys D c B hD hX hc).C i₀)
      (q₁ : ∀ k l m, P₀ k l m ⟶ W₀ k) (q₂ : ∀ k l m, P₀ k l m ⟶ W₀ l),
      (∀ {n : (sys D c B hD hX hc).I} (a : n ⟶ i₀),
          Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn ((sys D c B hD hX hc).J n)
            (fun k => ((sys D c B hD hX hc).u a).obj (W₀ k))
            (fun k l m => ((sys D c B hD hX hc).u a).obj (P₀ k l m))
            (fun k l m => ((sys D c B hD hX hc).u a).map (q₁ k l m))
            (fun k l m => ((sys D c B hD hX hc).u a).map (q₂ k l m))) ∧
        Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn
          (limitSitePrecoverage D c B hX).toGrothendieck
          (fun k => (toLimitSmall D c B hD hX hc i₀).obj (W₀ k))
          (fun k l m => (toLimitSmall D c B hD hX hc i₀).obj (P₀ k l m))
          (fun k l m => (toLimitSmall D c B hD hX hc i₀).map (q₁ k l m))
          (fun k l m => (toLimitSmall D c B hD hX hc i₀).map (q₂ k l m)) := by
  obtain ⟨κ, ν, hκ, hν, U, V, hUaff, hVaff, hUtop, hVle, hVsup⟩ :=
    Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens
      (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀))
  have hlevκ : ∀ {n : (sys D c B hD hX hc).I} (a : n ⟶ i₀),
      Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn ((sys D c B hD hX hc).J n)
        (fun k => ((sys D c B hD hX hc).u a).obj
          (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).inverse.obj
            (hcObj B _ (hD _) U hUaff k)))
        (fun k l m => ((sys D c B hD hX hc).u a).obj
          (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).inverse.obj
            (hcInter B _ (hD _) V hVaff k l m)))
        (fun k l m => ((sys D c B hD hX hc).u a).map
          ((((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).inverse.map
            (hcFst B _ (hD _) U V hUaff hVaff hVle k l m))))
        (fun k l m => ((sys D c B hD hX hc).u a).map
          ((((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).inverse.map
            (hcSnd B _ (hD _) U V hUaff hVaff hVle k l m)))) := by
    intro n a
    obtain ⟨hUa, hVa, hUtopa, hVlea, hVsupa⟩ := preimage_oneHypercover_data
      (D.map ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a))
      U V hUaff hVaff hUtop hVsup
    refine (isTopOneHypercover_level D c B hD hX hc n _ _ hUa hVa hVlea hUtopa hVsupa).of_iso
      (fun k => (transitionImage_isoObjOfPreimage D c B hD hX hc a _ (U k) (hUaff k)
        (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).counitIso.app _)).symm)
      (fun k l m => (transitionImage_isoObjOfPreimage D c B hD hX hc a _ (V k l m) (hVaff k l m)
        (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).counitIso.app _)).symm)
      (fun k l m => ?_) (fun k l m => ?_)
    all_goals
      exact hom_ext_of_iso_inverse_objOfAffineOpen D c B hD hX hc n _ (hUa _)
        (transitionImage_isoObjOfPreimage D c B hD hX hc a _ (U _) (hUaff _)
          (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).counitIso.app _)) _ _
  have hπ := isAffineHom_limitProjection D c hc
    ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀)
  have hCκ : Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn
      (limitSitePrecoverage D c B hX).toGrothendieck
      (fun k => (toLimitSmall D c B hD hX hc i₀).obj
        (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).inverse.obj
          (hcObj B _ (hD _) U hUaff k)))
      (fun k l m => (toLimitSmall D c B hD hX hc i₀).obj
        (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).inverse.obj
          (hcInter B _ (hD _) V hVaff k l m)))
      (fun k l m => (toLimitSmall D c B hD hX hc i₀).map
        ((((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).inverse.map
          (hcFst B _ (hD _) U V hUaff hVaff hVle k l m))))
      (fun k l m => (toLimitSmall D c B hD hX hc i₀).map
        ((((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).inverse.map
          (hcSnd B _ (hD _) U V hUaff hVaff hVle k l m)))) := by
    obtain ⟨hUa, hVa, hUtopa, hVlea, hVsupa⟩ := preimage_oneHypercover_data
      (c.π.app ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀))
      U V hUaff hVaff hUtop hVsup
    refine (isTopOneHypercover_limitSite D c B hX hc _ _ hUa hVa hVlea hUtopa hVsupa).of_iso
      (fun k => (AsSmall.up.mapIso (toLimitImage_isoObjOfPreimage D c B hD hX hc i₀ _ (U k)
        (hUaff k)
        (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).counitIso.app _))).symm)
      (fun k l m => (AsSmall.up.mapIso (toLimitImage_isoObjOfPreimage D c B hD hX hc i₀ _
        (V k l m) (hVaff k l m)
        (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).counitIso.app _))).symm)
      (fun k l m => ?_) (fun k l m => ?_)
    all_goals
      exact hom_ext_of_iso_up_objOfAffineOpen D c B hX _ (hUa _)
        (AsSmall.up.mapIso (toLimitImage_isoObjOfPreimage D c B hD hX hc i₀ _ (U _) (hUaff _)
          (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).counitIso.app _))) _ _
  obtain ⟨nκ, ⟨eκ⟩⟩ := Finite.exists_equiv_fin κ
  obtain ⟨nν, ⟨eν⟩⟩ := Finite.exists_equiv_fin ν
  exact ⟨Fin nκ, Fin nν, inferInstance, inferInstance, _, _, _, _,
    fun a => (hlevκ a).reindex eκ.symm eν.symm, hCκ.reindex eκ.symm eν.symm⟩

open Stacks.WeakSites.ColimitGlobalSections in
include hc in
/-- **Stacks 09YQ in degree zero, for a quasi-compact quasi-separated level.** Let the `X_i` be an
inverse system of schemes over a directed index with affine transition morphisms and limit `X`, let
`F` be a system of sheaves of sets on the small affine etale sites of the `X_i`, and let `G` on the
site of `X` be the colimit `colim f_i^{-1} F_i`. If one level `X_{i₀}` is quasi-compact and
quasi-separated then the global sections of `G` are the filtered colimit of the global sections of
the `F n` over the arrows `n ⟶ i₀`.

This is the degree-zero half of the Cech step that Stacks 09YQ passes over, and the difficulty it
answers is that a quasi-compact quasi-separated `X_{i₀}` is not an object of its own small affine
etale site unless it is affine: its global sections are the sections over no object, so the
object-level statement of Stacks 09YN does not apply to them. What replaces the missing terminal
object is the finite one-hypercover of `exists_hlev_and_hC`.

Nothing about sections is assumed. The object-level hypotheses of Stacks 09YN are derived from the
five inputs of Stacks 09YP for the raised site of the limit -- `toLimitSmall_transition`,
`toLimitSmall_obj_descends`, `toLimitSmall_hom_descends`, `toLimitSmall_hom_eventually_eq` and
`mem_limitSitePrecoverage_iff` -- so the hypotheses here are exactly a colimit presentation of `G`.

It instantiates the general
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit` at a
concrete site. -/
theorem globalSections_colimit_of_qcqs_level
    (F : InverseSystemOfFiniteSites.SheafSystem.{v, v, max u v + 1} (sys D c B hD hX hc))
    (G : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1)))
    (ι : ∀ i, (F.obj i).obj ⟶ (toLimitSmall D c B hD hX hc i).op ⋙ G.obj)
    (hpres : F.IsColimitPresentation (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) G ι)
    (i₀ : (sys D c B hD hX hc).I)
    [CompactSpace (D.obj
      ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀))]
    [QuasiSeparatedSpace (D.obj
      ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i₀))]
    (ρ : ∀ {n : (sys D c B hD hX hc).I} (_ : n ⟶ i₀),
      (F.obj n).obj.sections → G.obj.sections)
    (hρ : ∀ {n : (sys D c B hD hX hc).I} (a : n ⟶ i₀) (t : (F.obj n).obj.sections)
      (Y : (sys D c B hD hX hc).C n),
      (ρ a t).val (Opposite.op ((toLimitSmall D c B hD hX hc n).obj Y)) =
        (ι n).app (Opposite.op Y) (t.val (Opposite.op Y))) :
    GlobalSectionsIsColimit (sys D c B hD hX hc) F.obj F.map G i₀ ρ := by
  obtain ⟨hι, hG⟩ := hpres
  obtain ⟨hsurj, hsep⟩ := objectSections_jointlySurjective_and_separated
    (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) (toLimitSmall_obj_descends D c B hD hX hc)
    (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc) (limitSitePrecoverage D c B hX)
    (mem_limitSitePrecoverage_iff D c B hD hX hc) F.obj F.map F.map_comp G ι hι hG
  exact globalSections_colimit_of_exists_topOneHypercover (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc) F.obj F.map G ι
    F.map_comp hι hsurj hsep i₀ ρ hρ (exists_hlev_and_hC D c B hD hX hc i₀)

end Stacks.EtaleCohomology.QcqsLimitCohomology

end
