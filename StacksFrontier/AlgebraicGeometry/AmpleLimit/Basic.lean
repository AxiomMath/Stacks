module

public import StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic

/-!
# Ampleness descends through a cofiltered limit of schemes

Let `S = lim Sᵢ` be the limit of a cofiltered diagram of quasi-compact quasi-separated schemes
with affine transition morphisms, let `j` be a stage and let `M` be an invertible module on `Sⱼ`.
[Stacks Project, Tag 09MT] says that if the pullback of `M` to `S` is ample, then the pullback of
`M` to `Sᵢ` is ample for some `i` over `j`.

This file proves that, from one explicit hypothesis:
`Stacks.AlgebraicGeometry.AmpleLimit.SectionsDescent`, which is
[Stacks Project, Tag 01Z0] — `Γ(S, f₀^*ℱ₀) = colim Γ(Sᵢ, f_{i0}^*ℱ₀)` — for the tensor powers of
`M`, in its surjectivity half. Everything else the source's proof uses is discharged here or was
already available: the two remaining inputs `01Z6` and `01Z4` (3) are in Mathlib, and `01PS` is
the definition of ampleness in this library.

**Why the hypothesis is not discharged.** Mathlib's
`AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone` is Tag 01Z0 for the *structure sheaf* only:
it says `Γ(S, 𝒪_S)` is the filtered colimit of the `Γ(Sᵢ, 𝒪_{Sᵢ})`. Tag 01Z0 as the source states
it is for an arbitrary quasi-coherent `ℱ₀` on the base stage, and Tag 09MT needs exactly the case
`ℱ₀ = M^{⊗ n}`, which is not the structure sheaf. See the implementation notes for the route.

## Main definitions

* `Stacks.AlgebraicGeometry.AmpleLimit.transportSection`: a global section of the `n`th tensor
  power of the pullback of `M` to a stage, moved to a stage below it.
* `Stacks.AlgebraicGeometry.AmpleLimit.SectionsDescent`: [Stacks Project, Tag 01Z0] for the
  tensor powers of `M`, as a named hypothesis.
* `Stacks.AlgebraicGeometry.AmpleLimit.NonvanishingLocusDescent`: the weaker consequence of it
  that the descent of ampleness actually consumes — only the nonvanishing *loci* are compared.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isCompact_nonvanishingOpen`: the nonvanishing locus of a
  global section of an invertible module on a quasi-compact scheme is quasi-compact.
* `AlgebraicGeometry.Scheme.Modules.pullbackPowerSection` and
  `nonvanishingOpen_pullbackPowerSection`: the pullback of a global section of a tensor power,
  and the fact that its nonvanishing locus is the preimage of the original one.
* `Stacks.AlgebraicGeometry.AmpleLimit.nonvanishingLocusDescent_of_sectionsDescent`: Tag 01Z0
  implies the weak form.
* `Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit`:
  **[Stacks Project, Tag 09MT] from `NonvanishingLocusDescent`**, and
  `exists_isAmple_pullback_map_of_sectionsDescent`: the same from `SectionsDescent`, i.e. from
  Tag 01Z0 itself.

## Implementation notes

The source's proof is followed step for step. Ampleness of the pullback `L` to `S` gives, at every
point, an affine nonvanishing locus `S_s` of a section `s` of `L^{⊗ n}` with `n ≥ 1`; `S` is
quasi-compact, so finitely many of those cover it. Each `s` descends to a section at a stage
(this is the hypothesis, Tag 01Z0), so finitely many sections live at a single stage `k` —
obtained from `CategoryTheory.IsCofiltered.inf_exists`, which also *equalises* the morphisms to
`j`, so that one invertible module on `S_k` carries all of them. Each of their nonvanishing loci
is quasi-compact (`isCompact_nonvanishingOpen`) with affine preimage in `S`, so it becomes affine
at a later stage by Tag 01Z6 in the form
`AlgebraicGeometry.EventualFiniteness.exists_isAffineOpen_map_preimage_of_isLimit`; a second
application of `inf_exists` brings those stages together. Finally the loci cover `S`, so by
Tag 01Z4 (3) (`AlgebraicGeometry.exists_map_eq_top`) they cover a stage, and ampleness at that
stage is the definition.

Only one piece of bookkeeping is needed, and it is `transportSection`: moving a section along a
transition morphism produces a section of the `n`th power of an *iterated* pullback, which has to
be identified with the pullback along the composite. That identification is
`AlgebraicGeometry.Scheme.Modules.pullbackCompObjIso`, built from
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and `pullbackCongr`, conjugated past the tensor
power by `Stacks.SheafOfModules.Invertible.tensorPowerCongr`; because `transportSection` takes the
composite as an *equation* rather than forming it, the three moves of the proof land on the
pullback along `r ≫ fm ≫ fk` directly and no further comparison is needed at the end.

The invertibility of a pullback is [Stacks Project, Tag 0B8L],
`Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback`. It is not an instance in this
library; it is made one `scoped` to `Stacks.AlgebraicGeometry.AmpleLimit` here, keyed on
`AlgebraicGeometry.Scheme.Modules.pullback`, so that the iterated pullbacks the proof forms do not
each need a binder. The statements below cannot be written without it, because the invertible
module whose ampleness is asserted is a pullback along a *bound* morphism; a consumer therefore
writes `open scoped Stacks.AlgebraicGeometry.AmpleLimit`.

**The route to discharging `SectionsDescent`.** Tag 01Z0's own proof writes `Sᵢ` as the relative
spectrum of `f_{i0,*}𝒪_{Sᵢ}` over `S₀` and uses that global sections commute with filtered
colimits of quasi-coherent algebras. The cheaper route available here, which needs no new
colimit theory, is to trivialise: `M^{⊗ n}` is trivial on each member of a finite affine open
cover of `Sⱼ` (the stage is quasi-compact), so over the preimage of such a member a section of the
pullback *is a function*, and Mathlib's structure-sheaf statements
`AlgebraicGeometry.exists_appTop_π_eq_of_isLimit` and `exists_app_map_eq_map_of_isLimit` apply to
the opens diagram `AlgebraicGeometry.opensDiagram`, whose limit is that preimage
(`AlgebraicGeometry.isLimitOpensCone`). What remains is to glue the resulting local sections,
after making them agree on the quasi-compact overlaps at a later stage.

## References

* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerCongr)

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The nonvanishing locus of a global section of an invertible module on a quasi-compact
scheme is quasi-compact.** Finitely many affine opens cover the scheme, and the nonvanishing
locus meets each of them in an affine open by [Stacks Project, Tag 01PV]. -/
theorem isCompact_nonvanishingOpen {X : Scheme.{u}} [CompactSpace X] (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L] (s : L.sections) :
    IsCompact ((nonvanishingOpen (X := X.toRingedSpace) L s : X.Opens) : Set X) := by
  classical
  have hx : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := fun x => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  choose U hU hxU using hx
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x : X => ((U x : X.Opens) : Set X))
    (fun x => (U x).2.mem_nhds (hxU x))
  have hcov : ((nonvanishingOpen (X := X.toRingedSpace) L s : X.Opens) : Set X) =
      ⋃ x ∈ t, (((U x ⊓ nonvanishingOpen (X := X.toRingedSpace) L s : X.Opens)) : Set X) := by
    simp only [TopologicalSpace.Opens.coe_inf, ← Set.iUnion_inter]
    rw [ht, Set.top_eq_univ, Set.univ_inter]
  rw [hcov]
  exact t.finite_toSet.isCompact_biUnion fun x _ =>
    (isAffineOpen_inf_nonvanishingOpen L s _ (hU x)).isCompact

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L)]

/-- The pullback of a global section of the `n`th tensor power of an invertible module, read as a
global section of the `n`th tensor power of the pullback through
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso`. -/
def pullbackPowerSection (n : ℕ)
    (s : (tensorPower Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L (n : ℤ)).sections) :
    (tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj L) (n : ℤ)).sections :=
  SheafOfModules.sectionsMap (pullbackTensorPowerIso f L n).hom
    (Stacks.SheafOfModules.modulePullbackSection f.toLRSHom _ s)

/-- The nonvanishing locus of the pulled-back section is the preimage of the nonvanishing locus:
[Stacks Project, Tag 0H78] followed by the invariance of a nonvanishing locus under an
isomorphism of modules. -/
theorem nonvanishingOpen_pullbackPowerSection (n : ℕ)
    (s : (tensorPower Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L (n : ℤ)).sections) :
    nonvanishingOpen (X := X.toRingedSpace)
        (tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
          ((Scheme.Modules.pullback f).obj L) (n : ℤ))
        (pullbackPowerSection f L n s) =
      f ⁻¹ᵁ nonvanishingOpen (X := Y.toRingedSpace)
        (tensorPower Y.toRingedSpace.presheaf
          (structureSheafRing Y.toRingedSpace).property L (n : ℤ)) s :=
  (TopologicalSpace.Opens.ext (Stacks.SheafOfModules.nonvanishingLocus_sectionsMap
      X.toRingedSpace (pullbackTensorPowerIso f L n) _)).trans
    (Stacks.SheafOfModules.preimage_nonvanishingOpen f _ s).symm

end Pullback

/-- The pullback of a module along a composite, compared with the iterated pullback: the
object-level form of `AlgebraicGeometry.Scheme.Modules.pullbackComp`, with the composite supplied
as an equation so that a diagram's `CategoryTheory.Functor.map_comp` can be fed to it directly. -/
def pullbackCompObjIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hh : h = f ≫ g) (M : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback h).obj M :=
  (Scheme.Modules.pullbackComp f g).app M ≪≫ (Scheme.Modules.pullbackCongr hh.symm).app M

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.AlgebraicGeometry.AmpleLimit

/-- **[Stacks Project, Tag 0B8L]** as an instance: the pullback of an invertible module along a
morphism of schemes is invertible, in the `AlgebraicGeometry.SheafOfModules.IsInvertible`
spelling of invertibility and at the `AlgebraicGeometry.Scheme.Modules.pullback` spelling of the
pullback.

Both halves of that sentence are the point. `Stacks.Modules.isInvertible_pullback` is in the library, with
a global instance, but for the *other* of the two invertibility classes
(`Stacks.SheafOfModules.IsInvertible`), and it is the `AlgebraicGeometry` one that
`Stacks.SheafOfModules.Invertible.tensorPower` and `AlgebraicGeometry.Scheme.Modules.IsAmple`
require; and `Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback` is that class, but
stated for `RingedSpaceModuleAdjunction.modulePullback` of a morphism of ringed spaces, which
instance search does not match against a pullback along a morphism of schemes. So neither of the
two existing results fires here, and this is the restatement at the spelling the consumer uses.

It is given the `instance` attribute `scoped` to `Stacks.AlgebraicGeometry.AmpleLimit` just below,
so that the iterated pullbacks formed in this file do not each need an instance binder. The
statements of this file cannot be written without it — the invertible module whose ampleness is
asserted is a pullback along a *bound* morphism — so a consumer writes
`open scoped Stacks.AlgebraicGeometry.AmpleLimit`. -/
theorem algebraicGeometryIsInvertible_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [h : _root_.AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj M) :=
  @Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback X.toRingedSpace
    Y.toRingedSpace f.toLRSHom.toShHom M h

-- Scoped to this namespace rather than global, because the library deliberately keeps Tag 0B8L
-- out of instance search; a consumer writes `open scoped Stacks.AlgebraicGeometry.AmpleLimit`.
attribute [scoped instance] algebraicGeometryIsInvertible_pullback

section Transport

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hh : h = f ≫ g)
  (M : Z.Modules)
  [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
    (structureSheafRing Z.toRingedSpace).property M]

/-- A global section of the `n`th tensor power of `g^*M` on `Y`, moved along `f : X ⟶ Y` to a
global section of the `n`th tensor power of `h^*M` on `X`, where `h = f ≫ g`. The two tensor
powers are compared through `AlgebraicGeometry.Scheme.Modules.pullbackCompObjIso`. -/
def transportSection (n : ℕ)
    (t : (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
      ((Scheme.Modules.pullback g).obj M) (n : ℤ)).sections) :
    (tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullback h).obj M) (n : ℤ)).sections :=
  SheafOfModules.sectionsMap (tensorPowerCongr X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property _ _
      (Scheme.Modules.pullbackCompObjIso f g h hh M) n).hom
    (Scheme.Modules.pullbackPowerSection f ((Scheme.Modules.pullback g).obj M) n t)

/-- The nonvanishing locus of a transported section is the preimage of the nonvanishing locus. -/
theorem nonvanishingOpen_transportSection (n : ℕ)
    (t : (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
      ((Scheme.Modules.pullback g).obj M) (n : ℤ)).sections) :
    nonvanishingOpen (X := X.toRingedSpace) _ (transportSection f g h hh M n t) =
      f ⁻¹ᵁ nonvanishingOpen (X := Y.toRingedSpace) _ t := by
  rw [← Scheme.Modules.nonvanishingOpen_pullbackPowerSection f
    ((Scheme.Modules.pullback g).obj M) n t]
  exact TopologicalSpace.Opens.ext (Stacks.SheafOfModules.nonvanishingLocus_sectionsMap
    X.toRingedSpace _ _)

end Transport

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

section Hypotheses

variable (j : I) (M : (D.obj j).Modules)
  [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj j).toRingedSpace.presheaf
    (structureSheafRing (D.obj j).toRingedSpace).property M]

/-- **[Stacks Project, Tag 01Z0] for the tensor powers of an invertible module**, in its
surjectivity half and for the cone `c`: every global section of the `n`th tensor power of the
pullback of `M` to `c.pt` is the transport of a global section of the `n`th tensor power of the
pullback of `M` to some stage over `j`.

This is the statement Tag 01Z0 makes for `ℱ₀ = M^{⊗ n}`. Mathlib has it only for
`ℱ₀ = 𝒪`, as `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`. -/
def SectionsDescent : Prop :=
  ∀ (n : ℕ) (s : (tensorPower c.pt.toRingedSpace.presheaf
        (structureSheafRing c.pt.toRingedSpace).property
        ((Scheme.Modules.pullback (c.π.app j)).obj M) (n : ℤ)).sections),
      ∃ (j' : I) (g : j' ⟶ j) (t : (tensorPower (D.obj j').toRingedSpace.presheaf
          (structureSheafRing (D.obj j').toRingedSpace).property
          ((Scheme.Modules.pullback (D.map g)).obj M) (n : ℤ)).sections),
        transportSection (c.π.app j') (D.map g) (c.π.app j) (c.w g).symm M n t = s

/-- The consequence of [Stacks Project, Tag 01Z0] that the descent of ampleness consumes: the
nonvanishing locus of a global section of a tensor power of the pullback of `M` to `c.pt` is
already the preimage of the nonvanishing locus of a section at some stage over `j`. -/
def NonvanishingLocusDescent : Prop :=
  ∀ (n : ℕ) (s : (tensorPower c.pt.toRingedSpace.presheaf
        (structureSheafRing c.pt.toRingedSpace).property
        ((Scheme.Modules.pullback (c.π.app j)).obj M) (n : ℤ)).sections),
      ∃ (j' : I) (g : j' ⟶ j) (t : (tensorPower (D.obj j').toRingedSpace.presheaf
          (structureSheafRing (D.obj j').toRingedSpace).property
          ((Scheme.Modules.pullback (D.map g)).obj M) (n : ℤ)).sections),
        nonvanishingOpen (X := c.pt.toRingedSpace) _ s =
          c.π.app j' ⁻¹ᵁ nonvanishingOpen (X := (D.obj j').toRingedSpace) _ t

/-- Tag 01Z0 for the tensor powers of `M` gives the weak form: the nonvanishing locus of a
transported section is the preimage of the nonvanishing locus. -/
theorem nonvanishingLocusDescent_of_sectionsDescent
    (H : SectionsDescent D c j M) : NonvanishingLocusDescent D c j M := by
  intro n s
  obtain ⟨j', g, t, ht⟩ := H n s
  exact ⟨j', g, t, by rw [← ht, nonvanishingOpen_transportSection]⟩

end Hypotheses

variable [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- In a cofiltered category, finitely many morphisms `g x : a x ⟶ j` become compatible after
precomposing with morphisms `f x : k ⟶ a x` from a common object `k`. -/
private theorem exists_hom_comp_eq {J : Type u} [Category.{u} J] [IsCofiltered J] {α : Type*}
    [Finite α] (a : α → J) (j : J) (g : ∀ x, a x ⟶ j) :
    ∃ (k : J) (f : ∀ x, k ⟶ a x) (f₀ : k ⟶ j), ∀ x, f x ≫ g x = f₀ := by
  classical
  have := Fintype.ofFinite α
  have hx : ∀ x, a x ∈ insert j (Finset.univ.image a) := fun x =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ x))
  obtain ⟨k, f, hk⟩ := IsCofiltered.inf_exists (insert j (Finset.univ.image a))
    (Finset.univ.image fun x => ⟨a x, j, hx x, Finset.mem_insert_self _ _, g x⟩)
  exact ⟨k, fun x => f (hx x), f (Finset.mem_insert_self _ _), fun x =>
    hk (hx x) (Finset.mem_insert_self _ _) (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)⟩

include c in
/-- **[Stacks Project, Tag 09MT], from [Stacks Project, Tag 01Z0] for the tensor powers of the
module.** Let `c` be a limit cone on a cofiltered diagram `D` of quasi-compact quasi-separated
schemes with affine transition morphisms, let `M` be an invertible module on the stage `D.obj j`,
and assume the sections of the tensor powers of the pullback of `M` to `c.pt` descend to stages
(`NonvanishingLocusDescent`, which `nonvanishingLocusDescent_of_sectionsDescent` derives from
Tag 01Z0). If the pullback of `M` to `c.pt` is ample, then the pullback of `M` to some stage over
`j` is ample.

The `@[stacks 09MT]` attribute is **withheld**: the tag asserts its conclusion unconditionally,
and the hypothesis `hdesc` stands in for Tag 01Z0, which this development does not have for a
module other than the structure sheaf. -/
theorem exists_isAmple_pullback_map_of_isLimit (hc : IsLimit c) (j : I) (M : (D.obj j).Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj j).toRingedSpace.presheaf
      (structureSheafRing (D.obj j).toRingedSpace).property M]
    (hdesc : NonvanishingLocusDescent D c j M)
    (hample : Scheme.Modules.IsAmple c.pt ((Scheme.Modules.pullback (c.π.app j)).obj M)) :
    ∃ (j' : I) (g : j' ⟶ j),
      Scheme.Modules.IsAmple (D.obj j') ((Scheme.Modules.pullback (D.map g)).obj M) := by
  classical
  have : CompactSpace c.pt := hample.1
  choose n hn s hxs haff using hample.2
  choose jj gg tt htt using fun x : c.pt => hdesc (n x) (s x)
  obtain ⟨σ, hσ⟩ := CompactSpace.elim_nhds_subcover
    (fun x : c.pt =>
      ((nonvanishingOpen (X := c.pt.toRingedSpace) _ (s x) : c.pt.Opens) : Set c.pt))
    (fun x => (nonvanishingOpen (X := c.pt.toRingedSpace) _ (s x)).2.mem_nhds (hxs x))
  -- Gather the finitely many descended sections at one stage `k`, with the morphisms to `j`
  -- equalised, so that a single module on `D.obj k` carries all of them.
  obtain ⟨k, fk, fk₀, hcomp⟩ := exists_hom_comp_eq (fun x : (σ : Finset c.pt) => jj x.1) j
    fun x => gg x.1
  set t₁ : (x : (σ : Finset c.pt)) → (tensorPower (D.obj k).toRingedSpace.presheaf
      (structureSheafRing (D.obj k).toRingedSpace).property
      ((Scheme.Modules.pullback (D.map (fk₀))).obj M) ((n x.1 : ℕ) : ℤ)).sections :=
    fun x => transportSection (D.map (fk x)) (D.map (gg x.1)) (D.map (fk₀))
      (by rw [← D.map_comp, hcomp x]) M (n x.1) (tt x.1) with ht₁def
  have ht₁ : ∀ x : (σ : Finset c.pt),
      nonvanishingOpen (X := (D.obj k).toRingedSpace) _ (t₁ x) =
        D.map (fk x) ⁻¹ᵁ nonvanishingOpen (X := (D.obj (jj x.1)).toRingedSpace) _ (tt x.1) :=
    fun x => nonvanishingOpen_transportSection _ _ _ _ M _ _
  have hpre₁ : ∀ x : (σ : Finset c.pt),
      c.π.app k ⁻¹ᵁ nonvanishingOpen (X := (D.obj k).toRingedSpace) _ (t₁ x) =
        nonvanishingOpen (X := c.pt.toRingedSpace) _ (s x.1) := by
    intro x
    rw [ht₁ x, ← Scheme.Hom.comp_preimage, c.w (fk x)]
    exact (htt x.1).symm
  -- Each descended nonvanishing locus is quasi-compact with affine preimage, so Tag 01Z6 makes
  -- it affine at a later stage; a second gathering brings those stages together.
  choose j₂ p₂ haff₂ using fun x : (σ : Finset c.pt) =>
    _root_.AlgebraicGeometry.EventualFiniteness.exists_isAffineOpen_map_preimage_of_isLimit
      D c hc (nonvanishingOpen (X := (D.obj k).toRingedSpace) _ (t₁ x))
      (Scheme.Modules.isCompact_nonvanishingOpen _ _) (by rw [hpre₁ x]; exact haff x.1)
  obtain ⟨m, fm, fm₀, hcomp₂⟩ := exists_hom_comp_eq j₂ k p₂
  have haff₃ : ∀ x : (σ : Finset c.pt), IsAffineOpen
      (D.map (fm₀) ⁻¹ᵁ nonvanishingOpen (X := (D.obj k).toRingedSpace) _ (t₁ x)) := by
    intro x
    rw [← hcomp₂ x, D.map_comp, Scheme.Hom.comp_preimage]
    exact (haff₂ x).preimage (D.map (fm x))
  set t₂ : (x : (σ : Finset c.pt)) → (tensorPower (D.obj m).toRingedSpace.presheaf
      (structureSheafRing (D.obj m).toRingedSpace).property
      ((Scheme.Modules.pullback (D.map (fm₀ ≫ fk₀))).obj M) ((n x.1 : ℕ) : ℤ)).sections :=
    fun x => transportSection (D.map (fm₀)) (D.map (fk₀)) (D.map (fm₀ ≫ fk₀))
      (D.map_comp (fm₀) (fk₀)) M (n x.1) (t₁ x) with ht₂def
  have ht₂ : ∀ x : (σ : Finset c.pt),
      nonvanishingOpen (X := (D.obj m).toRingedSpace) _ (t₂ x) =
        D.map (fm₀) ⁻¹ᵁ nonvanishingOpen (X := (D.obj k).toRingedSpace) _ (t₁ x) :=
    fun x => nonvanishingOpen_transportSection _ _ _ _ M _ _
  -- The descended loci cover `c.pt`, hence a later stage, by Tag 01Z4 (3).
  have hcov : c.π.app m ⁻¹ᵁ (⨆ x : (σ : Finset c.pt),
      nonvanishingOpen (X := (D.obj m).toRingedSpace) _ (t₂ x)) = ⊤ := by
    rw [show (c.π.app m ⁻¹ᵁ (⨆ x : (σ : Finset c.pt),
        nonvanishingOpen (X := (D.obj m).toRingedSpace) _ (t₂ x))) =
        ⨆ x : (σ : Finset c.pt), c.π.app m ⁻¹ᵁ
          nonvanishingOpen (X := (D.obj m).toRingedSpace) _ (t₂ x) from
      Opens.map_iSup (c.π.app m).base _]
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun z => ?_)
    obtain ⟨x, hx, hz⟩ := Set.mem_iUnion₂.mp (hσ.ge (Set.mem_univ z))
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, ?_⟩
    rw [ht₂ ⟨x, hx⟩, ← Scheme.Hom.comp_preimage, c.w (fm₀), hpre₁ ⟨x, hx⟩]
    exact hz
  obtain ⟨j₃, r, hr⟩ := _root_.AlgebraicGeometry.exists_map_eq_top D c hc _ hcov
  set t₃ : (x : (σ : Finset c.pt)) → (tensorPower (D.obj j₃).toRingedSpace.presheaf
      (structureSheafRing (D.obj j₃).toRingedSpace).property
      ((Scheme.Modules.pullback (D.map (r ≫ fm₀ ≫ fk₀))).obj M)
        ((n x.1 : ℕ) : ℤ)).sections :=
    fun x => transportSection (D.map r) (D.map (fm₀ ≫ fk₀))
      (D.map (r ≫ fm₀ ≫ fk₀)) (D.map_comp r (fm₀ ≫ fk₀)) M (n x.1) (t₂ x) with ht₃def
  have ht₃ : ∀ x : (σ : Finset c.pt),
      nonvanishingOpen (X := (D.obj j₃).toRingedSpace) _ (t₃ x) =
        D.map r ⁻¹ᵁ nonvanishingOpen (X := (D.obj m).toRingedSpace) _ (t₂ x) :=
    fun x => nonvanishingOpen_transportSection _ _ _ _ M _ _
  refine ⟨j₃, r ≫ fm₀ ≫ fk₀, inferInstance, fun y => ?_⟩
  have hy : (D.map r).base y ∈ ⨆ x : (σ : Finset c.pt),
      nonvanishingOpen (X := (D.obj m).toRingedSpace) _ (t₂ x) := by
    have hmem : y ∈ D.map r ⁻¹ᵁ (⨆ x : (σ : Finset c.pt),
        nonvanishingOpen (X := (D.obj m).toRingedSpace) _ (t₂ x)) := by rw [hr]; trivial
    exact hmem
  obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  refine ⟨n x.1, hn x.1, t₃ x, ?_, ?_⟩
  · rw [ht₃ x]; exact hx
  · rw [ht₃ x, ht₂ x]
    exact (haff₃ x).preimage (D.map r)

include c in
/-- **[Stacks Project, Tag 09MT] from [Stacks Project, Tag 01Z0]**, stated with the hypothesis in
the form Tag 01Z0 has: the sections themselves descend, not merely their nonvanishing loci.

The `@[stacks 09MT]` attribute is **withheld** for the same reason as for
`exists_isAmple_pullback_map_of_isLimit`: `hdesc` stands in for Tag 01Z0 for the tensor powers of
`M`, and this development has Tag 01Z0 only for the structure sheaf (through Mathlib's
`AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`). -/
theorem exists_isAmple_pullback_map_of_sectionsDescent (hc : IsLimit c) (j : I)
    (M : (D.obj j).Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj j).toRingedSpace.presheaf
      (structureSheafRing (D.obj j).toRingedSpace).property M]
    (hdesc : SectionsDescent D c j M)
    (hample : Scheme.Modules.IsAmple c.pt ((Scheme.Modules.pullback (c.π.app j)).obj M)) :
    ∃ (j' : I) (g : j' ⟶ j),
      Scheme.Modules.IsAmple (D.obj j') ((Scheme.Modules.pullback (D.map g)).obj M) :=
  exists_isAmple_pullback_map_of_isLimit D c hc j M
    (nonvanishingLocusDescent_of_sectionsDescent D c j M hdesc) hample

end Stacks.AlgebraicGeometry.AmpleLimit

end
