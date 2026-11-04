module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocal
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocalUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.RingedBigSiteHom
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves

/-!
# Pullback of an adequate module along a morphism of schemes

Let `f : T ⟶ S` be a morphism of schemes. On the big `τ`-sites the pullback map

`f^* : Mod((Sch/S)_τ, 𝒪) ⥤ Mod((Sch/T)_τ, 𝒪)`

is given by *restriction*: a scheme `V` over `T` is a scheme over `S` by composing with `f`, and
`f^*𝓕(V) = 𝓕(V)`. This module makes that precise and derives from it that the pullback of an
adequate `𝒪`-module is adequate, which is [Stacks, Tag 06VJ].

The reason the pullback is a plain restriction, with no change of scalars, is that the structure
sheaf of a big site is the sheaf of *global functions on the underlying scheme*,
`Stacks.Sites.structurePresheaf`, which does not refer to the base at all. So the structure sheaf
of `(Sch/T)_τ` is literally the restriction of the structure sheaf of `(Sch/S)_τ` along the
index functor, and `f^*` is `PresheafOfModules.pushforward₀`, precomposition with the index
functor, rather than a tensor product.

## Main definitions

* `Stacks.Adequate.BigSite.baseChange` — the big `τ`-site over `T` whose cardinal cutoff is that
  of a given big `τ`-site over `S`. The two sites are then slices of one category of schemes, as
  they are in the source, where `(Sch/S)_τ` and `(Sch/T)_τ` are slices of a single `Sch_α`.
* `Stacks.Adequate.BigSite.ofAmbient` — the chosen big `τ`-site at a scheme below the cutoff of
  an ambient big `τ`-site `𝒮`, namely the localization of `𝒮` there. This is `Sch_α` with a
  base chosen in it, and it needs no hypotheses: its sheaf condition for the structure presheaf
  is [Stacks, Tag 03DU], `AlgebraicGeometry.bigSite_structure_isSheaf`.
* `Stacks.Adequate.pullbackIndex` — the index functor `(Sch/T)_τ ⥤ (Sch/S)_τ`, which sends a
  scheme over `T` to the same scheme over `S` via `f`. It is `Over.map`.
* `Stacks.Adequate.pullbackVal` — the pullback `f^*𝓕` as a presheaf of modules: the restriction
  of `𝓕` along `pullbackIndex`, with no change of scalars.
* `Stacks.Adequate.pullbackSheaf` — `f^*𝓕` as a sheaf of modules, given the sheaf condition for
  the restriction.
* `Stacks.Adequate.pullbackSheafOfAmbient` — `f^*𝓕` as a sheaf of modules when the two sites are
  the localizations of one ambient big site at `S` and at `T`, where the sheaf condition is
  supplied rather than assumed.

## Main results

* `Stacks.Adequate.pullbackIndex_op_comp_structureSheaf` — the structure sheaf of the big site
  over `T` *is* the restriction along the index functor of the structure sheaf of the big site
  over `S`. This is why `f^*` requires no change of scalars.
* `Stacks.Adequate.pullbackVal_obj` and `Stacks.Adequate.pullbackVal_map` — the source's formula
  `f^*𝓕(V) = 𝓕(V)`, and the matching identity for the restriction maps.
* `Stacks.Adequate.BigSite.exists_eq_ofAmbient` — *every* chosen big site is the localization of
  an ambient big site at its base. So quantifying over `BigSite.ofAmbient 𝒮 S hS` loses no
  generality over quantifying over `BigSite τ S`.
* `Stacks.Adequate.isSheaf_pullbackVal` — the restriction `f^*𝓕` of a sheaf of modules is a
  sheaf, when the sites over `S` and over `T` are the localizations of one ambient big site.
  This is the sheaf-condition half of the source's "`f^*` is given by restriction".
* `Stacks.Adequate.affineSectionFunctor_pullbackSheaf` — the affine-section functor of `f^*𝓕` at
  an affine scheme `Spec A` over `T` *is* the affine-section functor of `𝓕` at `Spec A` over `S`:
  `F_{f^*𝓕, A} = F_{𝓕, A}`. This is the whole mathematical content of the source's proof of
  Tag 06VJ, and it holds unconditionally, by definitional unfolding.
* `Stacks.Adequate.isAdequate_pullbackSheafOfAmbient` — [Stacks, Tag 06VJ]: the pullback of an
  adequate `𝒪`-module is adequate.

## Implementation notes

The affine schemes over `T` used to witness adequacy of `f^*𝓕` are *all* affine schemes of the
site over `T`, not only those coming from a covering of `S`, because a covering
`{Spec(A_i) → S}` of `S` need not pull back to a covering of `T` by affine schemes: the fibre
products `T ×_S Spec(A_i)` are not affine. This is why the source's proof invokes Tag 06VI,
which upgrades adequacy of the affine-section functors from the members of one covering to every
affine scheme over the base.

Two forms of the statement are given. The general one,
`Stacks.Adequate.isAdequate_pullbackSheaf`, takes the topology of the site over `T` as an
argument, and with it the sheaf condition `hsh` for the restricted module: an arbitrary
`Stacks.Adequate.BigSite` over `T` records compatibility of its topology only with the accepted
big-site construction over `T` itself, so its coverings bear no relation to those of the site
over `S`, and the restriction of a sheaf along `pullbackIndex` need not be one. The source's
assertion that `f^*` "is given by restriction" presupposes that it is.

The source's own situation is sharper: `(Sch/S)_τ` and `(Sch/T)_τ` are the localizations at `S`
and at `T` of a *single* `Sch_α`. In that situation the sheaf condition is a theorem, not a
hypothesis. `Stacks.Adequate.isSheaf_pullbackVal` proves it: the topology of a localized big site
is the localization of the topology of the big site
(`AlgebraicGeometry.overTopology_eq_siteTopology_over`), and `Over.map` between two slices of one
site with their localized topologies is continuous, so composing with its opposite carries
sheaves to sheaves. `Stacks.Adequate.isAdequate_pullbackSheafOfAmbient` is the resulting form of
Tag 06VJ, and it assumes no sheaf condition. By
`Stacks.Adequate.BigSite.exists_eq_ofAmbient` every chosen big site is of this form, so this is
the full strength of the source's statement and not a special case of it.

`Stacks.Adequate.isAdequate_pullbackSheafOfAmbient` assumes nothing beyond adequacy of `𝓕`.
It does not inherit the hypothesis `Stacks.Adequate.StandardAffineDescent` through the source's
own appeal to Tag 06VI: that hypothesis is the theorem
`Stacks.Adequate.standardAffineDescent`, so Tag 06VI,
`Stacks.Adequate.isAdequate_affineSectionFunctor`, is unconditional and nothing is inherited.
All three steps of Tag 06VI's proof are theorems —
`Stacks.Adequate.standardAffineRefinement`, `Stacks.Adequate.affineSectionRestriction` and
`Stacks.Adequate.standardAffineDescent`.

The content that Tag 06VJ's own proof contributes, over and above Tag 06VI, is exactly
`Stacks.Adequate.affineSectionFunctor_pullbackSheaf`,
`Stacks.Adequate.pullbackIndex_op_comp_structureSheaf` and
`Stacks.Adequate.isSheaf_pullbackVal`, and all three are proved here outright, with no
hypotheses at all.

## References

* [Stacks Project, Tag 06VJ](https://stacks.math.columbia.edu/tag/06VJ)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06VG](https://stacks.math.columbia.edu/tag/06VG)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S T : Scheme.{u}}

/-- The big `τ`-site over `T` with the cardinal cutoff of a given big `τ`-site `B` over `S`.
Sharing the cutoff makes the two sites slices of one category of schemes, which is the situation
of the source: there `(Sch/S)_τ` and `(Sch/T)_τ` are the slices of a single `Sch_α`. -/
public def BigSite.baseChange (B : BigSite τ S) (hT : schemeSizeBelow B.cutoff T)
    (J : GrothendieckTopology (Over (⟨T, hT⟩ : SchemeBelow B.cutoff)))
    (hJ : Presheaf.IsSheaf J
      (Stacks.Sites.structurePresheaf T
        (Over.post (ObjectProperty.ι (schemeSizeBelow B.cutoff)))))
    (hchosen :
      (τ = .zariski ∧ ∃ Z : BigZariskiSite.{u}, ∃ hTZ : Z.Contains T,
          ∃ _e : Z.schemeCardinal = B.cutoff, HEq J (BigZariskiOver.topology Z T hTZ)) ∨
      (τ = .etale ∧ ∃ E : BigEtaleSite.{u}, ∃ hTE : E.Contains T,
          ∃ _e : E.cutoff = B.cutoff, HEq J (BigEtaleOver.topology E T hTE)) ∨
      (τ = .fppf ∧ ∃ P : BigFppfSite.{u}, ∃ hTP : P.Contains T,
          ∃ _e : P.cutoff = B.cutoff, HEq J (BigFppfOver.topology P T hTP)) ∨
      (τ = .smooth ∧ ∃ M : BigSmoothSite.{u}, ∃ hTM : T.size < M.cutoff,
          ∃ _e : M.cutoff = B.cutoff, HEq J (BigSmoothOver.topology M T hTM)) ∨
      (τ = .syntomic ∧ ∃ Y : BigSyntomicSite.{u}, ∃ hTY : Y.Contains T,
          ∃ _e : Y.cutoff = B.cutoff, HEq J (BigSyntomicOver.topology Y T hTY))) :
    BigSite τ T where
  cutoff := B.cutoff
  base_mem := hT
  topology := J
  isSheaf := hJ
  chosen := hchosen

section

variable (B : BigSite τ S) (hT : schemeSizeBelow B.cutoff T)
  (J : GrothendieckTopology (Over (⟨T, hT⟩ : SchemeBelow B.cutoff)))
  (hJ : Presheaf.IsSheaf J
    (Stacks.Sites.structurePresheaf T
      (Over.post (ObjectProperty.ι (schemeSizeBelow B.cutoff)))))
  (hchosen :
    (τ = .zariski ∧ ∃ Z : BigZariskiSite.{u}, ∃ hTZ : Z.Contains T,
        ∃ _e : Z.schemeCardinal = B.cutoff, HEq J (BigZariskiOver.topology Z T hTZ)) ∨
    (τ = .etale ∧ ∃ E : BigEtaleSite.{u}, ∃ hTE : E.Contains T,
        ∃ _e : E.cutoff = B.cutoff, HEq J (BigEtaleOver.topology E T hTE)) ∨
    (τ = .fppf ∧ ∃ P : BigFppfSite.{u}, ∃ hTP : P.Contains T,
        ∃ _e : P.cutoff = B.cutoff, HEq J (BigFppfOver.topology P T hTP)) ∨
    (τ = .smooth ∧ ∃ M : BigSmoothSite.{u}, ∃ hTM : T.size < M.cutoff,
        ∃ _e : M.cutoff = B.cutoff, HEq J (BigSmoothOver.topology M T hTM)) ∨
    (τ = .syntomic ∧ ∃ Y : BigSyntomicSite.{u}, ∃ hTY : Y.Contains T,
        ∃ _e : Y.cutoff = B.cutoff, HEq J (BigSyntomicOver.topology Y T hTY)))
  (f : T ⟶ S)

/-- The index functor of the pullback: a scheme over `T` belonging to the site is a scheme over
`S` belonging to the site, via `f`. -/
public abbrev pullbackIndex : (B.baseChange hT J hJ hchosen).category ⥤ B.category :=
  Over.map (ObjectProperty.homMk f)

/-- The structure sheaf of the big site over `T` is the restriction along the index functor of
the structure sheaf of the big site over `S`. Both assign to a scheme of the site its ring of
global functions, which does not refer to the base; this is why the pullback `f^*` below is a
restriction and involves no change of scalars. -/
public theorem pullbackIndex_op_comp_structureSheaf :
    (pullbackIndex B hT J hJ hchosen f).op ⋙ B.structureSheaf.obj =
      (B.baseChange hT J hJ hchosen).structureSheaf.obj := rfl

/-- The pullback `f^*𝓕` of a presheaf of modules on the big site over `S`, as a presheaf of
modules on the big site over `T`: the restriction of `𝓕` along the index functor, with no change
of scalars. -/
public noncomputable def pullbackVal (F : SheafOfModules.{m} B.structureSheaf) :
    PresheafOfModules.{m} (B.baseChange hT J hJ hchosen).structureSheaf.obj :=
  (PresheafOfModules.pushforward₀.{m} (pullbackIndex B hT J hJ hchosen f)
    B.structureSheaf.obj).obj F.val

/-- `f^*𝓕(V) = 𝓕(V)` for a scheme `V` over `T`, viewed over `S` via `f`. -/
public theorem pullbackVal_obj (F : SheafOfModules.{m} B.structureSheaf)
    (V : (B.baseChange hT J hJ hchosen).categoryᵒᵖ) :
    ((pullbackVal B hT J hJ hchosen f F).obj V : Type m) =
      (F.val.obj ((pullbackIndex B hT J hJ hchosen f).op.obj V) : Type m) := rfl

/-- The restriction maps of `f^*𝓕` are those of `𝓕`. -/
public theorem pullbackVal_map (F : SheafOfModules.{m} B.structureSheaf)
    {V W : (B.baseChange hT J hJ hchosen).categoryᵒᵖ} (g : V ⟶ W)
    (x : (pullbackVal B hT J hJ hchosen f F).obj V) :
    (pullbackVal B hT J hJ hchosen f F).map g x =
      F.val.map ((pullbackIndex B hT J hJ hchosen f).op.map g) x := rfl

/-- The pullback `f^*𝓕` as a sheaf of modules on the big site over `T`, given the sheaf condition
for the restriction. The source's assertion that `f^*` "is given by restriction" presupposes that
condition; see the module documentation. -/
public noncomputable def pullbackSheaf (F : SheafOfModules.{m} B.structureSheaf)
    (hsh : Presheaf.IsSheaf (B.baseChange hT J hJ hchosen).topology
      (pullbackVal B hT J hJ hchosen f F).presheaf) :
    SheafOfModules.{m} (B.baseChange hT J hJ hchosen).structureSheaf :=
  ⟨pullbackVal B hT J hJ hchosen f F, hsh⟩

/-- **The affine-section functors of `f^*𝓕` are those of `𝓕`:** for an affine scheme `Spec A` of
the site over `T` by `g`, the functor `F_{f^*𝓕, A}` on `A`-algebras of the site equals the
functor `F_{𝓕, A}` attached to `Spec A` over `S` by `g ≫ f`.

This is the whole content of the source's proof of [Stacks, Tag 06VJ] beyond its appeal to
[Stacks, Tag 06VI]: both sides restrict `𝓕` along the same functor from `A`-algebras of the site
to schemes over `S`, and both restrict scalars along the same identification of `A`-algebras with
global functions on their spectra. -/
public theorem affineSectionFunctor_pullbackSheaf (F : SheafOfModules.{m} B.structureSheaf)
    (hsh : Presheaf.IsSheaf (B.baseChange hT J hJ hchosen).topology
      (pullbackVal B hT J hJ hchosen f F).presheaf)
    (A : CommRingCat.{u}) (g : Spec A ⟶ T) :
    affineSectionFunctor (B.baseChange hT J hJ hchosen)
        (pullbackSheaf B hT J hJ hchosen f F hsh) A g =
      affineSectionFunctor B F A (g ≫ f) := rfl

/-- The pullback `f^*𝓕` of an adequate `𝒪`-module `𝓕` on `(Sch/S)_τ` is an adequate
`𝒪`-module on `(Sch/T)_τ`, for an arbitrary chosen big site over `T`.

Every affine scheme `Spec A` of the site over `T` is an affine scheme of the site over `S`, and
by `affineSectionFunctor_pullbackSheaf` the affine-section functor of `f^*𝓕` there is the
affine-section functor of `𝓕`, which [Stacks, Tag 06VI] shows to be adequate. Adequacy of
`f^*𝓕` then follows because the affine open cover of `T` is a `τ`-covering by affine schemes of
the site.

The only hypothesis is `hsh`, the sheaf condition for the restriction, which an arbitrary site
over `T` does not supply. `isAdequate_pullbackSheafOfAmbient` is the form of [Stacks, Tag 06VJ]
carrying the attribute: there the two sites are the localizations of one ambient big site, as
they are in the source, and `hsh` is discharged by `isSheaf_pullbackVal`. -/
public theorem isAdequate_pullbackSheaf (F : SheafOfModules.{max u m} B.structureSheaf)
    (hF : IsAdequate B F)
    (hsh : Presheaf.IsSheaf (B.baseChange hT J hJ hchosen).topology
      (pullbackVal B hT J hJ hchosen f F).presheaf) :
    IsAdequate (B.baseChange hT J hJ hchosen)
      (pullbackSheaf B hT J hJ hchosen f F hsh) := by
  refine isAdequate_of_forall_affineSectionFunctor _ _ fun A g hA => ?_
  rw [affineSectionFunctor_pullbackSheaf]
  exact isAdequate_affineSectionFunctor B F hF A (g ≫ f) hA

end

/-! ### The two sites as localizations of one ambient big site -/

/-- The localized topology of an ambient big `τ`-site at a scheme `T` below its cutoff is the
topology of a chosen big site over `T`: it is the topology of the accepted big-site
construction for `τ`, on the nose. -/
public theorem BigSite.chosen_overTopology (𝒮 : AlgebraicGeometry.BigSite.{u} τ) (T : Scheme.{u})
    (hT : T.size < AlgebraicGeometry.cutoff τ 𝒮) :
    (τ = .zariski ∧ ∃ Z : BigZariskiSite.{u}, ∃ hTZ : Z.Contains T,
        ∃ _e : Z.schemeCardinal = AlgebraicGeometry.cutoff τ 𝒮,
          HEq (AlgebraicGeometry.overTopology τ 𝒮 T hT) (BigZariskiOver.topology Z T hTZ)) ∨
    (τ = .etale ∧ ∃ E : BigEtaleSite.{u}, ∃ hTE : E.Contains T,
        ∃ _e : E.cutoff = AlgebraicGeometry.cutoff τ 𝒮,
          HEq (AlgebraicGeometry.overTopology τ 𝒮 T hT) (BigEtaleOver.topology E T hTE)) ∨
    (τ = .fppf ∧ ∃ P : BigFppfSite.{u}, ∃ hTP : P.Contains T,
        ∃ _e : P.cutoff = AlgebraicGeometry.cutoff τ 𝒮,
          HEq (AlgebraicGeometry.overTopology τ 𝒮 T hT) (BigFppfOver.topology P T hTP)) ∨
    (τ = .smooth ∧ ∃ M : BigSmoothSite.{u}, ∃ hTM : T.size < M.cutoff,
        ∃ _e : M.cutoff = AlgebraicGeometry.cutoff τ 𝒮,
          HEq (AlgebraicGeometry.overTopology τ 𝒮 T hT) (BigSmoothOver.topology M T hTM)) ∨
    (τ = .syntomic ∧ ∃ Y : BigSyntomicSite.{u}, ∃ hTY : Y.Contains T,
        ∃ _e : Y.cutoff = AlgebraicGeometry.cutoff τ 𝒮,
          HEq (AlgebraicGeometry.overTopology τ 𝒮 T hT) (BigSyntomicOver.topology Y T hTY)) := by
  cases τ with
  | zariski => exact Or.inl ⟨rfl, 𝒮, hT, rfl, HEq.rfl⟩
  | etale => exact Or.inr (Or.inl ⟨rfl, 𝒮, hT, rfl, HEq.rfl⟩)
  | fppf => exact Or.inr (Or.inr (Or.inl ⟨rfl, 𝒮, hT, rfl, HEq.rfl⟩))
  | smooth => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, 𝒮, hT, rfl, HEq.rfl⟩)))
  | syntomic => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, 𝒮, hT, rfl, HEq.rfl⟩)))

/-- The chosen big `τ`-site at a scheme `T` below the cutoff of an ambient big `τ`-site `𝒮`:
the localization of `𝒮` at `T`. This is the source's `(Sch/T)_τ` for a fixed `Sch_α`, and it
takes no hypotheses — its sheaf condition for the presheaf of global functions is
[Stacks, Tag 03DU], `AlgebraicGeometry.bigSite_structure_isSheaf`. -/
public def BigSite.ofAmbient (𝒮 : AlgebraicGeometry.BigSite.{u} τ)
    (T : Scheme.{u}) (hT : T.size < AlgebraicGeometry.cutoff τ 𝒮) :
    BigSite τ T where
  cutoff := AlgebraicGeometry.cutoff τ 𝒮
  base_mem := hT
  topology := AlgebraicGeometry.overTopology τ 𝒮 T hT
  isSheaf := AlgebraicGeometry.bigSite_structure_isSheaf 𝒮 T hT
  chosen := BigSite.chosen_overTopology 𝒮 T hT

/-- A chosen big site is determined by its cutoff and its topology: the three remaining fields
are propositions. -/
public theorem BigSite.ext_of_cutoff_eq {B₁ B₂ : BigSite τ S}
    (hc : B₁.cutoff = B₂.cutoff) (ht : HEq B₁.topology B₂.topology) : B₁ = B₂ := by
  obtain ⟨κ₁, m₁, J₁, s₁, c₁⟩ := B₁
  obtain ⟨κ₂, m₂, J₂, s₂, c₂⟩ := B₂
  subst hc
  cases ht
  rfl

/-- **Every chosen big site is the localization of an ambient big site at its base.** This is
what the `chosen` field of `Stacks.Adequate.BigSite` says, read as a construction: so a
statement made for every `BigSite.ofAmbient 𝒮 S hS` is a statement made for every
`BigSite τ S`. -/
public theorem BigSite.exists_eq_ofAmbient (B : BigSite τ S) :
    ∃ (𝒮 : AlgebraicGeometry.BigSite.{u} τ) (hS : S.size < AlgebraicGeometry.cutoff τ 𝒮),
      BigSite.ofAmbient 𝒮 S hS = B := by
  cases τ <;>
  rcases B.chosen with ⟨h, 𝒮, hS, e, ht⟩ | ⟨h, 𝒮, hS, e, ht⟩ | ⟨h, 𝒮, hS, e, ht⟩ |
      ⟨h, 𝒮, hS, e, ht⟩ | ⟨h, 𝒮, hS, e, ht⟩ <;>
  first
  | exact ⟨𝒮, hS, BigSite.ext_of_cutoff_eq e ht.symm⟩
  | simp at h

/-! ### The pullback between two localizations of one ambient big site -/

section Ambient

variable (𝒮 : AlgebraicGeometry.BigSite.{u} τ)
  (hS : S.size < AlgebraicGeometry.cutoff τ 𝒮)
  (hT : T.size < AlgebraicGeometry.cutoff τ 𝒮)

/-- Base change of the localization of `𝒮` at `S`, along the localized topology of `𝒮` at `T`,
is the localization of `𝒮` at `T`. -/
public theorem BigSite.baseChange_ofAmbient :
    (BigSite.ofAmbient 𝒮 S hS).baseChange hT
        (AlgebraicGeometry.overTopology τ 𝒮 T hT)
        (AlgebraicGeometry.bigSite_structure_isSheaf 𝒮 T hT)
        (BigSite.chosen_overTopology 𝒮 T hT) = BigSite.ofAmbient 𝒮 T hT := rfl

/-- **The restriction of a sheaf of modules is a sheaf**, when the site over `T` and the site
over `S` are the localizations of one ambient big site `𝒮`. This is the sheaf-condition half of
the source's "`f^*` is given by restriction", and it is proved here outright.

The topology of a localized big site is the localization of the topology of `𝒮`
(`AlgebraicGeometry.overTopology_eq_siteTopology_over`), and `Over.map` between two slices of
one site, each carrying its localized topology, is continuous; so composing with its opposite
carries sheaves to sheaves. -/
public theorem isSheaf_pullbackVal (f : T ⟶ S)
    (F : SheafOfModules.{m} (BigSite.ofAmbient 𝒮 S hS).structureSheaf) :
    Presheaf.IsSheaf (AlgebraicGeometry.overTopology τ 𝒮 T hT)
      (pullbackVal (BigSite.ofAmbient 𝒮 S hS) hT
        (AlgebraicGeometry.overTopology τ 𝒮 T hT)
        (AlgebraicGeometry.bigSite_structure_isSheaf 𝒮 T hT)
        (BigSite.chosen_overTopology 𝒮 T hT) f F).presheaf := by
  have hpre : (pullbackVal (BigSite.ofAmbient 𝒮 S hS) hT
        (AlgebraicGeometry.overTopology τ 𝒮 T hT)
        (AlgebraicGeometry.bigSite_structure_isSheaf 𝒮 T hT)
        (BigSite.chosen_overTopology 𝒮 T hT) f F).presheaf =
      (Over.map (ObjectProperty.homMk (P := schemeSizeBelow (AlgebraicGeometry.cutoff τ 𝒮))
        (X := ⟨T, hT⟩) (Y := ⟨S, hS⟩) f)).op ⋙ F.val.presheaf := rfl
  rw [hpre]
  have hF : Presheaf.IsSheaf (AlgebraicGeometry.overTopology τ 𝒮 S hS) F.val.presheaf :=
    F.isSheaf
  rw [AlgebraicGeometry.overTopology_eq_siteTopology_over] at hF ⊢
  exact Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ hF

/-- The pullback `f^*𝓕` as a sheaf of modules on the localization of `𝒮` at `T`. Unlike
`pullbackSheaf`, this takes no sheaf condition: `isSheaf_pullbackVal` supplies it. -/
public noncomputable abbrev pullbackSheafOfAmbient (f : T ⟶ S)
    (F : SheafOfModules.{m} (BigSite.ofAmbient 𝒮 S hS).structureSheaf) :
    SheafOfModules.{m} (BigSite.ofAmbient 𝒮 T hT).structureSheaf :=
  pullbackSheaf (BigSite.ofAmbient 𝒮 S hS) hT
    (AlgebraicGeometry.overTopology τ 𝒮 T hT)
    (AlgebraicGeometry.bigSite_structure_isSheaf 𝒮 T hT)
    (BigSite.chosen_overTopology 𝒮 T hT) f F (isSheaf_pullbackVal 𝒮 hS hT f F)

/-- [Stacks, Tag 06VJ]: the pullback `f^*𝓕` of an adequate `𝒪`-module `𝓕` on `(Sch/S)_τ` is an
adequate `𝒪`-module on `(Sch/T)_τ`, where `(Sch/S)_τ` and `(Sch/T)_τ` are the localizations at
`S` and at `T` of one ambient big `τ`-site, as they are in the source.

The pullback is the restriction of `𝓕` along the index functor, which is a sheaf by
`isSheaf_pullbackVal`; its affine-section functor at an affine `Spec A` over `T` is the
affine-section functor of `𝓕` at `Spec A` over `S` by `affineSectionFunctor_pullbackSheaf`,
which [Stacks, Tag 06VI] shows to be adequate; and adequacy of `f^*𝓕` follows because the
affine open cover of `T` is a `τ`-covering by affine schemes of the site.

By `BigSite.exists_eq_ofAmbient` every chosen big site is a localization of an ambient big
site, so no generality is lost in stating the lemma this way.

Nothing is assumed beyond adequacy of `𝓕`: Tag 06VI is itself unconditional, so the appeal to
it in the source's proof carries no hypothesis here either. See the module documentation. -/
@[stacks 06VJ "the pullback of an adequate 𝒪-module along a morphism of schemes is adequate,
for the two sites the localizations of one ambient big site, as they are in the source"]
public theorem isAdequate_pullbackSheafOfAmbient (f : T ⟶ S)
    (F : SheafOfModules.{max u m} (BigSite.ofAmbient 𝒮 S hS).structureSheaf)
    (hF : IsAdequate (BigSite.ofAmbient 𝒮 S hS) F) :
    IsAdequate (BigSite.ofAmbient 𝒮 T hT) (pullbackSheafOfAmbient 𝒮 hS hT f F) :=
  isAdequate_pullbackSheaf (BigSite.ofAmbient 𝒮 S hS) hT _ _ _ f F hF
    (isSheaf_pullbackVal 𝒮 hS hT f F)

end Ambient

end Stacks.Adequate

end
