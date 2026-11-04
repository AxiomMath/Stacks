module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The big fppf site is subcanonical

A Grothendieck topology is *subcanonical* when every representable presheaf is a sheaf for
it. Mathlib knows that the fppf topology on the category of *all* schemes is subcanonical,
and that a localization `J.over X` of a subcanonical topology is subcanonical. A big fppf
site is neither of these: it is carried by the size-bounded full subcategory `Sch_κ` of
schemes, with a *chosen* set-sized system of covering families, so the statement has to be
transported across the inclusion `Sch_κ ⥤ Sch`.

The transport is not a dense-subsite argument. `Sch_κ` is *not* dense in `Sch`: a scheme
whose ring of global sections exceeds the cutoff has no open covering by schemes of size
below the cutoff, so there is no cover-dense functor to appeal to. What makes the transport
work instead is that `Sch_κ` is a *full* subcategory closed under fibre products, so for an
object `Z` of the site the representable `yoneda.obj Z` is the restriction along the
inclusion of the representable `yoneda.obj Z` on all schemes, and restriction along a
functor preserving the relevant fibre products does not change the sheaf condition for a
covering family of the subcategory. The sheaf condition is then read off from the fppf
sheaf condition in `Sch`, which Mathlib supplies.

This file isolates that argument as a statement about an arbitrary fully faithful functor
and then applies it to the big fppf site and to its localization over a contained scheme.
The big étale and big smooth sites are built the same way and can reuse the general
statement; for them the subcanonicality of the ambient topology on `Sch` is not a Mathlib
instance but follows from `CategoryTheory.GrothendieckTopology.Subcanonical.of_le` applied
to `AlgebraicGeometry.Scheme.etalePrecoverage_le_fppfPrecoverage` and
`AlgebraicGeometry.Scheme.smoothPrecoverage_le_fppfPrecoverage`.

## Main results

* `CategoryTheory.Precoverage.subcanonical_toGrothendieck_of_fullyFaithful`: a precoverage
  whose covering families become covering under a fully faithful functor preserving fibre
  products, and which is stable under base change up to refinement, generates a
  subcanonical topology as soon as the target precoverage generates one.
* `AlgebraicGeometry.BigFppfSite.subcanonical_topology`: the topology of a big fppf site is
  subcanonical.
* `AlgebraicGeometry.BigFppfOver.subcanonical_topology`: the topology of the big fppf site
  of a scheme contained in a big fppf site is subcanonical.
* `AlgebraicGeometry.BigFppfOver.isSheaf_pullback_yoneda_obj`: a fibre product of a sheaf
  over a sheaf along a morphism from a representable presheaf is a sheaf. This is the form
  in which the sheaf condition of a representable is consumed by the descent arguments for
  algebraic spaces.

## Implementation notes

The chosen covering families of a big fppf site are stable under base change in Mathlib's
strict sense (`CategoryTheory.Precoverage.IsStableUnderBaseChange`), even though a different
choice of fibre products gives a different presieve, and the étale case is proved: `IsStableUnderBaseChange` asks only that the base-changed presieve
be presented by *some* chosen family, and a combinatorially equivalent chosen family has the
*same* presieve, so
`AlgebraicGeometry.Space.exists_chosen_etaleCovering` supplies it. See
`AlgebraicGeometry.BigFppfSite.etalePrecoverage_isStableUnderBaseChange` in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence`. The same argument applies
verbatim to the fppf, Zariski and smooth chosen families, whose instances are not yet
stated only because nothing has needed them.

Nothing below depends on the strict form: what this file uses is the weaker coverage axiom —
a chosen family refining the base change — and that is all the sheaf condition needs, so the
argument goes through
`CategoryTheory.Coverage` rather than through base-change stability.

## References

* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 03O3](https://stacks.math.columbia.edu/tag/03O3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u₁ u₂ u

namespace CategoryTheory

/-! ### Site-independent input

Three general facts, stated for an arbitrary site: a fully faithful functor identifies a
representable presheaf with the restriction of a representable presheaf on the target
category; subcanonicality therefore transports along such a functor whenever it preserves
the fibre products the sheaf condition refers to; and a fibre product of sheaves of types,
formed in presheaves, is again a sheaf. -/

/-- For a fully faithful functor `F`, the canonical map
`yoneda.obj X ⟶ F.op ⋙ yoneda.obj (F.obj X)` of `CategoryTheory.yonedaMap` is an
isomorphism: a morphism `Y ⟶ X` is the same thing as a morphism `F.obj Y ⟶ F.obj X`. -/
noncomputable def Functor.yonedaMapIso {C : Type u₁} [Category.{v} C] {D : Type u₂}
    [Category.{v} D] (F : C ⥤ D) [F.Full] [F.Faithful] (X : C) :
    yoneda.obj X ≅ F.op ⋙ yoneda.obj (F.obj X) := by
  have (Y : Cᵒᵖ) : IsIso ((yonedaMap F X).app Y) :=
    (isIso_iff_bijective _).2 ⟨F.map_injective, F.map_surjective⟩
  have : IsIso (yonedaMap F X) := NatIso.isIso_of_isIso_app _
  exact asIso (yonedaMap F X)

/-- The forward map of `Functor.yonedaMapIso F X` is `CategoryTheory.yonedaMap F X`. -/
@[simp]
lemma Functor.yonedaMapIso_hom {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (X : C) :
    (F.yonedaMapIso X).hom = yonedaMap F X :=
  rfl

/-- Subcanonicality transported along a fully faithful functor.

Let `F : C ⥤ D` be fully faithful, let `C` have fibre products and let `F` preserve them.
Let `K` be a precoverage on `C` which is below the comap along `F` of a precoverage `J` on
`D` generating a subcanonical topology — that is, every `K`-covering family becomes a
`J`-covering family — and suppose that every base change of a `K`-covering family is refined
by a `K`-covering family. Then the topology generated by `K` is subcanonical.

The refinement hypothesis is the coverage axiom; it is strictly weaker than
`CategoryTheory.Precoverage.IsStableUnderBaseChange`, which a system of *chosen* covering
families does not satisfy. -/
theorem Precoverage.subcanonical_toGrothendieck_of_fullyFaithful {C : Type u₁} [Category.{v} C]
    {D : Type u₂} [Category.{v} D] (K : Precoverage C) (J : Precoverage D) (F : C ⥤ D)
    [F.Full] [F.Faithful] [Limits.HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan F]
    [J.toGrothendieck.Subcanonical]
    (hle : K ≤ J.comap F)
    (hrefine : ∀ {X Y : C} (f : Y ⟶ X) (R : Presieve X), R ∈ K X →
      ∃ T ∈ K Y, T.FactorsThruAlong R f) :
    K.toGrothendieck.Subcanonical := by
  let L : Coverage C := { toPrecoverage := K, pullback := @fun _ _ f R hR => hrefine f R hR }
  have hL : L.toGrothendieck = K.toGrothendieck := L.toGrothendieck_toPrecoverage.symm
  refine GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun Z => ?_
  rw [← hL, Presieve.isSheaf_coverage]
  intro X R hR
  exact Presieve.isSheafFor_iso (F.yonedaMapIso Z).symm
    ((Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks F (yoneda.obj (F.obj Z)) R).2
      ((GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := J.toGrothendieck) _).isSheafFor_of_mem_precoverage (hle _ hR)))

/-- A fibre product of sheaves, formed in presheaves, is a sheaf.

Sheaves are closed under limits, and the inclusion of sheaves into presheaves creates them,
so the presheaf fibre product is canonically isomorphic to the fibre product taken in
sheaves. -/
theorem Presheaf.isSheaf_pullback {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)
    {A : Type*} [Category A] [Limits.HasPullbacks A] {X Y Z : Cᵒᵖ ⥤ A}
    (f : X ⟶ Z) (g : Y ⟶ Z) (hX : Presheaf.IsSheaf J X)
    (hY : Presheaf.IsSheaf J Y) (hZ : Presheaf.IsSheaf J Z) :
    Presheaf.IsSheaf J (pullback f g) := by
  let f' : (⟨X, hX⟩ : Sheaf J A) ⟶ ⟨Z, hZ⟩ := ObjectProperty.homMk f
  let g' : (⟨Y, hY⟩ : Sheaf J A) ⟶ ⟨Z, hZ⟩ := ObjectProperty.homMk g
  exact (Presheaf.isSheaf_of_iso_iff
    (PreservesPullback.iso (sheafToPresheaf J A) f' g')).mp (Limits.pullback f' g').property

end CategoryTheory

namespace AlgebraicGeometry

namespace BigFppfSite

/-- The coverage axiom for the chosen covering families of a big fppf site: the base change
of a chosen covering family along any morphism of the site is refined by a chosen covering
family.

This is the base change axiom `AlgebraicGeometry.BigFppfSite.isSite` read at the level of
presieves. The fibre products it produces need not be the chosen fibre products of
`Sch_κ`, which is why the conclusion is a refinement rather than an equality of
presieves. -/
theorem exists_mem_precoverage_factorsThruAlong (B : BigFppfSite.{u}) {X Y : B.Schemes}
    (f : Y ⟶ X) (R : Presieve X) (hR : R ∈ B.precoverage X) :
    ∃ T ∈ B.precoverage Y, T.FactorsThruAlong R f := by
  obtain ⟨E, rfl, hE⟩ := hR
  obtain ⟨P, π₁, π₂, hpb, hcov⟩ := B.isSite.2.2 ⟨X, E⟩ hE Y f
  refine ⟨(⟨E.I₀, P, π₂⟩ : PreZeroHypercover.{u + 1} Y).presieve₀,
    ⟨⟨E.I₀, P, π₂⟩, rfl, hcov⟩, ?_⟩
  rintro Z g ⟨i⟩
  exact ⟨E.X i, π₁ i, E.f i, ⟨i⟩, (hpb i).w⟩

/-- The topology of a big fppf site is subcanonical: every representable presheaf on
`Sch_κ` is a sheaf for the chosen fppf covering families.

The inclusion `Sch_κ ⥤ Sch` is fully faithful and preserves fibre products, and a chosen
covering family becomes an fppf covering family of schemes, so this is Mathlib's
subcanonicality of the fppf topology on all schemes transported along the inclusion. -/
instance subcanonical_topology (B : BigFppfSite.{u}) : B.topology.Subcanonical :=
  B.precoverage.subcanonical_toGrothendieck_of_fullyFaithful Scheme.fppfPrecoverage
    B.inclusion (fun _ _ hR => by
      obtain ⟨_, rfl, hE⟩ := hR
      exact hE.1)
    B.exists_mem_precoverage_factorsThruAlong

/-- A representable presheaf on the underlying category of a big fppf site is a sheaf.

This is `AlgebraicGeometry.BigFppfSite.subcanonical_topology` in the `Presheaf.IsSheaf`
form in which the sheaf condition is usually stated. -/
theorem isSheaf_yoneda_obj (B : BigFppfSite.{u}) (X : B.Schemes) :
    Presheaf.IsSheaf B.topology (yoneda.obj X) :=
  (isSheaf_iff_isSheaf_of_type _ _).2
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end BigFppfSite

section Over

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace BigFppfOver

/-- The topology of the big fppf site of a scheme `S` contained in a big fppf site is
subcanonical.

The topology is the localization of the site's topology at `S`, and a localization of a
subcanonical topology is subcanonical. -/
instance subcanonical_topology : (BigFppfOver.topology B S hS).Subcanonical :=
  inferInstanceAs (B.topology.over (B.obj hS)).Subcanonical

/-- A representable presheaf on the big fppf site of `S` is a sheaf. -/
theorem isSheaf_yoneda_obj (a : BigFppfOver B S hS) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj a) :=
  (isSheaf_iff_isSheaf_of_type _ _).2
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

variable {B S hS}

/-- A fibre product of a sheaf over a sheaf along a morphism from a representable presheaf,
formed in presheaves on the big fppf site of `S`, is a sheaf.

This is the shape in which the descent arguments for algebraic spaces use the sheaf
condition of a representable: Stacks 03I2 forms `X ×[Y] yoneda.obj a` for a sheaf `X`, a
sheaf `Y` and a representable chart of `Y`, and needs the result to be a sheaf before it can
be representable. -/
theorem isSheaf_pullback_yoneda_obj {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {a : BigFppfOver B S hS} (h : yoneda.obj a ⟶ Y)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback f h) :=
  Presheaf.isSheaf_pullback _ f h hX (isSheaf_yoneda_obj B S hS a) hY

end BigFppfOver

end Over

end AlgebraicGeometry
