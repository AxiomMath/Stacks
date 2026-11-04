module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointsVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralDirectImageAcyclic
public import StacksFrontier.Topology.Noetherian.GenericPointsDenseOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale cohomology of sheaves supported on finitely many closed points

Let `i : Z ⟶ X` be a closed immersion and `j : U ⟶ X` the inclusion of the open complement. If
`Z` is affine, all of its points are closed and all of its residue fields are separably closed —
for instance if `Z` is a finite scheme of finite type over a separably closed field — then every
abelian sheaf on the small étale site of `X` which vanishes on `U` has no étale cohomology in
positive degrees. This is the computation the proof of Stacks Tag 0GJA makes for the closed part
`i_* i^{-1} F` of a constructible sheaf `F` on a curve, whose support is the finite set of
closed points outside a dense open.

The argument is the source's. A sheaf `C` vanishing on `U` is the direct image of its inverse
image to `Z`: the left term of the sequence `0 → j_! j^{-1} C → C → i_* i^{-1} C → 0` of
Tag 095L is zero. A closed immersion is integral, so direct image along it does not change
étale cohomology (Tags 03QP and 03YU), and on `Z` positive-degree cohomology vanishes by Tag
09AY.

The same conclusion holds after any base change `f : Y ⟶ X`, for the inverse image of a direct
image from `Z`, as soon as the base change of `Z` has the same three properties. That is the
form used for restriction to an open subscheme and for extension of an algebraically closed
ground field, Tags 0A5A and 0A58.

## Main results

* `Stacks.EtaleCohomology.sheafHEtaleAbelianDirectImageAddEquiv` — for an integral morphism
  `i : Z ⟶ X` and an abelian sheaf `G` on `Z`, `H^q(Z, G) ≃ H^q(X, i_* G)`, at the coefficient
  universe `max (u + 1) v` and an arbitrary `Ext` universe.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_isZero_etaleRestriction` — a sheaf vanishing on
  the open complement of such a `Z` has no positive-degree cohomology.
* `Stacks.EtaleCohomology.subsingleton_sheafH_inverseImage_etaleAbelianDirectImage` — the same
  for `f^{-1} i_* G`, along any `f : Y ⟶ X` whose base change of `Z` has the three properties.
* `Stacks.EtaleCohomology.isAffine_and_isClosed_and_isSepClosed_of_finite` — a finite scheme
  locally of finite type over a separably closed field has the three properties.
* `TopologicalSpace.NoetherianSpace.isClosed_singleton_of_not_mem_of_dense` — in a sober
  Noetherian space of Krull dimension at most one, every point outside a dense open is closed.

## References

* [Stacks Project, Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 09AY](https://stacks.math.columbia.edu/tag/09AY)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Set Order

universe u v w

namespace TopologicalSpace

variable {T : Type*} [TopologicalSpace T]

/-- Two strict specializations in a row in a Kolmogorov space bound its Krull dimension below by
two: the three point closures form a strictly increasing chain of irreducible closed sets. -/
theorem two_le_topologicalKrullDim_of_specializes [T0Space T] {x y z : T} (hxy : x ⤳ y)
    (hyz : y ⤳ z) (h₁ : x ≠ y) (h₂ : y ≠ z) : (2 : WithBot ℕ∞) ≤ topologicalKrullDim T := by
  let c : T → IrreducibleCloseds T := fun a =>
    ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : ∀ {a b : T}, a ⤳ b → a ≠ b → c b < c a := by
    intro a b hab hne
    refine lt_of_le_of_ne (specializes_iff_closure_subset.mp hab) fun hEq ↦ hne ?_
    exact (t0Space_iff_inseparable T).mp ‹_› a b
      (inseparable_iff_closure_eq.mpr (congrArg IrreducibleCloseds.carrier hEq).symm)
  let l : LTSeries (IrreducibleCloseds T) :=
    { length := 2, toFun := ![c z, c y, c x],
      step := fun i => by
        fin_cases i
        · exact hlt hyz h₂
        · exact hlt hxy h₁ }
  have : ((2 : ℕ) : WithBot ℕ∞) ≤ krullDim (IrreducibleCloseds T) :=
    le_krullDim_iff.mpr ⟨l, rfl⟩
  exact_mod_cast this

/-- **In a sober Noetherian space of Krull dimension at most one, a point outside a dense open is
closed.** A generic point of an irreducible component lies in every dense open, so a point `x`
outside one is not generic: it is a strict specialization of the generic point of a component
containing it. If `x` were not closed it would in turn strictly specialize to some point of its
closure, and the resulting chain of length two contradicts the dimension bound. -/
theorem NoetherianSpace.isClosed_singleton_of_not_mem_of_dense [NoetherianSpace T]
    [QuasiSober T] [T0Space T] (hdim : topologicalKrullDim T ≤ 1) {D : Set T} (hD : IsOpen D)
    (hd : Dense D) {x : T} (hx : x ∉ D) : IsClosed ({x} : Set T) := by
  by_contra hcl
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ closure ({x} : Set T), y ≠ x := by
    by_contra h
    push Not at h
    exact hcl (closure_eq_iff_isClosed.mp
      (subset_antisymm (fun y hy => h y hy ▸ rfl) subset_closure))
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := x)).closure
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.prop (isClosed_of_mem_irreducibleComponents C hC)
  have hηgen : η ∈ genericPoints T := by
    show closure {η} ∈ irreducibleComponents T
    rw [hη.def]
    exact hC
  have hηx : η ⤳ x := by
    rw [specializes_iff_mem_closure, hη.def]
    exact hxC (subset_closure rfl)
  by_cases hEq : η = x
  · exact hx (hEq ▸ NoetherianSpace.mem_of_mem_genericPoints_of_dense hD hd hηgen)
  · exact absurd ((two_le_topologicalKrullDim_of_specializes hηx
      (specializes_iff_mem_closure.mpr hy) hEq hyx.symm).trans hdim) (by decide)

end TopologicalSpace

namespace Stacks.EtaleCohomology

section Geometry

/-- A finite scheme locally of finite type over a field is discrete: the morphism to the point is
locally quasi-finite, having finite fibres, and the fibre over the point is everything. -/
theorem discreteTopology_of_finite {K : Type u} [Field K] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of K)) [LocallyOfFiniteType f] [Finite Z] : DiscreteTopology Z := by
  have : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f fun _ => Set.toFinite _
  have h := f.isDiscrete_preimage_singleton (default : Spec (.of K))
  have hu : f ⁻¹' {default} = Set.univ := by
    ext z
    simp [Subsingleton.elim (f z) default]
  rw [hu] at h
  exact isDiscrete_univ_iff.mp h

/-- **A finite scheme locally of finite type over a separably closed field satisfies the
hypotheses of Tag 09AY**: it is affine, all of its points are closed and all of its residue
fields are separably closed. It is discrete, so affine as a finite discrete scheme, and the
residue field at a closed point of a scheme locally of finite type over a separably closed
field is separably closed. -/
theorem isAffine_and_isClosed_and_isSepClosed_of_finite {K : Type u} [Field K] [IsSepClosed K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K)) [LocallyOfFiniteType f] [Finite Z] :
    IsAffine Z ∧ (∀ z : Z, IsClosed ({z} : Set Z)) ∧
      ∀ z : Z, IsSepClosed ↥(Z.residueField z) := by
  have := discreteTopology_of_finite f
  have hcl : ∀ z : Z, IsClosed ({z} : Set Z) := fun z => isClosed_discrete _
  exact ⟨inferInstance, hcl, fun z => isSepClosed_residueField_of_isClosed f z (hcl z)⟩

/-- The base change of the complement of a closed immersion is the complement of its base
change: for `f : Y ⟶ X`, the open immersion `Y ×_X U ⟶ Y` has image the complement of the image
of `Y ×_X Z ⟶ Y` when `U ⟶ X` has image the complement of the image of `Z ⟶ X`. -/
theorem range_pullback_snd_eq_compl {Z U X Y : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    (hij : Set.range j.base = (Set.range i.base)ᶜ) (f : Y ⟶ X) :
    Set.range (pullback.snd j f).base = (Set.range (pullback.snd i f).base)ᶜ := by
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, hij, Set.preimage_compl]

end Geometry

section Cohomology

/-- **Direct image along an integral morphism does not change étale cohomology**, at the
coefficient universe `max (u + 1) v` and an arbitrary `Ext` universe: for `i : Z ⟶ X` integral
— a closed immersion, for instance — and an abelian sheaf `G` on the small étale site of `Z`,
`H^q(Z, G) ≃ H^q(X, i_* G)`. Direct image along `i` is exact (Tag 04C2) and preserves injective
objects, being right adjoint to the exact inverse image, so Tag 03YU applies. -/
def sheafHEtaleAbelianDirectImageAddEquiv {Z X : Scheme.{u}} (i : Z ⟶ X) [IsIntegralHom i]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Sheaf.H.{w} G q ≃+ Sheaf.H.{w} ((etaleAbelianDirectImage.{u, v} i).obj G) q :=
  have : ((smallEtaleBaseChange i).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (smallEtaleTopology X) (smallEtaleTopology Z)).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (etaleAbelianInverseImageDirectImageAdj.{u, v} i)
  Stacks.Cohomology.BiggerSite.sheafHAddEquiv (smallEtaleTopology X) (smallEtaleTopology Z)
    (smallEtaleBaseChange i) terminalIsTerminal
    (isTerminalSmallEtaleBaseChangeObj i terminalIsTerminal) rfl G q

/-- The vanishing of `subsingleton_sheafH_of_isZero_etaleRestriction` at the `Ext` universe
`max (u + 1) v`, where the abelian sheaves on both small étale sites form Grothendieck abelian
categories and so have `Ext` groups. -/
private theorem subsingleton_sheafH_of_isZero_etaleRestriction_aux {Z U X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) [IsAffine Z]
    (hclosed : ∀ z : Z, IsClosed ({z} : Set Z))
    (hsep : ∀ z : Z, IsSepClosed ↥(Z.residueField z))
    (C : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hC : IsZero ((etaleRestriction.{u, v} j).obj C)) (q : ℕ) (hq : 0 < q) :
    letI := IsGrothendieckAbelian.hasExt.{max (u + 1) v}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    Subsingleton (Sheaf.H.{max (u + 1) v} C q) := by
  have := IsGrothendieckAbelian.hasExt.{max (u + 1) v}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  have := IsGrothendieckAbelian.hasExt.{max (u + 1) v}
    (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, v} i j hij C
  have hg : IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit.app C) :=
    hS.isIso_g_iff.mpr ((extensionByZero.{u, v} j).map_isZero hC)
  have h₀ : Subsingleton (Sheaf.H.{max (u + 1) v}
      ((etaleAbelianInverseImage.{u, v} i).obj C) q) :=
    subsingleton_etaleCohomology_of_closed_points.{u, max (u + 1) v, max (u + 1) v}
      Z hclosed hsep _ q hq
  have h₁ : Subsingleton (Sheaf.H.{max (u + 1) v} ((etaleAbelianDirectImage.{u, v} i).obj
      ((etaleAbelianInverseImage.{u, v} i).obj C)) q) :=
    (sheafHEtaleAbelianDirectImageAddEquiv.{u, v, max (u + 1) v} i _ q).symm.injective.subsingleton
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : Sheaf.H.{max (u + 1) v} C q, x = Sheaf.H.map
      (inv ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit.app C)) q
      (Sheaf.H.map ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit.app C) q x) := by
    intro x
    rw [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply]
  rw [key a, key b]
  exact congrArg _ (h₁.elim _ _)

/-- **A sheaf vanishing off a finite set of closed points has no higher étale cohomology.** Let
`i : Z ⟶ X` be a closed immersion with `Z` affine, all of whose points are closed and all of whose
residue fields are separably closed, and let `j : U ⟶ X` be the inclusion of the open
complement. An abelian sheaf `C` on the small étale site of `X` whose restriction to `U` vanishes
has vanishing étale cohomology in every positive degree, for every choice of `Ext` universe.

The left term of the sequence `0 → j_! j^{-1} C → C → i_* i^{-1} C → 0` of Tag 095L vanishes, so
`C ≅ i_* i^{-1} C`; direct image along the integral `i` does not change cohomology; and the
positive-degree cohomology of `Z` vanishes by Tag 09AY. The computation is made at the `Ext`
universe `max (u + 1) v` and transported to `w` by `CategoryTheory.Abelian.Ext.chgUniv`. -/
@[sga "4 VIII 2.4" "more general"]
theorem subsingleton_sheafH_of_isZero_etaleRestriction {Z U X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) [IsAffine Z]
    (hclosed : ∀ z : Z, IsClosed ({z} : Set Z))
    (hsep : ∀ z : Z, IsSepClosed ↥(Z.residueField z))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (C : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hC : IsZero ((etaleRestriction.{u, v} j).obj C)) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} C q) := by
  have := IsGrothendieckAbelian.hasExt.{max (u + 1) v}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  have := subsingleton_sheafH_of_isZero_etaleRestriction_aux.{u, v} i j hij hclosed hsep C hC q hq
  exact (Abelian.Ext.chgUniv.{max (u + 1) v, w}).injective.subsingleton

/-- The inverse image of a direct image from a closed subscheme vanishes on the base change of
the open complement: for `f : Y ⟶ X`, the restriction of `f^{-1} i_* G` to `Y ×_X U` is the
inverse image of the restriction of `i_* G` to `U`, which is zero. -/
theorem isZero_etaleRestriction_inverseImage_etaleAbelianDirectImage {Z U X Y : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j] (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (f : Y ⟶ X) (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsZero ((etaleRestriction.{u, v} (pullback.snd j f)).obj
      ((etaleAbelianInverseImage.{u, v} f).obj ((etaleAbelianDirectImage.{u, v} i).obj G))) := by
  refine IsZero.of_iso ?_
    ((etaleAbelianInverseImageRestrictionIso.{u, v} (pullback.snd j f)).app _).symm
  refine IsZero.of_iso ?_ ((etaleAbelianInverseImageCompIso'.{u, v} (pullback.snd j f) f
    (pullback.snd j f ≫ f) rfl).app _).symm
  refine IsZero.of_iso ?_ (((etaleAbelianInverseImageCompIso'.{u, v} (pullback.fst j f) j
    (pullback.snd j f ≫ f) pullback.condition.symm).app _).trans
      ((etaleAbelianInverseImage.{u, v} (pullback.fst j f)).mapIso
        ((etaleAbelianInverseImageRestrictionIso.{u, v} j).app _)))
  exact Functor.map_isZero _ (isZero_etaleRestriction_etaleAbelianDirectImage i j hij G)

/-- **The inverse image of a direct image from finitely many closed points has no higher étale
cohomology.** Let `i : Z ⟶ X` be a closed immersion and `f : Y ⟶ X` a morphism whose base change
`Y ×_X Z` is affine with all points closed and all residue fields separably closed. Then for every
abelian sheaf `G` on `Z` the étale cohomology of `f^{-1} i_* G` vanishes in positive degrees: the
sheaf vanishes on `Y ×_X U` for `U` the open complement of `Z`, and
`subsingleton_sheafH_of_isZero_etaleRestriction` applies to the base change of `i`. -/
@[sga "4 VIII 2.4" "more general"]
theorem subsingleton_sheafH_inverseImage_etaleAbelianDirectImage {Z U X Y : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) (f : Y ⟶ X) [IsAffine (pullback i f)]
    (hclosed : ∀ z : ↥(pullback i f), IsClosed ({z} : Set ↥(pullback i f)))
    (hsep : ∀ z : ↥(pullback i f), IsSepClosed ↥((pullback i f).residueField z))
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w}
      ((etaleAbelianInverseImage.{u, v} f).obj ((etaleAbelianDirectImage.{u, v} i).obj G)) q) :=
  subsingleton_sheafH_of_isZero_etaleRestriction.{u, v, w} (pullback.snd i f) (pullback.snd j f)
    (range_pullback_snd_eq_compl i j hij f) hclosed hsep _
    (isZero_etaleRestriction_inverseImage_etaleAbelianDirectImage.{u, v} i j hij f G) q hq

end Cohomology

end Stacks.EtaleCohomology

end
