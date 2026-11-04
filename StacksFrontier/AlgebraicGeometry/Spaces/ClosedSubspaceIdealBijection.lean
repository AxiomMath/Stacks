module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart

/-!
# The defining ideal sheaf of a closed subspace, and the injectivity of Stacks 03MB

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Stacks 03MB
asserts that `Z ↦ 𝓘_Z` is an inclusion-reversing *bijection* between the closed subspaces of `X`
and the quasi-coherent ideal sheaves of `𝒪_X`.  This file supplies the ideal sheaf as an object
and the injective, order-reversing half of the correspondence.

Two things are done.

First, `AlgebraicGeometry.Space.definingIdealSheaf` assembles
`AlgebraicGeometry.Space.definingIdealAt` — the ideal of a closed subspace on one étale scheme
chart, which is a kernel of a map of rings of global sections — into a single *sheaf submodule*
of `𝒪_X` on the small étale ringed site of `X`.  The two conditions a sheaf submodule has to
satisfy are both consequences of `definingIdealAt` being the kernel of the structure map
`i♯ : 𝒪_X ⟶ i_*𝒪_Z` of Stacks 03G8: stability under restriction is naturality of `i♯`, and
locality of membership is separatedness of its target, a sheaf of rings, on a covering sieve.
Before this the library had no ideal sheaf on an algebraic space at all, only the chartwise
ideals; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ZeroScheme.lean`.

Second, the map `Z ↦ 𝓘_Z` is injective and order-reversing, which is
`AlgebraicGeometry.Space.definingIdealOrderEmbedding`.  Order-reversal is
`AlgebraicGeometry.Space.definingIdealAt_antitone`.  Injectivity is the substance: it is proved
by *recovering* `Z` from its ideal, through the chart-local membership criterion
`AlgebraicGeometry.Space.mem_obj_iff_definingIdealAt_le`, which needs the chart to be affine.
The affine charts are supplied by Stacks 03FX in the form
`AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`: a surjective étale chart
whose underlying scheme is a coproduct of affines, each summand being itself an affine étale
chart of `X`.  A point of `X` over a test object is pushed to that chart by
`AlgebraicGeometry.Space.mem_obj_of_surjective_etale`, and then the test object is covered by
the preimages of the summands — a Zariski covering, hence an fppf covering sieve by
`AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion` — on each of which the
point factors through one affine summand.

`AlgebraicGeometry.Space.le_of_forall_ker_le` is the same injectivity statement with the
chartwise *ideal sheaves of schemes* in place of their ideals of global sections.  It holds at an
arbitrary chart and needs no affine refinement, because `mem_obj_iff_ker_le` is stated for the
ideal sheaf.

Third, the *surjectivity* half is reduced to one chart and to schemes alone, by
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isInvariantSubscheme`.  Given a
surjective étale chart `φ : U ⟶ X` and a sheaf of ideals `J ⊆ 𝒪_U` on the *scheme* `U` which is
invariant under the relation `R = U ×_X U`, the closed subscheme `V(J) ⊆ U` descends to a closed
subspace of `X`: that is Stacks 03I2 for closed immersions, available here because effective
descent of closed immersions along surjective étale morphisms is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`.  Its defining
ideal is then computed at every étale chart `A` of `X` lying over `U`: the base change of the
subspace along `A` is the pullback subscheme `V(m^{-1}J)`, because the two have the same functor
of points — `AlgebraicGeometry.Space.preimage_invariantSubspace` and
`AlgebraicGeometry.Space.subschemePoints_pullback` — and an immersed subscheme is determined by
its functor of points.  So the defining ideal sheaf of the descended subspace is prescribed
chartwise by `J`, and a sheaf of ideals of `𝒪_X` is pinned down by its sections over the affine
charts lying over one surjective chart,
`AlgebraicGeometry.Space.structureSubmodule_ext_of_forall_isAffine_hom`.

## Main definitions

* `AlgebraicGeometry.Space.definingIdealSheaf` is the defining ideal of a closed subspace as a
  sheaf submodule of `𝒪_X` on the small étale ringed site of `X`.
* `AlgebraicGeometry.Space.definingIdealOrderEmbedding` is the inclusion-reversing order
  embedding of the closed subspaces of `X` into those sheaf submodules.

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_map` and
  `AlgebraicGeometry.Space.mem_definingIdealAt_of_sieve` are the two conditions making the
  chartwise defining ideals a sheaf submodule: stability under étale restriction, and locality
  of membership.
* `AlgebraicGeometry.Space.definingIdealSheaf_obj`: its sections over a chart are
  `AlgebraicGeometry.Space.definingIdealAt`, so it is the defining ideal and not some other
  ideal sheaf with the same formal properties.
* `AlgebraicGeometry.Space.le_of_forall_definingIdealAt_le` and
  `AlgebraicGeometry.Space.le_of_definingIdealSheaf_le`: **a closed subspace is recovered from
  its defining ideal.** Testing the inclusion of ideals on the affine charts alone suffices.
* `AlgebraicGeometry.Space.definingIdealSheaf_injective`: consequently `Z ↦ 𝓘_Z` is injective.
* `AlgebraicGeometry.Space.le_of_forall_ker_le` and
  `AlgebraicGeometry.Space.eq_of_forall_ker_eq`: the same, with the chartwise ideal sheaves of
  schemes as the data, at arbitrary charts.
* `AlgebraicGeometry.Space.structureSubmodule_ext_of_forall_isAffine` and
  `AlgebraicGeometry.Space.structureSubmodule_ext_of_forall_isAffine_hom`: **a sheaf of ideals of
  `𝒪_X` is determined by its sections over the affine étale charts**, and even over the affine
  charts lying above one chart whose structure morphism is surjective.  Consequently
  `AlgebraicGeometry.Space.definingIdealSheaf_eq_of_forall_isAffine`: agreement with `𝓘_Z` on the
  affine charts is agreement.
* `AlgebraicGeometry.Space.isClosedSubspace_invariantSubspace_subschemeι`: **an invariant sheaf
  of ideals on a surjective étale chart cuts out a closed subspace of `X`.**
* `AlgebraicGeometry.Space.definingIdealAt_invariantSubspace_subschemeι`: the defining ideal of
  that closed subspace, at any chart lying over the given one, is the ideal of global functions
  cut out by the pullback of the ideal sheaf.
* `AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isInvariantSubscheme`: **the
  surjectivity half of Stacks 03MB, reduced to one chart and to schemes alone.**

## What is not proved here, and where it is proved

The bijection of Stacks 03MB is not obtained in this file, which stops at the reduction of its
surjectivity half to one chart.  It *is* obtained in this tree, in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceFromQuasicoherentIdeal.lean`: the bijection
is `AlgebraicGeometry.Space.toDual_definingIdealSheaf_bijective'` (line 340) and the order
isomorphism together with its kernel formula is
`AlgebraicGeometry.Space.closedSubspaceQuasicoherentIdealOrderIso` (line 358).  Both of the two
statements this file leaves open are proved there or upstream of it.

* **Quasi-coherence of the ideal sheaf.** `definingIdealSheaf` lands in the sheaf submodules of
  `𝒪_X`, not in the quasi-coherent ones, so it is not by itself a map into the right-hand side of
  Stacks 03MB.  What is unconditional here is that `𝓘_Z` satisfies the base change criterion,
  `AlgebraicGeometry.Space.definingIdealSheaf_isCartesianOnAffineCharts`, and the passage from
  that criterion to quasi-coherence is the unconditional
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`
  (`StacksFrontier/AlgebraicGeometry/Spaces/CartesianRelations.lean:1170`); the two compose to
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceIdealQuasicoherent.lean:357`).  The
  converse identification, Descent 03DX(2) in the direction quasi-coherent ⟹ cartesian on affine
  charts, is also available:
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`
  (`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentCartesianOnAffineCharts.lean:640`, carrying
  `@[stacks 03DX]`), proved by the descent argument of Stacks 0H04.  Nothing here is blocked on
  Stacks 03DW, which is not an input to 03DX at all.
* **Surjectivity is reduced here, and proved elsewhere.** What
  `AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isInvariantSubscheme` still asks for
  is the ideal sheaf `J ⊆ 𝒪_U` on the chart, together with its invariance and the chartwise
  match with `𝓘`.  That construction is
  `AlgebraicGeometry.Space.exists_idealSheafData_of_isCartesianOnAffineCharts`
  (`StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafDataFromCartesian.lean:533`), and with it the
  surjectivity half needs nothing but 03MB's own hypothesis:
  `AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceFromQuasicoherentIdeal.lean:329`) takes
  only `hN : N.toSheafOfModules.IsQuasicoherentOnSite`.  The construction takes `J` to be given
  on an affine open `V ⊆ U` by the sections `𝓘(V)`, the open `V` being itself an affine étale
  chart of `X` — this is `AlgebraicGeometry.Space.openChart` — and the compatibility
  `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_basicOpen` demanded of an ideal sheaf, as
  well as the invariance, are instances of the base change criterion
  `AlgebraicGeometry.Space.IsCartesianOnAffineCharts`: for a morphism of affine étale charts the
  sections of `𝓘` over the smaller are generated by those over the larger.  Carrying it out
  needed the sections of the structure sheaf over `AlgebraicGeometry.Space.openChart` to be
  transported to the sections over the open, which is the isomorphism
  `AlgebraicGeometry.Scheme.Opens.topIso` and is not an equality.

  Stacks' own route is different and is *not* what the reduction above follows.  Stacks forms the
  vanishing subfunctor `Z(T) = {h : T ⟶ X ∣ h^*𝓘 ⟶ 𝒪_T` is zero`}` and cuts out its base change
  along `φ : U ⟶ X` by the image of `φ^*𝓘 ⟶ 𝒪_U`; that needs a formula for the sections of
  `AlgebraicGeometry.Space.modulePullback`, an abstract left adjoint which has none.  Going
  through the invariant ideal sheaf on the chart avoids the module pullback altogether.

  The invariance needs no formula for the sections of
  `AlgebraicGeometry.Scheme.IdealSheafData.comap` along the two legs, which are étale rather than
  open immersions, and the construction of the ideal sheaf uses no étale descent at all; this is
  `AlgebraicGeometry.Space.exists_idealSheafData_of_isCartesianOnAffineCharts`.  What suffices is
  the comap formula on an affine open lying over an affine open, which holds for *every* morphism
  of schemes and is `Stacks.IdealSheaf.ideal_comap_appLE`.  The invariance then
  falls out because both legs are morphisms of étale charts with the same composite to the space,
  so a single sheaf of ideals on the relation is identified with both inverse images.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Kernels of global functions and subobjects of schemes -/

/-- Pulling a global regular function back further can only enlarge the ideal it is killed by:
if a function on `Z` is killed by pullback along `q : Y ⟶ Z`, it is killed by pullback along
any `r ≫ q`. -/
theorem ker_appTop_le_comp {X Y Z : Scheme.{u}} (r : X ⟶ Y) (q : Y ⟶ Z) :
    RingHom.ker q.appTop.hom ≤ RingHom.ker (r ≫ q).appTop.hom := by
  intro a ha
  refine RingHom.mem_ker.mpr ?_
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    RingHom.mem_ker.mp ha, map_zero]

/-- **Two monomorphisms of schemes defining the same subobject kill the same global functions.**
Each factors through the other, so `AlgebraicGeometry.ker_appTop_le_comp` applies both ways. -/
theorem ker_appTop_eq_of_subobject_mk_eq {X Y Z : Scheme.{u}} (p : X ⟶ Z) (q : Y ⟶ Z)
    [Mono p] [Mono q] (h : Subobject.mk p = Subobject.mk q) :
    RingHom.ker p.appTop.hom = RingHom.ker q.appTop.hom := by
  refine le_antisymm ?_ ?_
  · rw [← Subobject.ofMkLEMk_comp (f := q) (g := p) h.ge]
    exact ker_appTop_le_comp _ _
  · rw [← Subobject.ofMkLEMk_comp (f := p) (g := q) h.le]
    exact ker_appTop_le_comp _ _

namespace Scheme.IdealSheafData

/-- **The closed subscheme cut out by an ideal sheaf pulls back to the one cut out by the
pulled-back ideal sheaf**, as subobjects.  This is
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso` read in the subobject lattice; the same
computation appears inside the proof of
`AlgebraicGeometry.Scheme.IdealSheafData.pullback_subobject_eq_of_support_comap_eq`, where it is
not available separately. -/
theorem pullback_subobject_mk_subschemeι {U R : Scheme.{u}} (I : U.IdealSheafData)
    (g : R ⟶ U) :
    (Subobject.pullback g).obj (Subobject.mk I.subschemeι) =
      Subobject.mk (I.comap g).subschemeι := by
  have hh : (I.comapIso g).hom ≫ (Limits.pullbackSymmetry g I.subschemeι).hom ≫
      Limits.pullback.snd I.subschemeι g = (I.comap g).subschemeι := by
    calc (I.comapIso g).hom ≫ (Limits.pullbackSymmetry g I.subschemeι).hom ≫
          Limits.pullback.snd I.subschemeι g
        _ = (I.comapIso g).hom ≫ Limits.pullback.fst g I.subschemeι := by
          simp only [Limits.pullbackSymmetry_hom_comp_snd]
        _ = _ := comapIso_hom_fst I g
  rw [Subobject.pullback_obj_mk (IsPullback.of_hasPullback I.subschemeι g)]
  refine Subobject.mk_eq_mk_of_comm _ _
    (I.comapIso g ≪≫ Limits.pullbackSymmetry g I.subschemeι).symm ?_
  rw [← hh]
  simp

end Scheme.IdealSheafData

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chartwise defining ideals form a sheaf submodule of the structure sheaf -/

/-- A regular function on an étale chart of `X` lies in the defining ideal of a closed subspace
`Z` exactly when the structure map of the inclusion of `Z` kills it.  This is the definition of
`AlgebraicGeometry.Space.definingIdealAt` unfolded. -/
theorem mem_definingIdealAt_iff (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS X).obj.obj U)) :
    a ∈ definingIdealAt B S hS X Z U ↔
      ((structureSharp B S hS (ObjectProperty.homMk Z.1.ι :
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).hom.app U).hom a = 0 :=
  RingHom.mem_ker

/-- The structure map of Stacks 03G8 commutes with étale restriction, read on sections. -/
theorem structureSharp_app_apply_map (X Y : AlgebraicSpaces B S hS) (f : X ⟶ Y)
    {U V : (SmallEtale B S hS Y.1)ᵒᵖ} (g : U ⟶ V)
    (a : ToType ((structureRingSheaf B S hS Y).obj.obj U)) :
    ((structureSharp B S hS f).hom.app V).hom
        (((structureRingSheaf B S hS Y).obj.map g).hom a) =
      ((structureRingSheafDirectImage B S hS f).obj.map g).hom
        (((structureSharp B S hS f).hom.app U).hom a) :=
  ConcreteCategory.congr_hom ((structureSharp B S hS f).hom.naturality g) a

/-- **The defining ideals are stable under étale restriction.** The restriction of a regular
function in the defining ideal of a closed subspace at one étale chart lies in its defining
ideal at any smaller chart. -/
theorem definingIdealAt_map (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) {U V : (SmallEtale B S hS X.1)ᵒᵖ} (f : U ⟶ V)
    (a : ToType ((structureRingSheaf B S hS X).obj.obj U))
    (ha : a ∈ definingIdealAt B S hS X Z U) :
    ((structureRingSheaf B S hS X).obj.map f).hom a ∈ definingIdealAt B S hS X Z V := by
  rw [mem_definingIdealAt_iff] at ha ⊢
  rw [structureSharp_app_apply_map, ha, map_zero]

/-- **Membership in the defining ideal of a closed subspace is local on the small étale site.**
A regular function on an étale chart whose restriction along every arrow of a covering sieve
lies in the defining ideal already lies in it: the direct image of the structure sheaf of the
subspace is a sheaf, hence separated. -/
theorem mem_definingIdealAt_of_sieve (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (s : ToType ((structureRingSheaf B S hS X).obj.obj U))
    (T : Sieve U.unop) (hT : T ∈ SmallEtale.topology B S hS X.1 U.unop)
    (h : ∀ (V : SmallEtale B S hS X.1) (m : V ⟶ U.unop), T m →
      ((structureRingSheaf B S hS X).obj.map m.op).hom s ∈
        definingIdealAt B S hS X Z (op V)) :
    s ∈ definingIdealAt B S hS X Z U := by
  refine (mem_definingIdealAt_iff B S hS X Z U s).2 ?_
  refine (structureRingSheafDirectImage B S hS (ObjectProperty.homMk Z.1.ι :
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).isSeparated
    U.unop T hT _ 0 ?_
  intro V m hm
  have key := (mem_definingIdealAt_iff B S hS X Z (op V) _).1 (h V m hm)
  rw [structureSharp_app_apply_map B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) X
    (ObjectProperty.homMk Z.1.ι) m.op s] at key
  exact key.trans (map_zero _).symm

/-- **The defining ideal sheaf of a closed subspace.** The ideals
`AlgebraicGeometry.Space.definingIdealAt` of a closed subspace `Z ⊆ X`, taken at every étale
scheme chart of `X`, are the sections of a sheaf submodule of the structure sheaf `𝒪_X` on the
small étale ringed site of `X`.  This is the ideal sheaf `𝓘_Z ⊆ 𝒪_X` of Stacks 03MB.

Quasi-coherence of `𝓘_Z` is *not* asserted; see the section "What is not proved" of the module
documentation. -/
noncomputable def definingIdealSheaf (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule where
  obj U := definingIdealAt B S hS X Z U
  map f a ha := definingIdealAt_map B S hS X Z f a ha
  isSheaf {U} s hs :=
    mem_definingIdealAt_of_sieve B S hS X Z U s _ hs fun _ _ hm => hm

/-- The sections of the defining ideal sheaf over an étale chart are the defining ideal at that
chart. -/
theorem definingIdealSheaf_obj (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    (definingIdealSheaf B S hS X Z).obj U = definingIdealAt B S hS X Z U :=
  rfl

/-- **Stacks 03MB, the inclusion-reversal, at the level of ideal sheaves.** A smaller closed
subspace has a larger defining ideal sheaf. -/
theorem definingIdealSheaf_antitone (X : AlgebraicSpaces B S hS)
    (Z W : ClosedSubspaces B S hS X.1) (hZW : Z.1 ≤ W.1) :
    definingIdealSheaf B S hS X W ≤ definingIdealSheaf B S hS X Z :=
  fun U => definingIdealAt_antitone B S hS X Z W hZW U.unop

/-! ### A closed subspace is determined by its defining ideal -/

/-- A point `x` of `X`, restricted to the base change of the étale chart `f` along `x`, is the
image under `f` of the first projection of the base change. -/
private theorem map_snd_eq_app_fst' (X : AlgebraicSpaces B S hS) {UX : BigFppfOver B S hS}
    {f : yoneda.obj UX ⟶ X.1}
    (hfE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    {T : (BigFppfOver B S hS)ᵒᵖ} (x : X.1.obj T) (τ : yoneda.obj T.unop ⟶ X.1)
    (hτ : τ = yonedaEquiv.symm x) :
    X.1.map (hfE.rep.snd τ).op x = f.app (op (hfE.rep.pullback τ)) (hfE.rep.fst' τ) := by
  have hw : yoneda.map (hfE.rep.fst' τ) ≫ f = yoneda.map (hfE.rep.snd τ) ≫ τ := by
    rw [hfE.rep.map_fst' τ]
    exact hfE.rep.w τ
  rw [← yonedaEquiv_yoneda_map_comp B S hS f (hfE.rep.fst' τ), hw, ← yonedaEquiv_naturality, hτ,
    Equiv.apply_symm_apply]

/-- **A closed subspace is recovered from the chartwise ideal sheaves of its base changes.** If
the ideal sheaf of the closed immersion of schemes `W ×_X U ⟶ U` is contained in that of
`Z ×_X U ⟶ U` at every étale scheme chart `U` of `X`, then `Z ⊆ W`.

The chart need not be affine: the membership criterion
`AlgebraicGeometry.Space.mem_obj_iff_ker_le` is stated for the ideal sheaf, and applies directly
at the chart which the algebraic-space hypothesis supplies. -/
theorem le_of_forall_ker_le (X : AlgebraicSpaces B S hS)
    (Z W : ClosedSubspaces B S hS X.1)
    (h : ∀ U : SmallEtale B S hS X.1,
      ((BigFppfOver.toScheme B S hS).map (W.2.2.rep.snd U.1.hom)).ker ≤
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)).ker) :
    Z.1 ≤ W.1 := by
  intro T x hx
  obtain ⟨UX, f, hfS, hfE⟩ := X.2.exists_atlas
  set U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk f, hfE⟩
  set τ : yoneda.obj T.unop ⟶ X.1 := yonedaEquiv.symm x with hτ
  refine mem_obj_of_surjective_etale B S hS X.2.isSheaf W.1 W.2.1.isSheaf
    (hfE.rep.snd τ) (hfS.property_snd τ) (hfE.property_snd τ) _ ?_
  have hval : X.1.map (hfE.rep.snd τ).op x =
      U.1.hom.app (op (hfE.rep.pullback τ)) (hfE.rep.fst' τ) :=
    map_snd_eq_app_fst' B S hS X hfE x τ hτ
  rw [hval, mem_obj_iff_ker_le]
  refine (h U).trans ?_
  rw [← mem_obj_iff_ker_le, ← hval]
  exact Z.1.map (hfE.rep.snd τ).op hx

/-- **A closed subspace is determined by the chartwise ideal sheaves of its base changes.** -/
theorem eq_of_forall_ker_eq (X : AlgebraicSpaces B S hS)
    (Z W : ClosedSubspaces B S hS X.1)
    (h : ∀ U : SmallEtale B S hS X.1,
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (W.2.2.rep.snd U.1.hom)).ker) :
    Z = W :=
  Subtype.ext (le_antisymm
    (le_of_forall_ker_le B S hS X Z W fun U => (h U).ge)
    (le_of_forall_ker_le B S hS X W Z fun U => (h U).le))

/-- **Stacks 03MB, injectivity: a closed subspace is recovered from its defining ideal.** If the
defining ideal of `W` is contained in that of `Z` at every *affine* étale scheme chart of `X`,
then `Z ⊆ W`.

Affine charts suffice because the affine étale charts of `X` cover it: Stacks 03FX supplies a
surjective étale chart whose underlying scheme is a coproduct of affines, each summand being an
affine étale chart.  A point of `X` is pushed onto that chart, and the test object carrying it is
then covered by the preimages of the summands, on each of which the point factors through a
single affine chart.  Over an affine chart the defining ideal determines membership, by
`AlgebraicGeometry.Space.mem_obj_iff_definingIdealAt_le`. -/
theorem le_of_forall_definingIdealAt_le (X : AlgebraicSpaces B S hS)
    (Z W : ClosedSubspaces B S hS X.1)
    (h : ∀ U : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
      definingIdealAt B S hS X W (op U) ≤ definingIdealAt B S hS X Z (op U)) :
    Z.1 ≤ W.1 := by
  intro T x hx
  obtain ⟨UX, f, I, Ya, j, e, hfS, hfE, haff, hcompat, -, hietale, -⟩ :=
    X.2.exists_affine_coproduct_atlas
  obtain ⟨hjoi, hjcov, -⟩ := isOpenImmersion_cover_disjoint_of_iso_sigma e hcompat
  set τ : yoneda.obj T.unop ⟶ X.1 := yonedaEquiv.symm x with hτ
  refine mem_obj_of_surjective_etale B S hS X.2.isSheaf W.1 W.2.1.isSheaf
    (hfE.rep.snd τ) (hfS.property_snd τ) (hfE.property_snd τ) _ ?_
  have hval := map_snd_eq_app_fst' B S hS X hfE x τ hτ
  -- the preimages of the affine summands cover the base-changed test object
  choose c ic hicoi hicrange _hicuniv using fun i : I =>
    exists_restrict_bigFppfOver (hfE.rep.pullback τ)
      (((BigFppfOver.toScheme B S hS).map (hfE.rep.fst' τ)) ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map (j i)).opensRange)
  have hsieve : Sieve.ofArrows c ic ∈ BigFppfOver.topology B S hS (hfE.rep.pullback τ) := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS ic hicoi fun y => ?_
    obtain ⟨i, hi⟩ := hjcov (((BigFppfOver.toScheme B S hS).map (hfE.rep.fst' τ)).base y)
    exact ⟨i, by rw [hicrange i]; exact hi⟩
  refine mem_obj_of_sieve_le B S hS X.2.isSheaf W.1 W.2.1.isSheaf _ _ hsieve ?_
  rintro V m ⟨b, a, p, ⟨i⟩, rfl⟩
  -- the affine étale chart cut out by the `i`-th summand
  set U : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map (j i) ≫ f), hietale i⟩
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := haff i
  -- over `V` the point factors through that chart
  have hsub : Set.range ((BigFppfOver.toScheme B S hS).map
      ((a ≫ ic i) ≫ hfE.rep.fst' τ)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (j i)) := by
    rintro _ ⟨z, rfl⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    have hz : ((BigFppfOver.toScheme B S hS).map (a ≫ ic i)).base z ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (ic i)) := by
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rw [hicrange i] at hz
    exact hz
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V ⟶ Ya i, ψ ≫ j i = (a ≫ ic i) ≫ hfE.rep.fst' τ := by
    have := hjoi i
    set χ := _root_.AlgebraicGeometry.IsOpenImmersion.lift
      ((BigFppfOver.toScheme B S hS).map (j i))
      ((BigFppfOver.toScheme B S hS).map ((a ≫ ic i) ≫ hfE.rep.fst' τ)) hsub
    have hχ : χ ≫ (BigFppfOver.toScheme B S hS).map (j i) =
        (BigFppfOver.toScheme B S hS).map ((a ≫ ic i) ≫ hfE.rep.fst' τ) :=
      _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
    obtain ⟨φ, hφ⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS χ (by
      rw [← BigFppfOver.toScheme_map_comp_hom (j i), ← Category.assoc, hχ,
        BigFppfOver.toScheme_map_comp_hom])
    exact ⟨φ, (BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, hφ, hχ])⟩
  have hpoint : X.1.map (a ≫ ic i).op (X.1.map (hfE.rep.snd τ).op x) =
      U.1.hom.app (op V) ψ := by
    rw [hval, ← NatTrans.naturality_apply]
    show f.app (op V) ((a ≫ ic i) ≫ hfE.rep.fst' τ) = _
    rw [← hψ]
    exact (NatTrans.comp_app_apply (yoneda.map (j i)) f (op V) ψ).symm
  rw [hpoint, mem_obj_iff_definingIdealAt_le (hS := hS)]
  refine (h U hUaff).trans ?_
  rw [← mem_obj_iff_definingIdealAt_le (hS := hS), ← hpoint]
  exact Z.1.map (a ≫ ic i).op (Z.1.map (hfE.rep.snd τ).op hx)

/-- **Stacks 03MB, injectivity.** An inclusion of defining ideal sheaves comes from the reverse
inclusion of closed subspaces. -/
theorem le_of_definingIdealSheaf_le (X : AlgebraicSpaces B S hS)
    (Z W : ClosedSubspaces B S hS X.1)
    (h : definingIdealSheaf B S hS X W ≤ definingIdealSheaf B S hS X Z) :
    Z.1 ≤ W.1 :=
  le_of_forall_definingIdealAt_le B S hS X Z W fun U _ => h (op U)

/-- **Stacks 03MB, injectivity.** Distinct closed subspaces have distinct defining ideal
sheaves. -/
theorem definingIdealSheaf_injective (X : AlgebraicSpaces B S hS) :
    Function.Injective (definingIdealSheaf B S hS X) := fun Z W hZW =>
  Subtype.ext (le_antisymm
    (le_of_definingIdealSheaf_le B S hS X Z W hZW.ge)
    (le_of_definingIdealSheaf_le B S hS X W Z hZW.le))

/-! ### A sheaf of ideals of `𝒪_X` is determined on the affine charts -/

/-- A section of `𝒪_X` whose restriction along `a` lies in a sheaf submodule `N` has all its
further restrictions along `l ≫ a` in `N`. -/
private theorem unit_map_comp_mem_submodule (X : AlgebraicSpaces B S hS)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {V Y A : SmallEtale B S hS X.1} (s : ToType ((structureRingSheaf B S hS X).obj.obj (op V)))
    (a : A ⟶ V) (l : Y ⟶ A)
    (h : (SheafOfModules.unit (structureRingSheaf B S hS X)).val.map a.op s ∈ N.obj (op A)) :
    (SheafOfModules.unit (structureRingSheaf B S hS X)).val.map (l ≫ a).op s ∈ N.obj (op Y) :=
  N.map (X := op A) (Y := op Y) l.op h

/-- **A sheaf submodule of `𝒪_X` is contained in another as soon as it is on every affine étale
chart.**

The affine étale charts of an algebraic space are a dense subsite of its small étale site,
Stacks 04JS in the form `AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`,
so every étale chart `W` carries a covering sieve each of whose arrows *factors* through an
affine étale chart.  A section over `W` of the smaller submodule restricts, along such a
factorisation, through a section over an affine chart, where the hypothesis applies; locality
of membership in the larger submodule then puts the section itself in it. -/
theorem structureSubmodule_le_of_forall_isAffine (X : AlgebraicSpaces B S hS)
    (N₁ N₂ : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      N₁.obj (op A) ≤ N₂.obj (op A)) :
    N₁ ≤ N₂ := by
  have : (AffineEtale.inclusion B S hS X.1).IsCoverDense
      (SmallEtale.topology B S hS X.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS X.1 X.2).2.isCoverDense'
  intro W s hs
  refine N₂.isSheaf s ((SmallEtale.topology B S hS X.1).superset_covering ?_
    ((AffineEtale.inclusion B S hS X.1).is_cover_of_isCoverDense
      (SmallEtale.topology B S hS X.1) W.unop))
  rintro Y f ⟨A, l, m, ⟨rfl⟩⟩
  exact unit_map_comp_mem_submodule B S hS X N₂ s m l (h _ A.property (N₁.map m.op hs))

/-- **A sheaf submodule of `𝒪_X` is determined by its sections over the affine étale charts.**
Two sheaves of ideals of the structure sheaf of an algebraic space which agree on every étale
chart whose underlying scheme is affine are equal. -/
theorem structureSubmodule_ext_of_forall_isAffine (X : AlgebraicSpaces B S hS)
    (N₁ N₂ : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      N₁.obj (op A) = N₂.obj (op A)) :
    N₁ = N₂ :=
  le_antisymm
    (structureSubmodule_le_of_forall_isAffine B S hS X N₁ N₂ fun A hA => (h A hA).le)
    (structureSubmodule_le_of_forall_isAffine B S hS X N₂ N₁ fun A hA => (h A hA).ge)

/-- **The defining ideal sheaf of a closed subspace is recognised on affine charts.** A sheaf of
ideals of `𝒪_X` whose sections over every *affine* étale chart are the defining ideal of a
closed subspace `Z` there *is* the defining ideal sheaf of `Z`.

This is the step which lets the surjectivity half of Stacks 03MB be proved on affine charts
alone: the ideal produced there automatically agrees with `𝓘_Z` on every chart. -/
theorem definingIdealSheaf_eq_of_forall_isAffine (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      definingIdealAt B S hS X Z (op A) = I.obj (op A)) :
    definingIdealSheaf B S hS X Z = I :=
  structureSubmodule_ext_of_forall_isAffine B S hS X _ I h

/-- **The surjectivity half of Stacks 03MB needs only the affine charts.** If some closed
subspace of `X` has the given sheaf of ideals as its defining ideal on every affine étale chart,
then that sheaf of ideals is a defining ideal sheaf outright.

This is the surjectivity half of the correspondence of Stacks 03MB — the hypothesis `hr` of
`AlgebraicGeometry.Space.closedSubspaceIdealOrderIso` — reduced to its affine form; it is not a
proof of either. -/
theorem exists_definingIdealSheaf_eq_of_exists_forall_isAffine (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : ∃ Z : ClosedSubspaces B S hS X.1, ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      definingIdealAt B S hS X Z (op A) = I.obj (op A)) :
    ∃ Z : ClosedSubspaces B S hS X.1, definingIdealSheaf B S hS X Z = I :=
  h.imp fun Z hZ => definingIdealSheaf_eq_of_forall_isAffine B S hS X Z I hZ

/-- **The inclusion-reversing injection of Stacks 03MB.** Sending a closed subspace of `X` to its
defining ideal sheaf is an order embedding of the closed subspaces into the order dual of the
sheaf submodules of `𝒪_X`.

That the image is exactly the *quasi-coherent* ideal sheaves is part of
`AlgebraicGeometry.Space.closedImmersion_quasicoherentIdeal_correspondence`. -/
noncomputable def definingIdealOrderEmbedding (X : AlgebraicSpaces B S hS) :
    ClosedSubspaces B S hS X.1 ↪o
      ((SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)ᵒᵈ where
  toFun Z := OrderDual.toDual (definingIdealSheaf B S hS X Z)
  inj' := definingIdealSheaf_injective B S hS X
  map_rel_iff' {Z W} :=
    ⟨fun hle => Subtype.coe_le_coe.1 (le_of_definingIdealSheaf_le B S hS X Z W hle),
      fun hle => definingIdealSheaf_antitone B S hS X Z W (Subtype.coe_le_coe.2 hle)⟩

/-! ### Closed subspaces from an invariant sheaf of ideals on a chart -/

/-- **A sheaf of ideals of `𝒪_X` is determined on the affine charts lying over a fixed
surjective chart.** If `Uc` is an étale chart of `X` whose structure morphism is surjective on
points, then two sheaf submodules of `𝒪_X` which agree over every *affine* étale chart admitting
a morphism to `Uc` are already in the same inclusion relation everywhere.

Two coverings are composed.  Every chart `W` is covered by the single chart `W ×_X Uc`, which
lies over `Uc`, by Stacks 03M0's geometric input
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`; and that chart is in turn covered
by arrows factoring through affine charts over it, by the dense-subsite property of the affine
étale charts, Stacks 04JS.  An affine chart over `W ×_X Uc` lies over `Uc`, so the hypothesis
applies to it. -/
theorem structureSubmodule_le_of_forall_isAffine_hom (X : AlgebraicSpaces B S hS)
    (Uc : SmallEtale B S hS X.1) (hsurj : IsSurjective B S hS Uc.1.hom)
    (N₁ N₂ : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      (A ⟶ Uc) → N₁.obj (op A) ≤ N₂.obj (op A)) :
    N₁ ≤ N₂ := by
  have : (AffineEtale.inclusion B S hS X.1).IsCoverDense
      (SmallEtale.topology B S hS X.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS X.1 X.2).2.isCoverDense'
  intro W s hs
  refine N₂.isSheaf s ((SmallEtale.topology B S hS X.1).transitive
    (SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2 Uc hsurj W.unop) _ ?_)
  rintro Y f ⟨i, ⟨m⟩⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    ((AffineEtale.inclusion B S hS X.1).is_cover_of_isCoverDense
      (SmallEtale.topology B S hS X.1) Y)
  rintro Z g ⟨A, l, k, ⟨rfl⟩⟩
  change _ ∈ N₂.obj (op Z)
  rw [Category.assoc]
  exact unit_map_comp_mem_submodule B S hS X N₂ s (k ≫ f) l
    (h _ A.property (k ≫ m) (N₁.map (k ≫ f).op hs))

/-- **A sheaf of ideals of `𝒪_X` is determined by its sections over the affine charts lying over
a fixed surjective chart.** -/
theorem structureSubmodule_ext_of_forall_isAffine_hom (X : AlgebraicSpaces B S hS)
    (Uc : SmallEtale B S hS X.1) (hsurj : IsSurjective B S hS Uc.1.hom)
    (N₁ N₂ : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      (A ⟶ Uc) → N₁.obj (op A) = N₂.obj (op A)) :
    N₁ = N₂ :=
  le_antisymm
    (structureSubmodule_le_of_forall_isAffine_hom B S hS X Uc hsurj N₁ N₂
      fun A hA m => (h A hA m).le)
    (structureSubmodule_le_of_forall_isAffine_hom B S hS X Uc hsurj N₂ N₁
      fun A hA m => (h A hA m).ge)

/-- The arrow of the subobject of `U` cut out by an ideal sheaf is a closed immersion. -/
private theorem isClosedImmersion_mk_subschemeι_arrow {U : Scheme.{u}} (I : U.IdealSheafData) :
    _root_.AlgebraicGeometry.IsClosedImmersion (Subobject.mk I.subschemeι).arrow := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

/-- **The functor of points of a subscheme of a chart pulls back to the functor of points of
the pulled-back subscheme.** -/
theorem subschemePoints_pullback {U A : BigFppfOver B S hS} (g : A ⟶ U)
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U)) :
    subschemePoints B S hS
        ((Subobject.pullback ((BigFppfOver.toScheme B S hS).map g)).obj Z) =
      (subschemePoints B S hS Z).preimage (yoneda.map g) := by
  refine le_antisymm (fun T f hf => ?_) (fun T f hf => ?_)
  · have h := (mem_subschemePoints_iff B S hS (Z := (Subobject.pullback
      ((BigFppfOver.toScheme B S hS).map g)).obj Z) f).1 hf
    rw [Limits.pullback_factors_iff, ← Functor.map_comp] at h
    exact (mem_subschemePoints_iff B S hS (Z := Z) (f ≫ g)).2 h
  · have h := (mem_subschemePoints_iff B S hS (Z := Z) (f ≫ g)).1 hf
    refine (mem_subschemePoints_iff B S hS _).2 ?_
    rw [Limits.pullback_factors_iff, ← Functor.map_comp]
    exact h

section Chart

variable (X : AlgebraicSpaces B S hS) {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X.1}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData)

include hs in
/-- **Invariance of the closed subscheme cut out by an ideal sheaf is a condition on points.**
The two pullbacks of `V(J)` along the two legs of the relation `R = U ×_X U` agree as soon as a
morphism into `R` lands in `V(J)` along one leg exactly when it does along the other.

This replaces the comparison of the two pulled-back *ideal sheaves* by a comparison of their
functors of points, so no formula for the sections of
`AlgebraicGeometry.Scheme.IdealSheafData.comap` along the legs — which are étale, not open
immersions — is needed. -/
theorem isInvariantSubscheme_of_preimage_subschemePoints_eq
    (hpt : (subschemePoints B S hS (Subobject.mk J.subschemeι)).preimage
          (yoneda.map (atlasRelationTarget B S hS hs)) =
        (subschemePoints B S hS (Subobject.mk J.subschemeι)).preimage
          (yoneda.map (atlasRelationSource B S hS hs))) :
    IsInvariantSubscheme B S hS hs (Subobject.mk J.subschemeι) := by
  have hci := isClosedImmersion_mk_subschemeι_arrow J
  refine subschemePoints_injective B S hS ?_ ?_ ?_
  · rw [Scheme.IdealSheafData.pullback_subobject_mk_subschemeι]
    have := isClosedImmersion_mk_subschemeι_arrow (J.comap ((BigFppfOver.toScheme B S hS).map
      (atlasRelationTarget B S hS hs)))
    infer_instance
  · rw [Scheme.IdealSheafData.pullback_subobject_mk_subschemeι]
    have := isClosedImmersion_mk_subschemeι_arrow (J.comap ((BigFppfOver.toScheme B S hS).map
      (atlasRelationSource B S hS hs)))
    infer_instance
  · rw [subschemePoints_pullback, subschemePoints_pullback]
    exact hpt

include hs he in
/-- **An invariant sheaf of ideals on a surjective étale chart cuts out a closed subspace.**
The subspace is `AlgebraicGeometry.Space.invariantSubspace` of the closed subscheme of the
chart that the ideal sheaf defines; closedness is Stacks 03I2 for closed immersions, whose
effective-descent hypothesis is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`. -/
theorem isClosedSubspace_invariantSubspace_subschemeι
    (hinv : IsInvariantSubscheme B S hS hs (Subobject.mk J.subschemeι)) :
    IsClosedSubspace B S hS (invariantSubspace B S hS φ (Subobject.mk J.subschemeι)) := by
  have hci := isClosedImmersion_mk_subschemeι_arrow J
  exact isAlgebraicSpace_and_presheaf_invariantSubspace B S hS hs he
    (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) X.2 _
    inferInstance hci hinv

include hs he in
/-- **The defining ideal of the closed subspace cut out by an invariant ideal sheaf, on a chart
lying over the given one.** For an étale chart `A` of `X` with a morphism `m : A ⟶ Uc` to the
chart carrying the ideal sheaf `J`, the defining ideal of the closed subspace at `A` is the
ideal of global functions on `A` cut out by the pullback `m^{-1}J` — that is, the kernel of
`Γ(A) ⟶ Γ(V(m^{-1}J))`.

No affineness is needed.  The proof identifies the base change of the subspace along `A` with
the pullback subscheme: its functor of points is the preimage of the functor of points of
`V(J)`, by `AlgebraicGeometry.Space.preimage_invariantSubspace` and the fact that `A ⟶ X`
factors through the chart, and an immersed subscheme is determined by its functor of points. -/
theorem definingIdealAt_invariantSubspace_subschemeι
    (hinv : IsInvariantSubscheme B S hS hs (Subobject.mk J.subschemeι))
    (hZ : IsClosedSubspace B S hS
      (invariantSubspace B S hS φ (Subobject.mk J.subschemeι)))
    (A : SmallEtale B S hS X.1)
    (m : A ⟶ (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.1)) :
    definingIdealAt B S hS X
        ⟨invariantSubspace B S hS φ (Subobject.mk J.subschemeι), hZ⟩ (op A) =
      RingHom.ker ((J.comap ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map m))).subschemeι.appTop).hom := by
  have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map m) ≫ φ = A.1.hom :=
    CostructuredArrow.w m.1
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom)) :=
    hZ.2.property A.1.hom _ _ (hZ.2.rep.isPullback A.1.hom)
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom)) :=
    inferInstance
  have hpres : (Subobject.underlyingIso ((BigFppfOver.toScheme B S hS).map
        (hZ.2.rep.snd A.1.hom))).symm.hom ≫
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom))).arrow =
      (BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom) :=
    Subobject.underlyingIso_arrow _
  have himmp : _root_.AlgebraicGeometry.IsImmersion
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom))).arrow := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk
      ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom))]
    infer_instance
  have hsp : subschemePoints B S hS
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom))) =
      subschemePoints B S hS ((Subobject.pullback ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map m))).obj (Subobject.mk J.subschemeι)) := by
    rw [subschemePoints_eq_range B S hS _ _ hpres,
      range_yoneda_snd_eq_preimage B S hS A.1.hom hZ.2.rep, ← hw,
      Subfunctor.preimage_comp, preimage_invariantSubspace B S hS hs _ hinv,
      subschemePoints_pullback]
  have hqci := isClosedImmersion_mk_subschemeι_arrow (J.comap ((BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS X.1).map m)))
  have hobj : Subobject.mk ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom)) =
      Subobject.mk (J.comap ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map m))).subschemeι := by
    rw [← Scheme.IdealSheafData.pullback_subobject_mk_subschemeι]
    refine subschemePoints_injective B S hS himmp ?_ hsp
    rw [Scheme.IdealSheafData.pullback_subobject_mk_subschemeι]
    exact inferInstance
  rw [definingIdealAt_eq_ker, Scheme.Γ_map_op]
  exact ker_appTop_eq_of_subobject_mk_eq _ _ hobj

include hs he in
/-- **The surjectivity half of Stacks 03MB, reduced to one chart.** Let `φ : U ⟶ X` be a
surjective étale chart of an algebraic space `X` and let `J ⊆ 𝒪_U` be a sheaf of ideals on the
*scheme* `U`, invariant under the relation `R = U ×_X U`.  If, over every étale chart `A` of `X`
lying over `U`, the ideal of global functions cut out by the pullback of `J` is the given sheaf
of ideals `I ⊆ 𝒪_X` at `A`, then `I` is the defining ideal sheaf of a closed subspace of `X`.

This is the surjectivity half of the correspondence of Stacks 03MB — the hypothesis `hr` of
`AlgebraicGeometry.Space.closedSubspaceIdealOrderIso` — reduced to a statement
about one chart and about schemes only: the closed subspace, the descent of the closed immersion
along the chart, and the passage from the charts over `U` to all charts are all discharged here.
What it does **not** do is construct `J` from `I`; see the module documentation. -/
theorem exists_definingIdealSheaf_eq_of_isInvariantSubscheme
    (hinv : IsInvariantSubscheme B S hS hs (Subobject.mk J.subschemeι))
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hmatch : ∀ (A : SmallEtale B S hS X.1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      ∀ m : A ⟶ (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.1),
      RingHom.ker ((J.comap ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map m))).subschemeι.appTop).hom = I.obj (op A)) :
    ∃ Z : ClosedSubspaces B S hS X.1, definingIdealSheaf B S hS X Z = I := by
  have hZ := isClosedSubspace_invariantSubspace_subschemeι B S hS X hs he J hinv
  refine ⟨⟨invariantSubspace B S hS φ (Subobject.mk J.subschemeι), hZ⟩, ?_⟩
  refine structureSubmodule_ext_of_forall_isAffine_hom B S hS X
    (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.1)
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U φ).1 hs) _ I
    fun A hA m => ?_
  exact (definingIdealAt_invariantSubspace_subschemeι B S hS X hs he J hinv hZ A m).trans
    (hmatch A hA m)

end Chart

end Space

end AlgebraicGeometry

end
