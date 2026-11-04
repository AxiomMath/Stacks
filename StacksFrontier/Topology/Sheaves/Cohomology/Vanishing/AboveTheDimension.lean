module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Square
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.MayerVietoris
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Spectral.Basic
import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Profinite.ClopenRefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksFrontier.Topology.Profinite.Defs
public import StacksFrontier.Topology.Sheaves.EpiMono.Defs
public import StacksFrontier.Topology.Sheaves.Sheaf.Abelian
public import StacksFrontier.Topology.Specialization.Defs
public import StacksFrontier.Topology.Spectral.ConstructibleTopology
public import StacksFrontier.Topology.Spectral.ConstructiblyClosedStable
public import StacksFrontier.Topology.Spectral.LimitGeneralizations
public import StacksFrontier.Topology.Spectral.ProfiniteCharacterization
import StacksFrontier.CategoryTheory.Sites.LocalImageSheaf

/-!
# Cohomology of a spectral space in degrees above its dimension

Stacks 0A3G asserts, for an abelian sheaf `F` on a spectral space `X` of finite Krull dimension
`d`, that (1) `H^q(X, F) = 0` for `q > d` and that (2) `H^d(X, F) → H^d(U, F)` is surjective for
every quasi-compact open `U ⊆ X`. This file proves the part of that statement which does not
depend on comparing cohomology on `X` with cohomology on an inverse limit of quasi-compact
opens, namely the implication (2) ⟹ (1) and the case `d = 0`.

The source argues by induction on `d`. Clause (2) in dimension `d` is proved from clause (1) in
dimensions below `d` by passing to the set `W` of points which specialize into `X ∖ U` without
lying in it — a spectral space of dimension `< d`, which is what
`topologicalKrullDim_specGen_sdiff_lt` records — and then transporting a class that dies on `W`
to a quasi-compact open neighbourhood of `W`. That last transport is Stacks 0A3D, which rests in
turn on the comparison of cohomology along a cofiltered limit of spectral spaces (Stacks 0A37),
and it is the one ingredient not available here; see the implementation notes.

## Main definitions

None.

## Main results

* `cohomology_subsingleton_of_surjective_top_restrictions`: clause (1) of Stacks 0A3G follows
  from clause (2), for a spectral space and with no hypothesis on its dimension.
* `cohomology_subsingleton_of_isProfiniteStacks`: Stacks 0A3F, higher cohomology on a profinite
  space vanishes, in the `Ext` formulation of `Sheaf.H`.
* `cohomology_subsingleton_of_topologicalKrullDim_eq_zero`: clause (1) of Stacks 0A3G for
  `d = 0`, unconditionally.
* `surjective_cohomologyPresheaf_map_top_of_isCohomologyTransport` and
  `cohomology_subsingleton_of_isCohomologyTransport`: clause (2), and then clause (1) in every
  degree above `d`, from `IsCohomologyTransport` — the shape in which the source's induction
  consumes Stacks 0A3D. These complete the induction: with that one property the tag is proved.
* `subsingleton_sheafH_of_isCohomologyTransport`: the same conclusion in the global `Sheaf.H`
  spelling, which is the one the consumers of Stacks 0A3G ask for.
* `isProfiniteStacks_of_topologicalKrullDim_eq_zero`: a zero-dimensional spectral space is
  profinite.
* `topologicalKrullDim_specGen_sdiff_lt`: for constructible `E` in a spectral space of dimension
  `d`, the points specializing into `E` but outside `E` have dimension `< d`.
* `exists_isCompact_sup_eq_top_inf_le`: the two-element quasi-compact cover used by the
  Mayer–Vietoris step.

## Implementation notes

Cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant abelian
sheaf `ℤ`, and cohomology over an open subset is `Sheaf.H'`, the value of
`Sheaf.cohomologyPresheaf`. Vanishing is expressed as `Subsingleton` rather than `IsZero`, so
that the two-out-of-three clauses which are statements about individual classes can be stated
and used uniformly.

Clause (1)-from-(2) is *not* proved by the source's route through Čech cohomology and Leray
acyclicity. Instead the induction runs over the degree `q`: a positive-degree class over a
quasi-compact open is locally trivial (Stacks 01FW), the quasi-compact opens of a spectral space
form a basis closed under intersection, and the finitely many pieces of a trivializing cover are
merged two at a time with the Mayer–Vietoris sequence of
`CategoryTheory.GrothendieckTopology.MayerVietorisSquare`, whose degree-`(q-1)` surjectivity
input is clause (2) when `q - 1 = d` and the inductive hypothesis when `q - 1 > d`. This keeps
the whole argument inside the `Ext` long exact sequence, which is the only long exact sequence
available for sheaf cohomology as Mathlib defines it.

This file leaves exactly one input to be supplied from outside: the `IsCohomologyTransport`
predicate below. In the source that input is Stacks 0A3D, in its clause (2), which identifies
`H^p(W ∖ E, F|_{W ∖ E})` for constructible `E` with the filtered colimit of `H^p(V ∖ E, F)` over
the quasi-compact open neighbourhoods `V` of `E`, where `W` is the set of points specializing
into `E`. (Clause (1) of that tag, over `W` rather than `W ∖ E`, is the companion statement and
is not what this induction consumes.) Both clauses of 0A3D are themselves proved, in
`StacksFrontier/Topology/Sheaves/Cohomology/CompactSubset/GeneralizationsOfCohomology.lean` and
`StacksFrontier/Topology/Sheaves/Cohomology/CompactSubset/GeneralizationsOfComplementCohomology.lean`.

**Nothing of Stacks 0A3G is left open by the library.** Downstream of this file,
`StacksFrontier/Topology/Sheaves/Cohomology/Vanishing/SpectralSpaces.lean` discharges
`IsCohomologyTransport` unconditionally — in positive dimension by
`Stacks.CohomologyVanishing.isCohomologyTransport_of_topologicalKrullDim_eq`, through the
comparison map of Stacks 09V3 along a quasi-compact set stable under generalization, and in
dimension zero because a quasi-compact open of a zero-dimensional spectral space is clopen —
and so proves clauses (1) and (2) of the tag with no hypothesis beyond spectrality and the
dimension bound. Clause (3) is
`Stacks.CohomologyVanishing.subsingleton_rightDerived_supportedSections_of_topologicalKrullDim_le`
in `StacksFrontier/Topology/Sheaves/Cohomology/Vanishing/SpectralSupportVanishing.lean`.

The predicate `IsCohomologyTransport` below is precisely the consequence of 0A3D (2) that the
induction uses, with the inductive vanishing already applied to its target: it says that a
degree-`d` class over a quasi-compact open `U` dies on `U ⊓ V` for some quasi-compact open
`V ⊇ X ∖ U`. It is stated without reference to any sheaf on a non-open subspace, because every
term of 0A3D's colimit is a value of the cohomology presheaf of `F` itself — `V ∖ E = V ⊓ U` is
an open of `X`. Only the *target* of 0A3D's comparison lives on the subspace `W ∖ E`, and the
role of the dimension drop `topologicalKrullDim_specGen_sdiff_lt` is to make that target vanish
by clause (1) in dimensions `< d`.

With `IsCohomologyTransport` in hand the whole of Stacks 0A3G follows, and both steps are proved
below: clause (2) by `surjective_cohomologyPresheaf_map_top_of_isCohomologyTransport`, which is
the Mayer–Vietoris gluing for the cover `X = U ∪ V`, and then clause (1) in every degree above
`d` by `cohomology_subsingleton_of_surjective_top_restrictions`.

`exists_isCompact_sup_eq_top_inf_le` is the variant geometric input, for the form of 0A3D in
which the vanishing is known only on a neighbourhood of `W` rather than of `E`: it completes a
quasi-compact open `U` to a two-element cover whose overlap is inside a prescribed neighbourhood
of `W`. The route taken below does not need it, because 0A3D's colimit is already indexed by the
quasi-compact open neighbourhoods of `E = X ∖ U`, and such a `V` satisfies `U ⊔ V = ⊤` outright.

## References

* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Tag 0A3F](https://stacks.math.columbia.edu/tag/0A3F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace

universe u v w w'

namespace Stacks.CohomologyVanishing

theorem intProjective :
    Projective (AddCommGrpCat.of (ULift.{v} ℤ)) := by
  refine ⟨?_⟩
  intro E Y f e he
  let : Epi e := he
  obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective e).mp he
    (f.hom (ULift.up 1 : ULift.{v} ℤ))
  let g : ULift.{v} ℤ →+ E := uliftZMultiplesHom E y
  have h1 : e.hom (g (ULift.up 1)) = f.hom (ULift.up 1) := by
    change e.hom ((uliftZMultiplesHom E y) (ULift.up 1)) = f.hom (ULift.up 1)
    rw [uliftZMultiplesHom_apply_apply]
    rw [show AddEquiv.ulift (ULift.up 1 : ULift.{v} ℤ) = (1 : ℤ) from rfl,
      one_smul]
    exact hy
  refine ⟨AddCommGrpCat.ofHom g, ?_⟩
  apply AddCommGrpCat.Hom.ext
  ext z
  cases z with
  | up z =>
    have hz : (ULift.up z : ULift.{v} ℤ) = z • (ULift.up 1) := by ext; simp
    rw [hz, _root_.map_zsmul, _root_.map_zsmul]
    exact congrArg (fun a => z • a) h1

private theorem mv_lift_compatible_pair
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    (x₂ : F.H' n S.toSquare.X₂) (x₃ : F.H' n S.toSquare.X₃)
    (hcompat : (F.cohomologyPresheaf n).map S.toSquare.f₁₂.op x₂ =
      (F.cohomologyPresheaf n).map S.toSquare.f₁₃.op x₃) :
    ∃ x : F.H' n S.toSquare.X₄,
      (F.cohomologyPresheaf n).map S.toSquare.f₂₄.op x = x₂ ∧
      (F.cohomologyPresheaf n).map S.toSquare.f₃₄.op x = x₃ := by
  let x := (AddCommGrpCat.biprodIsoProd _ _).inv ⟨x₂, x₃⟩
  have hxker : S.fromBiprod F n x = 0 := by
    dsimp [x]
    rw [S.fromBiprod_biprodIsoProd_inv_apply]
    rw [hcompat, sub_self]
  obtain ⟨y, hfy⟩ := (ShortComplex.ab_exact_iff _).mp
    ((S.sequence_exact F n (n + 1) (by omega)).exact 0) x hxker
  have hfy' : (S.toBiprod F n).hom y = x := hfy
  refine ⟨y, ?_, ?_⟩
  · have h := congrArg (ConcreteCategory.hom
      (biprod.fst : F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ F.H' n S.X₂)) hfy'
    dsimp [GrothendieckTopology.MayerVietorisSquare.toBiprod] at h
    rw [← ConcreteCategory.comp_apply] at h
    rw [biprod.lift_fst] at h
    simpa [x, AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply] using h
  · have h := congrArg (ConcreteCategory.hom
      (biprod.snd : F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ F.H' n S.X₃)) hfy'
    dsimp [GrothendieckTopology.MayerVietorisSquare.toBiprod] at h
    rw [← ConcreteCategory.comp_apply] at h
    rw [biprod.lift_snd] at h
    simpa [x, AddCommGrpCat.biprodIsoProd_inv_comp_snd_apply] using h

private theorem mv_zero_of_restrict_zero_of_surjective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (q : ℕ) (hq : 0 < q) (x : F.H' q S.toSquare.X₄)
    (hx₂ : (F.cohomologyPresheaf q).map S.toSquare.f₂₄.op x = 0)
    (hx₃ : (F.cohomologyPresheaf q).map S.toSquare.f₃₄.op x = 0)
    (hres : Function.Surjective fun y : F.H' (q - 1) S.toSquare.X₂ =>
      (F.cohomologyPresheaf (q - 1)).map S.toSquare.f₁₂.op y) : x = 0 := by
  let hseq := S.sequence_exact F (q - 1) q (by omega)
  let T := hseq.sc 2
  have hExact := hseq.exact 2
  have hxker : T.g.hom x = 0 := by
    change S.toBiprod F q x = 0
    rw [S.toBiprod_apply, hx₂, hx₃]
    change (AddCommGrpCat.biprodIsoProd _ _).inv (0, 0) = 0
    exact map_zero _
  obtain ⟨y, hfy⟩ := (ShortComplex.ab_exact_iff _).mp hExact x hxker
  obtain ⟨z, hz⟩ := hres y
  have hfrom : S.fromBiprod F (q - 1)
      ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨z, 0⟩) = y := by
    rw [S.fromBiprod_biprodIsoProd_inv_apply]
    change ((F.cohomologyPresheaf (q - 1)).map S.toSquare.f₁₂.op).hom z -
      ((F.cohomologyPresheaf (q - 1)).map S.toSquare.f₁₃.op).hom 0 = y
    have hz' : ((F.cohomologyPresheaf (q - 1)).map S.toSquare.f₁₂.op).hom z = y := hz
    rw [hz']
    simp
  have hδ : S.δ F (q - 1) q (by omega) y = 0 := by
    have h := congrArg (fun f => f ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨z, 0⟩))
      (S.fromBiprod_δ F (q - 1) q (by omega))
    have h' : S.δ F (q - 1) q (by omega)
        (S.fromBiprod F (q - 1)
          ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨z, 0⟩)) = 0 := by
      exact h
    rw [hfrom] at h'
    exact h'
  have hfy' : T.f.hom y = S.δ F (q - 1) q (by omega) y := rfl
  rw [hfy', hδ] at hfy
  exact hfy.symm

section Profinite

variable {X : Type u} [TopologicalSpace X]

private lemma globalSections_epi_of_isProfiniteStacks
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    (hX : IsProfiniteStacks X)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}}
    (f : F ⟶ G) [Epi f] :
    Epi (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj
      (op (⊤ : Opens X))).map f) := by
  apply (AddCommGrpCat.epi_iff_surjective _).2
  intro t
  have hloc : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f.hom := by
    exact Stacks.Sites.LocalImage.epi_localSurjective (Opens.grothendieckTopology X) f
  choose U i hi using fun x : X ↦ hloc.imageSieve_mem t x (by simp)
  have hOpen : TopologicalSpace.IsOpenCover U := by
    apply le_antisymm le_top
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hi x |>.2⟩
  obtain ⟨hcompact, hT2, htd⟩ :=
    (isProfiniteStacks_iff_compact_t2_totallyDisconnected X).mp hX
  let : CompactSpace X := hcompact
  let : T2Space X := hT2
  let : TotallyDisconnectedSpace X := htd
  obtain ⟨n, W, hWref₀, hWcov, hWdisj⟩ :=
    hOpen.exists_finite_nonempty_disjoint_clopen_cover
  have hWref : ∀ j, ∃ i, (W j : Set X) ⊆ U i := fun j => (hWref₀ j).2
  let V : Fin n → Opens X := fun j => ⟨W j, (W j).isClopen'.2⟩
  have hVcov : (⊤ : Opens X) ≤ iSup V := by
    intro x _
    rw [Opens.mem_iSup]
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hWcov (Set.mem_univ x))
    exact ⟨j, hj⟩
  choose x hx using hWref
  choose a ha using fun j => hi (x j) |>.1
  let K₀ := AddCommGrpCat.uliftFunctor.{u, w}
  let K := sheafCompose (Opens.grothendieckTopology X) K₀
  let F₁ : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w} := K.obj F
  let G₁ : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w} := K.obj G
  let f₁ : F₁ ⟶ G₁ := K.map f
  let F₁' : TopCat.Sheaf AddCommGrpCat.{max u w} (TopCat.of X) := F₁
  let G₁' : TopCat.Sheaf AddCommGrpCat.{max u w} (TopCat.of X) := G₁
  let t₁ : ToType (G₁'.obj.obj (op (⊤ : Opens X))) := ULift.up t
  let incl : ∀ j, V j ⟶ U (x j) := fun j => homOfLE (show V j ≤ U (x j) from by
    intro y hy
    exact hx j hy)
  let s : ∀ j, ToType (F₁.obj.obj (op (V j))) := fun j =>
    F₁.obj.map (incl j).op (ULift.up (a j))
  have hcompat : TopCat.Presheaf.IsCompatible F₁'.presheaf V s := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    · have hWbot : W i ⊓ W j = ⊥ := by
        exact le_antisymm (disjoint_iff_inf_le.mp (hWdisj hij)) bot_le
      have hinter : V i ⊓ V j = ⊥ := by
        apply SetLike.coe_injective
        change (V i : Set X) ∩ (V j : Set X) = ∅
        exact congrArg (fun A : Clopens X => (A : Set X)) hWbot
      have hbot : (⊥ : Sieve (⊥ : Opens X)) ∈
          Opens.grothendieckTopology X (⊥ : Opens X) :=
        (Opens.mem_grothendieckTopology (T := X) (U := ⊥) (S := ⊥)).2 (by simp)
      have : Subsingleton (F₁.obj.obj (op (V i ⊓ V j))) := by
        rw [hinter]
        exact AddCommGrpCat.subsingleton_of_isZero
          (Sheaf.isTerminalOfBotCover F₁ (⊥ : Opens X) hbot).isZero
      exact Subsingleton.elim _ _
  obtain ⟨r, hr, -⟩ := F₁'.existsUnique_gluing' V ⊤
    (fun j => homOfLE (show V j ≤ ⊤ from le_top)) hVcov s hcompat
  have hglobal : f₁.hom.app (op ⊤) r = t₁ := by
    refine G₁'.eq_of_locally_eq' V ⊤
      (fun j => homOfLE (show V j ≤ ⊤ from le_top)) hVcov
      (f₁.hom.app (op ⊤) r) t₁ ?_
    intro j
    rw [← ConcreteCategory.comp_apply, ← NatTrans.naturality]
    rw [ConcreteCategory.comp_apply]
    rw [hr j]
    dsimp [s]
    rw [NatTrans.naturality_apply f₁.hom (incl j).op (ULift.up (a j))]
    have hlocal : f₁.hom.app (op (U (x j))) (ULift.up (a j)) =
        ULift.up ((G.obj.map (i (x j)).op) t) := congrArg ULift.up (ha j)
    rw [hlocal]
    change ULift.up ((G.obj.map (incl j).op) ((G.obj.map (i (x j)).op) t)) =
      ULift.up ((G.obj.map (homOfLE (show V j ≤ ⊤ from le_top)).op) t)
    apply congrArg ULift.up
    rw [← Functor.map_comp_apply, ← op_comp]
    have hcomp : incl j ≫ i (x j) = homOfLE (show V j ≤ ⊤ from le_top) :=
      Subsingleton.elim _ _
    rw [hcomp]
  refine ⟨r.down, ?_⟩
  exact congrArg ULift.down hglobal
/-- **Stacks 0A3F.** On a profinite space every positive-degree sheaf cohomology group of every
abelian sheaf vanishes.

Global sections is exact on a profinite space, because local lifts along a cover may be refined
to lifts along a *disjoint* finite clopen cover (Stacks 08ZZ) and those glue with no
compatibility to check. Sheaf cohomology is `Ext` out of the constant sheaf `ℤ`, and the
constant-sheaf functor is left adjoint to global sections, so exactness of global sections makes
that constant sheaf projective and every `Ext` out of it vanishes in positive degree.

This is the `Sheaf.H` (that is, `Ext`) formulation; the right-derived-functor formulation is
`Stacks.CohomologyVanishing.isZero_abelianSheafCohomology_of_isProfiniteStacks`. -/
@[stacks 0A3F "sheaf cohomology as Ext out of the constant sheaf"]
theorem cohomology_subsingleton_of_isProfiniteStacks
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})]
    (hX : IsProfiniteStacks X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (q : ℕ) (hq : 0 < q) : Subsingleton (Sheaf.H.{w', w, u, u} F q) := by
  let P : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w} :=
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj
    (AddCommGrpCat.of (ULift.{w} ℤ))
  let E : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj
      (op (⊤ : Opens X))
  let adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{w}
    (Limits.isTerminalTop : Limits.IsTerminal (⊤ : Opens X))
  let : E.PreservesEpimorphisms :=
    ⟨fun f _ => globalSections_epi_of_isProfiniteStacks hX f⟩
  let : Projective P := adj.map_projective _ intProjective
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  exact subsingleton_of_forall_eq 0 (fun x => Abelian.Ext.eq_zero_of_projective x)

end Profinite

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

omit [SpectralSpace X] in
private lemma cohomologyPresheaf_bot_subsingleton
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (F.H' n (⊥ : Opens X)) := by
  let J := Opens.grothendieckTopology X
  let P := Stacks.Cohomology.Locality.freeYonedaSheaf (J := J) (⊥ : Opens X)
  have hbot : (⊥ : Sieve (⊥ : Opens X)) ∈ J (⊥ : Opens X) :=
    (Opens.mem_grothendieckTopology (T := X) (U := ⊥) (S := ⊥)).2 (by simp)
  have hsections (G : Sheaf J AddCommGrpCat.{u}) :
      Subsingleton (G.obj.obj (op (⊥ : Opens X))) := by
    exact AddCommGrpCat.subsingleton_of_isZero
      (Sheaf.isTerminalOfBotCover G (⊥ : Opens X) hbot).isZero
  let rep (G : Sheaf J AddCommGrpCat.{u}) :
      (P ⟶ G) ≃ G.obj.obj (op (⊥ : Opens X)) :=
    (sheafificationAdjunction J AddCommGrpCat).homEquiv _ _ |>.trans
      (Stacks.Cohomology.Locality.repEquiv (⊥ : Opens X) G.obj)
  have hPinit : IsInitial P := by
    letI : ∀ G : Sheaf J AddCommGrpCat.{u}, Unique (P ⟶ G) := fun G =>
      { default := (rep G).symm 0
        uniq := fun f => (rep G).injective ((hsections G).elim _ _) }
    exact IsInitial.ofUnique P
  let hP : IsZero P := hPinit.isZero
  change Subsingleton (Abelian.Ext.{w'} P F n)
  cases n with
  | zero =>
    let : Subsingleton (P ⟶ F) := ⟨fun f g => hP.eq_of_src f g⟩
    exact (Equiv.subsingleton_congr Abelian.Ext.addEquiv₀.toEquiv).2 inferInstance
  | succ n =>
    let : Projective P := hP.projective
    exact subsingleton_of_forall_eq 0 (fun ξ => Abelian.Ext.eq_zero_of_projective ξ)

private lemma specialization_eq_of_krullDim_zero (hX : topologicalKrullDim X = 0)
    {x y : X} (hxy : x ⤳ y) : x = y := by
  have hdim : topologicalKrullDim X ≤ (0 : WithBot ℕ∞) := by rw [hX]
  have hmax : ∀ Z : IrreducibleCloseds X, IsMax Z := by
    exact (Order.krullDim_nonpos_iff_forall_isMax).mp
      (by simpa only [topologicalKrullDim] using hdim)
  have hle : (⟨closure ({y} : Set X), isIrreducible_singleton.closure,
      isClosed_closure⟩ : IrreducibleCloseds X) ≤
      ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩ := by
    exact closure_minimal (Set.singleton_subset_iff.mpr hxy.mem_closure) isClosed_closure
  have heq : closure ({x} : Set X) = closure ({y} : Set X) := by
    apply Set.Subset.antisymm
    · exact hmax ⟨closure ({y} : Set X), isIrreducible_singleton.closure,
        isClosed_closure⟩ hle
    · exact hle
  apply Inseparable.eq
  rw [inseparable_iff_mem_closure]
  constructor
  · simpa only [heq] using
      (show x ∈ closure ({x} : Set X) from subset_closure (Set.mem_singleton x))
  · exact hxy.mem_closure

private lemma qcOpen_isClosed_of_krullDim_zero (hX : topologicalKrullDim X = 0)
    {U : Set X} (hUo : IsOpen U) (hUc : IsCompact U) : IsClosed U := by
  apply isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization
  · exact hUc.isClopen_constructibleTopology hUo |>.1
  · intro x y hxy hx
    rw [specialization_eq_of_krullDim_zero hX hxy] at hx
    exact hx

/-- A spectral space of Krull dimension zero is profinite.

Dimension zero forbids nontrivial specializations, so every quasi-compact open is stable under
specialization and therefore closed; a spectral space whose quasi-compact opens are all closed is
Hausdorff, hence profinite by Stacks 0905. -/
theorem isProfiniteStacks_of_topologicalKrullDim_eq_zero
    (hX : topologicalKrullDim X = 0) :
    IsProfiniteStacks X := by
  have hT2 : T2Space X := t2Space_of_qcOpen_isClosed fun U hUo hUc =>
    qcOpen_isClosed_of_krullDim_zero hX hUo hUc
  have hTD : TotallyDisconnectedSpace X := totallyDisconnectedSpace_of_t2
  exact (isProfiniteStacks_iff_compact_t2_totallyDisconnected X).2
    ⟨inferInstance, hT2, hTD⟩

/-- If `a` specializes to `b` and `a ≠ b`, the closure of `b` is strictly below that of `a`. -/
private lemma irreducibleCloseds_closure_lt_of_specializes {a b : X} (h : a ⤳ b) (hne : a ≠ b) :
    (⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds X) <
      ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
  refine lt_of_le_of_ne ?_ fun heq => hne ?_
  · exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp h))
      isClosed_closure
  · have hcl : closure ({b} : Set X) = closure {a} :=
      congrArg (fun c : IrreducibleCloseds X => c.carrier) heq
    refine (h.antisymm ?_).eq
    rw [specializes_iff_mem_closure, hcl]
    exact subset_closure rfl

private lemma chainInGeneralizationDifference_lt (d : ℕ)
    (hd : topologicalKrullDim X = d) (E : Set X) (hE : Topology.IsConstructible E)
    (p : LTSeries (IrreducibleCloseds (↑(specGen E \ E)))) : p.length < d := by
  let W := specGen E \ E
  let : SpectralSpace W := isSpectral_specGen_diff_constructible hE
  let y : Fin (p.length + 1) → W := fun i => (p.toFun i).isIrreducible'.genericPoint
  have hy : ∀ i, IsGenericPoint (y i) (p.toFun i).carrier :=
    fun i => (p.toFun i).isIrreducible'.isGenericPoint_genericPoint (p.toFun i).isClosed'
  have hs := Topology.specializes_succ_castSucc_of_isGenericPoint p y hy
  let z : Fin (p.length + 1) → X := fun i => (y i).val
  have hzs : ∀ i : Fin p.length, z i.succ ⤳ z i.castSucc := by
    intro i
    exact (hs i).map continuous_subtype_val
  obtain ⟨e, heE, hye⟩ := (y 0).property.1
  have hne : z 0 ≠ e := by
    intro heq
    have : z 0 ∈ E := by simpa [z, heq] using heE
    exact (y 0).property.2 this
  let cl : X → IrreducibleCloseds X := fun x =>
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hstep0 : cl e < cl (z 0) := irreducibleCloseds_closure_lt_of_specializes hye hne
  have hstep : ∀ i : Fin p.length, cl (z i.castSucc) < cl (z i.succ) := by
    intro i
    refine irreducibleCloseds_closure_lt_of_specializes (hzs i) fun hxy => ?_
    have hcar : (p.toFun i.castSucc).carrier = (p.toFun i.succ).carrier := by
      rw [← hy i.castSucc, ← hy i.succ, Subtype.ext hxy.symm]
    exact (ne_of_lt (p.step i)) (IrreducibleCloseds.ext hcar)
  let q : LTSeries (IrreducibleCloseds X) :=
    ⟨p.length + 1, Fin.cons (cl e) (fun i => cl (z i)), by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hstep0
      · simpa using hstep j⟩
  have hq : ((q.length : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    unfold topologicalKrullDim
    exact le_iSup (fun r : LTSeries (IrreducibleCloseds X) => (↑r.length : WithBot ℕ∞)) q
  have hn : p.length + 1 ≤ d := by
    have := hq
    rw [hd] at this
    exact_mod_cast this
  omega

/-- Let `X` be a spectral space of finite Krull dimension `d` and let `E ⊆ X` be constructible.
The points of `X` which specialize into `E` but do not lie in `E` form a spectral space of
dimension strictly smaller than `d`: a chain of irreducible closed subsets there extends, by one
more step, to a chain in `X`, because the generic point of the largest member specializes to a
point of `E` lying outside the chain.

This is the dimension-drop step in the proof of Stacks 0A3G. -/
theorem topologicalKrullDim_specGen_sdiff_lt (d : ℕ)
    (hd : topologicalKrullDim X = d) (E : Set X) (hE : Topology.IsConstructible E) :
    topologicalKrullDim (↑(specGen E \ E)) < d := by
  let W := specGen E \ E
  let : SpectralSpace W := isSpectral_specGen_diff_constructible hE
  by_cases hd0 : d = 0
  · subst d
    have hW : IsEmpty W := by
      refine ⟨fun x => ?_⟩
      obtain ⟨e, he, hxe⟩ := x.property.1
      have hne : x.val ≠ e := by
        intro h
        exact x.property.2 (h ▸ he)
      have hchain : (1 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
        unfold topologicalKrullDim
        let c : IrreducibleCloseds X :=
          ⟨closure {e}, isIrreducible_singleton.closure, isClosed_closure⟩
        let c' : IrreducibleCloseds X :=
          ⟨closure {x.val}, isIrreducible_singleton.closure, isClosed_closure⟩
        have hlt : c < c' := irreducibleCloseds_closure_lt_of_specializes hxe hne
        let s : LTSeries (IrreducibleCloseds X) :=
          ⟨1, fun i => if i = 0 then c else c', by
            intro i
            have : i = 0 := Subsingleton.elim _ _
            subst i
            simpa [c, c'] using hlt⟩
        exact le_iSup (fun p : LTSeries (IrreducibleCloseds X) => (↑p.length : WithBot ℕ∞)) s
      rw [hd] at hchain
      norm_num at hchain
    have hdimW : topologicalKrullDim W = ⊥ :=
      (topologicalKrullDim_eq_bot_iff_isEmpty W).2 hW
    rw [hdimW]
    exact WithBot.bot_lt_coe 0
  · have hle : topologicalKrullDim W ≤ (d - 1 : ℕ) := by
      unfold topologicalKrullDim
      apply iSup_le
      intro p
      have hp := chainInGeneralizationDifference_lt d hd E hE p
      exact_mod_cast (Nat.le_pred_of_lt hp)
    have hp : (d - 1 : ℕ) < d := Nat.sub_one_lt hd0
    exact lt_of_le_of_lt hle (by exact_mod_cast hp)

private lemma dimension_eq_nat_or_isEmpty {Y : Type*} [TopologicalSpace Y] (d : ℕ)
    (hY : topologicalKrullDim Y < d) :
    IsEmpty Y ∨ ∃ e : ℕ, topologicalKrullDim Y = e ∧ e < d := by
  by_cases hbot : topologicalKrullDim Y = ⊥
  · exact Or.inl ((topologicalKrullDim_eq_bot_iff_isEmpty Y).mp hbot)
  · obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hbot
    have hatop : a ≠ ⊤ := by
      intro ha'
      have hY' : (a : WithBot ℕ∞) < d := by rw [ha]; exact hY
      rw [ha'] at hY'
      exact (not_lt_of_ge le_top) hY'
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp hatop
    have hdim : topologicalKrullDim Y = e := by
      exact ha.symm.trans (congrArg WithBot.some he.symm)
    refine Or.inr ⟨e, hdim, ?_⟩
    have hY' := hY
    rw [hdim] at hY'
    exact_mod_cast hY'

/-- Let `U` and `V` be quasi-compact opens of a spectral space `X` such that `V` contains every
point which specializes into `Uᶜ` without lying in `Uᶜ`. Then `U` can be completed to a
two-element cover of `X` by a quasi-compact open `O` whose overlap with `U` is inside `V`. This
is the geometric input to the Mayer–Vietoris step in Stacks 0A3G. -/
theorem exists_isCompact_sup_eq_top_inf_le
    (U V : Opens X) (hU : IsCompact (U : Set X))
    (hV : IsCompact (V : Set X))
    (hWV : specGen (U : Set X)ᶜ \ (U : Set X)ᶜ ⊆ V) :
    ∃ O : Opens X, IsCompact (O : Set X) ∧ U ⊔ O = ⊤ ∧ U ⊓ O ≤ V := by
  classical
  let E : Set X := (U : Set X)ᶜ
  let B : Set X := (U : Set X) \ V
  have hEc : IsCompact E := U.isOpen.isClosed_compl.isCompact
  have hBc : @IsCompact X (constructibleTopology X) B :=
    (IsConstructible.isClosed_constructibleTopology
      ((hU.isConstructible U.isOpen).sdiff
        (hV.isConstructible V.isOpen))).isCompact_constructibleTopology
  have hsep (y : B) : ∃ A : Opens X, IsCompact (A : Set X) ∧ E ⊆ A ∧ y.val ∉ A := by
    have hEZ : E ⊆ (closure ({y.val} : Set X))ᶜ := by
      intro e he hye
      have hyW : y.val ∈ specGen E \ E :=
        ⟨⟨e, he, specializes_iff_mem_closure.mpr hye⟩, by simpa [E] using y.property.1⟩
      exact y.property.2 (hWV hyW)
    obtain ⟨A, hAc, hAo, hEA, hAZ⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between hEc
        isClosed_closure.isOpen_compl hEZ
    exact ⟨⟨A, hAo⟩, hAc, hEA, fun hy => hAZ hy (subset_closure rfl)⟩
  choose A hAc hEA hyA using hsep
  have hcov : B ⊆ ⋃ y : B, (A y : Set X)ᶜ := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyA ⟨y, hy⟩⟩
  have hAo (y : B) : @IsOpen X (constructibleTopology X) (A y : Set X)ᶜ :=
    ((hAc y).isClopen_constructibleTopology (A y).isOpen).1.isOpen_compl
  obtain ⟨t, ht⟩ := @IsCompact.elim_finite_subcover X (constructibleTopology X)
    B B hBc (fun y : B => (A y : Set X)ᶜ) hAo hcov
  let T : Set (Set X) := (fun y : B => (A y : Set X)) '' (t : Set B)
  have hTf : T.Finite := t.finite_toSet.image _
  have hTo : ∀ S ∈ T, IsOpen S := by
    rintro S ⟨y, hy, rfl⟩
    exact (A y).isOpen
  have hTc : ∀ S ∈ T, IsCompact S := by
    rintro S ⟨y, hy, rfl⟩
    exact hAc y
  let O : Opens X := ⟨⋂₀ T, hTf.isOpen_sInter hTo⟩
  have hO (x : X) : x ∈ O ↔ ∀ y ∈ t, x ∈ A y := by
    simp [O, T]
  have hOc : IsCompact (O : Set X) :=
    QuasiSeparatedSpace.isCompact_sInter hTf (fun S hS => Or.inl (hTo S hS)) hTc
  have hEO : E ⊆ O := fun x hx => (hO x).mpr (fun y _ => hEA y hx)
  refine ⟨O, hOc, ?_, ?_⟩
  · ext x
    change (x ∈ U ∨ x ∈ O) ↔ True
    exact iff_true_intro (or_iff_not_imp_left.mpr (fun hx => hEO hx))
  · intro x hx
    by_contra hxV
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht ⟨hx.1, hxV⟩)
    exact hxy ((hO x).mp hx.2 y hy)

private lemma cohomology_eq_zero_of_surjective_restrictions
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (hn : 0 < n)
    (hres : ∀ (A B : Opens X), IsCompact (A : Set X) → IsCompact (B : Set X) →
      ∀ h : B ≤ A, Function.Surjective
        ((F.cohomologyPresheaf (n - 1)).map (homOfLE h).op))
    (U : Opens X) (hU : IsCompact (U : Set X))
    (x : (F.cohomologyPresheaf n).obj (op U)) : x = 0 := by
  classical
  let P := F.cohomologyPresheaf n
  obtain ⟨S, hS⟩ := Stacks.Cohomology.Locality.cohomologyPresheaf_locally_zero F n hn U x
  have hlocal (y : U) : ∃ (V : Opens X) (_ : IsCompact (V : Set X))
      (_ : y.val ∈ V) (hVU : V ≤ U), P.map (homOfLE hVU).op x = 0 := by
    obtain ⟨A, f, hf, hy⟩ := S.property y.val y.property
    obtain ⟨V, hVc, hVo, hyV, hVA⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between isCompact_singleton
        A.isOpen (Set.singleton_subset_iff.mpr hy)
    let V' : Opens X := ⟨V, hVo⟩
    have hVU : V' ≤ U := hVA.trans (leOfHom f)
    refine ⟨V', hVc, hyV rfl, hVU, ?_⟩
    have h := congrArg (P.map (homOfLE (show V' ≤ A from hVA)).op) (hS ⟨A, f, hf⟩)
    rw [map_zero] at h
    rw [← Functor.map_comp_apply, ← op_comp] at h
    exact h
  choose V hVc hyV hVU hxV using hlocal
  have hfin : ∀ t : Finset U, IsCompact ((t.sup V : Opens X) : Set X) ∧
      ∀ h : t.sup V ≤ U, P.map (homOfLE h).op x = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨by simp, ?_⟩
      intro h
      have : Subsingleton (F.H' n (⊥ : Opens X)) := cohomologyPresheaf_bot_subsingleton F n
      exact @Subsingleton.elim (F.H' n ⊥)
        (cohomologyPresheaf_bot_subsingleton F n) _ _
    | @insert y t hyt ih =>
      rw [Finset.sup_insert]
      refine ⟨(hVc y).union ih.1, ?_⟩
      intro h
      let A := V y
      let B := t.sup V
      let sq : Square (Opens X) := {
        X₁ := A ⊓ B
        X₂ := A
        X₃ := B
        X₄ := A ⊔ B
        f₁₂ := homOfLE inf_le_left
        f₁₃ := homOfLE inf_le_right
        f₂₄ := homOfLE le_sup_left
        f₃₄ := homOfLE le_sup_right
        fac := Subsingleton.elim _ _ }
      let T := Opens.mayerVietorisSquare' sq rfl rfl
      apply mv_zero_of_restrict_zero_of_surjective (Opens.grothendieckTopology X)
        T F n hn (P.map (homOfLE h).op x)
      · change P.map (homOfLE (show A ≤ A ⊔ B from le_sup_left)).op
          (P.map (homOfLE h).op x) = 0
        rw [← Functor.map_comp_apply, ← op_comp]
        exact hxV y
      · change P.map (homOfLE (show B ≤ A ⊔ B from le_sup_right)).op
          (P.map (homOfLE h).op x) = 0
        rw [← Functor.map_comp_apply, ← op_comp]
        exact ih.2 (le_sup_right.trans h)
      · exact hres A (A ⊓ B) (hVc y)
          (QuasiSeparatedSpace.inter_isCompact _ _ A.isOpen (hVc y) B.isOpen ih.1)
          inf_le_left
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun y : U => (V y : Set X))
    (fun y => (V y).isOpen) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩)
  have heq : t.sup V = U := by
    apply le_antisymm (Finset.sup_le (fun y _ => hVU y))
    intro y hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact (Finset.le_sup hz : V z ≤ t.sup V) hyz
  have h := (hfin t).2
  rw [heq] at h
  simpa using h le_rfl

/-- **Stacks 0A3G, the implication (2) ⟹ (1).** Let `X` be a spectral space and `F` an abelian
sheaf on `X`. Suppose that for every quasi-compact open `U ⊆ X` the restriction
`H^d(X, F) → H^d(U, F)` is surjective. Then `H^q(U, F) = 0` for every quasi-compact open `U` and
every `q > d`.

The hypothesis is clause (2) of Stacks 0A3G in degree `d`, and the conclusion is clause (1); the
dimension of `X` never enters, so this is the formal part of the source's argument. For that
reason this theorem carries no `@[stacks]` attribute: it is a step of the source's proof, taking
one clause of the tag as an input and returning another, and a declaration shaped like that
states nothing about the tag. Clause (1) itself, with the dimension hypothesis and no surjectivity
input, is `Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le`; the whole
proposition is
`Stacks.CohomologyVanishing.subsingleton_sheafH_and_surjective_and_subsingleton_supported_of_topologicalKrullDim_eq`.
The proof
replaces the source's Čech-and-Leray route by induction on `q`: a positive-degree class over a
quasi-compact open is locally trivial (Stacks 01FW), the quasi-compact opens of a spectral space
are a basis closed under intersection, and two opens at a time are merged with the Mayer–Vietoris
sequence, where surjectivity in degree `q - 1` is supplied either by the hypothesis (when
`q - 1 = d`) or by the inductive hypothesis (when `q - 1 > d`). -/
theorem cohomology_subsingleton_of_surjective_top_restrictions
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d : ℕ)
    (hres : ∀ (U : Opens X), IsCompact (U : Set X) → Function.Surjective
      ((F.cohomologyPresheaf d).map (homOfLE (show U ≤ ⊤ from le_top)).op))
    (q : ℕ) (hq : d < q) (U : Opens X) (hU : IsCompact (U : Set X)) :
    Subsingleton ((F.cohomologyPresheaf q).obj (op U)) := by
  induction q using Nat.strong_induction_on generalizing U with
  | h q ih =>
    apply subsingleton_of_forall_eq 0
    intro x
    apply cohomology_eq_zero_of_surjective_restrictions F q (by omega) _ U hU x
    intro A B hAc hBc hBA
    by_cases heq : q - 1 = d
    · rw [heq]
      intro y
      obtain ⟨z, hz⟩ := hres B hBc y
      refine ⟨(F.cohomologyPresheaf d).map (homOfLE (show A ≤ ⊤ from le_top)).op z, ?_⟩
      rw [← Functor.map_comp_apply, ← op_comp]
      exact hz
    · have := ih (q - 1) (by omega) (by omega) B hBc
      intro y
      exact ⟨0, Subsingleton.elim _ _⟩

/-- **Stacks 0A3G, clause (1) in dimension zero.** Let `X` be a spectral space of Krull dimension
`0` and let `F` be an abelian sheaf on `X`. Then `H^q(X, F) = 0` for every `q > 0`.

This is the base case of the induction on the dimension in Stacks 0A3G: a zero-dimensional spectral space is profinite
(`isProfiniteStacks_of_topologicalKrullDim_eq_zero`), and on a profinite space positive-degree
cohomology vanishes (`cohomology_subsingleton_of_isProfiniteStacks`).

The hypotheses are satisfiable: `X = Spec R` for a zero-dimensional ring such as a field, a
finite product of fields, or `ZMod 4`, has `topologicalKrullDim X = 0`, and the conclusion is
then a genuine statement about every abelian sheaf on a nontrivial space. -/
@[stacks 0A3G "clause (1) for dimension zero"]
theorem cohomology_subsingleton_of_topologicalKrullDim_eq_zero
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (q : ℕ) (hX : topologicalKrullDim X = ((0 : ℕ) : WithBot ℕ∞)) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w', w, u, u} F q) :=
  cohomology_subsingleton_of_isProfiniteStacks
    (isProfiniteStacks_of_topologicalKrullDim_eq_zero (by exact_mod_cast hX)) F q hq

/-! ### Clause (2), and then clause (1), from the transport that Stacks 0A3D supplies -/

section Transport

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **The transport property that Stacks 0A3D (2) supplies in degree `d`**: every degree-`d`
cohomology class over a quasi-compact open `U` of `X` is killed by restriction to `U ⊓ V` for
some quasi-compact open `V` containing the complement of `U`.

Write `Z = X ∖ U`, closed and constructible because `U` is a quasi-compact open of a spectral
space, and write `W` for the set of points of `X` specializing into `Z`. Stacks 0A3D (2)
presents `H^d(W ∖ Z, F|_{W ∖ Z})` as the filtered colimit of `H^d(V ∖ Z, F)` over the
quasi-compact open neighbourhoods `V` of `Z`. Every term of that colimit is a value of the
cohomology presheaf of `F` itself, since `V ∖ Z = V ⊓ U` is an open of `X`; only the target of
the comparison involves a sheaf on a subspace that is not open. The class `ξ` is the image of
the term `V = ⊤`, and `W ∖ Z` is a spectral space of dimension `< d` by
`topologicalKrullDim_specGen_sdiff_lt`, so clause (1) of Stacks 0A3G in dimensions `< d` makes
that target vanish; injectivity of the colimit comparison then produces the `V` asked for here.

This is therefore exactly the shape in which the induction of Stacks 0A3G consumes Stacks
0A3D, and no `@[stacks]` attribute is placed on it: it is a hypothesis, not a theorem. -/
def IsCohomologyTransport (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (d : ℕ) : Prop :=
  ∀ U : Opens X, IsCompact (U : Set X) → ∀ ξ : (F.cohomologyPresheaf d).obj (op U),
    ∃ V : Opens X, IsCompact (V : Set X) ∧ (U : Set X)ᶜ ⊆ (V : Set X) ∧
      (F.cohomologyPresheaf d).map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op ξ = 0

omit [SpectralSpace X] in
/-- **Stacks 0A3G, clause (2), from the transport of Stacks 0A3D.** If every degree-`d` class
over a quasi-compact open `U` dies on `U ⊓ V` for some quasi-compact open `V ⊇ X ∖ U`, then the
restriction `H^d(X, F) → H^d(U, F)` is surjective for every quasi-compact open `U`.

This is the Mayer–Vietoris step of the source's argument. The hypothesis makes `X = U ∪ V` a
two-element cover by quasi-compact opens on which the class `ξ` and the class `0` agree — they
agree on `U ⊓ V` precisely because `ξ` dies there — so the Mayer–Vietoris sequence of
`CategoryTheory.GrothendieckTopology.MayerVietorisSquare` glues them to a class over `X` which
restricts to `ξ` on `U`. No hypothesis on the dimension of `X` enters. -/
theorem surjective_cohomologyPresheaf_map_top_of_isCohomologyTransport
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d : ℕ)
    (htr : IsCohomologyTransport F d) (U : Opens X) (hU : IsCompact (U : Set X)) :
    Function.Surjective
      ((F.cohomologyPresheaf d).map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  intro ξ
  obtain ⟨V, hVc, hUV, hξ⟩ := htr U hU ξ
  have htop : (⊤ : Opens X) = U ⊔ V := by
    refine le_antisymm (fun x _ => ?_) le_top
    by_cases hx : x ∈ U
    · exact Or.inl hx
    · exact Or.inr (hUV hx)
  let sq : Square (Opens X) := {
    X₁ := U ⊓ V
    X₂ := U
    X₃ := V
    X₄ := ⊤
    f₁₂ := homOfLE inf_le_left
    f₁₃ := homOfLE inf_le_right
    f₂₄ := homOfLE le_top
    f₃₄ := homOfLE le_top
    fac := Subsingleton.elim _ _ }
  let T := Opens.mayerVietorisSquare' sq htop rfl
  have hcompat : (F.cohomologyPresheaf d).map T.toSquare.f₁₂.op ξ =
      (F.cohomologyPresheaf d).map T.toSquare.f₁₃.op 0 := by
    rw [map_zero]
    exact hξ
  obtain ⟨x, hx₂, -⟩ :=
    mv_lift_compatible_pair (Opens.grothendieckTopology X) T F d ξ 0 hcompat
  exact ⟨x, hx₂⟩

/-- **Stacks 0A3G, clause (1), from the transport of Stacks 0A3D.** With that transport
available in degree `d`, the cohomology of `F` vanishes over every quasi-compact open in every
degree `q > d`.

Together with `topologicalKrullDim_specGen_sdiff_lt` this is the whole of the source's induction
on the dimension: the transport in degree `d` is what Stacks 0A3D (2) yields once clause (1) is
known in dimensions `< d`, it gives clause (2) in degree `d` by
`surjective_cohomologyPresheaf_map_top_of_isCohomologyTransport`, and clause (2) gives clause
(1) in all degrees above `d` by `cohomology_subsingleton_of_surjective_top_restrictions`. The
transport is the single remaining input. -/
theorem cohomology_subsingleton_of_isCohomologyTransport
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d : ℕ)
    (htr : IsCohomologyTransport F d) (q : ℕ) (hq : d < q) (U : Opens X)
    (hU : IsCompact (U : Set X)) :
    Subsingleton ((F.cohomologyPresheaf q).obj (op U)) :=
  cohomology_subsingleton_of_surjective_top_restrictions F d
    (fun V hV =>
      surjective_cohomologyPresheaf_map_top_of_isCohomologyTransport F d htr V hV) q hq U hU

/-- **Stacks 0A3G, clause (1), in the global `Sheaf.H` spelling.** With the transport of Stacks
0A3D available in degree `d`, the global cohomology `H^q(X, F)` vanishes for every `q > d`.

This is `cohomology_subsingleton_of_isCohomologyTransport` at the terminal open `⊤`, which a
spectral space being compact is quasi-compact, read through
`Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top`. It is the shape
in which the consumers of Stacks 0A3G ask for it: the comparison of abelian-sheaf cohomology
with cohomology in `Mod(𝒪_X)` is stated for `Sheaf.H`, not for the cohomology presheaf. -/
theorem subsingleton_sheafH_of_isCohomologyTransport
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d : ℕ)
    (htr : IsCohomologyTransport F d) (q : ℕ) (hq : d < q) :
    Subsingleton (Sheaf.H.{u, u, u, u} F q) := by
  refine (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
    F q).2 ?_
  refine cohomology_subsingleton_of_isCohomologyTransport F d htr q hq ⊤ ?_
  simpa using isCompact_univ (X := X)

end Transport

section Nonvacuity

/-- The prime spectrum of a nontrivial commutative ring of Krull dimension zero is a nonempty
spectral space of topological Krull dimension zero.

This is what makes `cohomology_subsingleton_of_topologicalKrullDim_eq_zero` a statement with
content: its hypotheses are met by `Spec R` for every nontrivial zero-dimensional `R`, which
includes every field, every nontrivial artinian ring and every nontrivial Boolean ring — the
last giving spectra that are arbitrary nonempty profinite spaces, so the class is not confined
to finite or one-point spaces. -/
theorem topologicalKrullDim_primeSpectrum_eq_zero (R : Type u) [CommRing R] [Nontrivial R]
    [Ring.KrullDimLE 0 R] :
    topologicalKrullDim (PrimeSpectrum R) = ((0 : ℕ) : WithBot ℕ∞) := by
  have hne : Nonempty (IrreducibleCloseds (PrimeSpectrum R)) :=
    ⟨⟨closure {Classical.arbitrary (PrimeSpectrum R)},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  refine le_antisymm ?_ ?_
  · rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact_mod_cast Ring.krullDimLE_iff.mp ‹_›
  · simpa [topologicalKrullDim] using
      Order.krullDim_nonneg (α := IrreducibleCloseds (PrimeSpectrum R))

/-- A fully instantiated consequence of
`cohomology_subsingleton_of_topologicalKrullDim_eq_zero`, with every typeclass hypothesis
discharged by instance synthesis: on `Spec (ZMod 6)` every positive-degree cohomology group of
every abelian sheaf vanishes.

`ZMod 6` is a nontrivial finite, hence artinian, hence zero-dimensional ring, and
`ZMod 6 ≅ ZMod 2 × ZMod 3`, so its spectrum has two points rather than one and the site of opens
is not the trivial one. -/
theorem subsingleton_cohomology_primeSpectrum_zmod_six
    (F : Sheaf (Opens.grothendieckTopology (PrimeSpectrum (ZMod 6))) AddCommGrpCat.{0})
    (q : ℕ) (hq : 0 < q) : Subsingleton (Sheaf.H.{0, 0, 0, 0} F q) := by
  have : Nontrivial (ZMod 6) := inferInstanceAs (Nontrivial (Fin 6))
  have : HasExt.{0}
      (Sheaf (Opens.grothendieckTopology (PrimeSpectrum (ZMod 6))) AddCommGrpCat.{0}) :=
    hasExt_of_enoughInjectives _
  exact cohomology_subsingleton_of_topologicalKrullDim_eq_zero F q
    (topologicalKrullDim_primeSpectrum_eq_zero (ZMod 6)) hq

end Nonvacuity

end Stacks.CohomologyVanishing
