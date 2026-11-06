module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.JointlySurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFlatRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Maps from a quasi-coherent module to a parasitic module vanish

Let `𝒳` be an algebraic stack. A map `φ : 𝓣 ⟶ 𝓟` of `𝒪_𝒳`-modules on the fppf site of `𝒳`,
from a quasi-coherent module `𝓣` to a parasitic module `𝓟` (**Stacks 0773**), is zero.

This is the vanishing `Hom(𝓣, 𝓟) = Hom(𝓣, Q 𝓟) = 0` that the source reads off **Stacks 0779**,
proved here directly from the definitions, with no coherator.

* On the slice at an object `y` over which `𝓣` has a global presentation
  `⊕ 𝒪 ⟶ ⊕ 𝒪 ⟶ 𝓣 ⟶ 0`, a map out of `𝓣` is determined by the images of the generators, and
  a generator is a map out of `𝒪`, which is a section over the terminal object `y` of the
  slice. So if `𝓟(y) = 0` the map vanishes on the whole slice at `y`.
* Every object of `𝒳` is covered by objects admitting a map to a flat object (the atlas of
  `𝒳`, `AlgebraicGeometry.Stack.FlatFppf.hasLocalFactorizations_inclusion`), every flat object is
  covered by flat objects over which `𝓣` has a global presentation
  (`AlgebraicGeometry.Stack.exists_flatObject_covering_le_of_mem_associatedTopology`), and `𝓟`
  vanishes at flat objects. So `φ` vanishes on a covering sieve of every object, hence is zero
  because `𝓟` is a sheaf.

## Main results

* `SheafOfModules.uliftUnit_hom_eq_zero_of_isTerminal`: a map out of the structure sheaf of a
  site with a terminal object `t`, into a module whose sections at `t` vanish, is zero.
* `SheafOfModules.hom_over_eq_zero_of_hasGlobalPresentation`: a map out of a module with a
  global presentation on the slice at `y`, into a module vanishing at `y`, is zero on that slice.
* `SheafOfModules.eq_zero_of_locally_presented_vanishing`: the site-level form of the vanishing.
* `AlgebraicGeometry.Stack.eq_zero_of_isQuasicoherentOnSite_of_isParasitic`: the vanishing for
  an algebraic stack.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0776](https://stacks.math.columbia.edu/tag/0776)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m t w

namespace SheafOfModules

section Site

variable {D : Type u} [Category.{v} D] {K : GrothendieckTopology D} {R' : Sheaf K RingCat.{r}}

/-- **A map out of the structure sheaf into a module vanishing at a terminal object is zero.**
Such a map is the section it takes `1` to, and every section of `𝒪` is a multiple of the
restriction of `1` from the terminal object. -/
theorem uliftUnit_hom_eq_zero_of_isTerminal {T₀ : D} (hT : IsTerminal T₀)
    {N : SheafOfModules.{max t r} R'} (hN : Subsingleton (N.val.obj (op T₀)))
    (g : uliftForPresentation.{u, v, r, r, t} (SheafOfModules.unit R') ⟶ N) : g = 0 := by
  ext X x
  obtain ⟨a⟩ := x
  let f : op T₀ ⟶ X := (hT.from X.unop).op
  have h2 : g.val.app (op T₀) (ULift.up (1 : R'.obj.obj (op T₀))) = 0 := hN.elim _ _
  let one : (uliftForPresentation.{u, v, r, r, t} (SheafOfModules.unit R')).val.obj X :=
    ULift.up (1 : R'.obj.obj X)
  have h3 : g.val.app X one = 0 := by
    have hn := PresheafOfModules.naturality_apply g.val f (ULift.up (1 : R'.obj.obj (op T₀)))
    rw [h2, map_zero] at hn
    refine Eq.trans ?_ hn
    congr 1
    apply ULift.ext
    show (1 : R'.obj.obj X) = R'.obj.map f 1
    rw [map_one]
  have hs : ∀ a : R'.obj.obj X, g.val.app X (ULift.up a) = 0 := by
    intro a
    have hm := (g.val.app X).hom.map_smul a one
    rw [h3, smul_zero] at hm
    refine Eq.trans ?_ hm
    congr 1
    exact ULift.ext (mul_one a).symm
  exact hs a

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A map out of a globally presented slice into a module vanishing at the base is zero on
that slice.** -/
theorem hom_over_eq_zero_of_hasGlobalPresentation {T P : SheafOfModules.{m} R} (φ : T ⟶ P)
    {y : C} (hT : (T.over y).HasGlobalPresentation) (hP : Subsingleton (P.val.obj (op y))) :
    φ.over y = 0 := by
  obtain ⟨I, K', P', Q', ι, κ, ⟨hP'⟩, -, a, b, hab, ⟨hb⟩⟩ := hT
  have h0 : b ≫ uliftForPresentationMap (φ.over y) = 0 := by
    refine Cofan.IsColimit.hom_ext hP' _ _ fun i => ?_
    rw [comp_zero]
    refine uliftUnit_hom_eq_zero_of_isTerminal (Over.mkIdTerminal (X := y)) ?_ _
    exact ⟨fun c d => ULift.ext (hP.elim c.down d.down)⟩
  have h1 : uliftForPresentationMap (φ.over y) = 0 :=
    Cofork.IsColimit.hom_ext hb (by simpa using h0)
  ext X x
  exact congrArg (fun f => (f.val.app X (ULift.up x)).down) h1

/-- **Vanishing from local presentations.** A map `φ : T ⟶ P` of sheaves of modules is zero if
every object has a covering sieve each of whose members maps to an object over which `T` has a
global presentation and at which `P` vanishes. -/
theorem eq_zero_of_locally_presented_vanishing {T P : SheafOfModules.{m} R} (φ : T ⟶ P)
    (h : ∀ x : C, ∃ S ∈ J x, ∀ (z : C) (f : z ⟶ x), S f → ∃ (y : C) (_ : z ⟶ y),
      (T.over y).HasGlobalPresentation ∧ Subsingleton (P.val.obj (op y))) :
    φ = 0 := by
  have hz : ∀ (z : C) (y : C) (g : z ⟶ y), (T.over y).HasGlobalPresentation →
      Subsingleton (P.val.obj (op y)) → φ.val.app (op z) = 0 := fun z y g hT hP =>
    congrArg (fun f : T.over y ⟶ P.over y => f.val.app (op (Over.mk g)))
      (hom_over_eq_zero_of_hasGlobalPresentation φ hT hP)
  apply (SheafOfModules.toSheaf R).map_injective
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  obtain ⟨S, hS, hSm⟩ := h V.unop
  apply P.isSheaf.hom_ext ⟨S, hS⟩
  rintro ⟨W, k, hk⟩
  obtain ⟨y, g, hT, hP⟩ := hSm W k hk
  have hW' : ((SheafOfModules.toSheaf R).map φ).hom.app (op W) =
      ((SheafOfModules.toSheaf R).map 0).hom.app (op W) := by
    ext s
    exact congrArg (fun f => f s) (hz W y g hT hP)
  show ((SheafOfModules.toSheaf R).map φ).hom.app V ≫
      ((SheafOfModules.toSheaf R).obj P).obj.map k.op =
    ((SheafOfModules.toSheaf R).map 0).hom.app V ≫
      ((SheafOfModules.toSheaf R).obj P).obj.map k.op
  rw [← NatTrans.naturality, ← NatTrans.naturality, hW']

end Site

end SheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A map from a quasi-coherent module to a parasitic module on an algebraic stack is zero.**

Let `𝒳` be an algebraic stack and `φ : 𝓣 ⟶ 𝓟` a map of `𝒪_𝒳`-modules on the fppf site of `𝒳`
(**Stacks 06TP**), with `𝓣` quasi-coherent (**Stacks 06WG**) and `𝓟` parasitic
(**Stacks 0773**). Then `φ = 0`. This is the vanishing `Hom(𝓣, 𝓟) = 0` the source uses in the
proofs of **Stacks 0779** and **Stacks 0776**, proved without the coherator. -/
theorem eq_zero_of_isQuasicoherentOnSite_of_isParasitic (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {T P : SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)}
    [hT : T.IsQuasicoherentOnSite] (hP : IsParasitic B S hS 𝒳 .fppf P.val) (φ : T ⟶ P) :
    φ = 0 := by
  let J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf
  -- the arrows into an object whose source maps to a flat, presented object
  let Rz : ∀ x : 𝒳.val.val.obj, Sieve x := fun x =>
    { arrows := fun z _ => ∃ (y : 𝒳.val.val.obj) (_ : z ⟶ y),
        flatObject B S hS 𝒳.val y ∧ (T.over y).HasGlobalPresentation
      downward_closed := by
        rintro Y Z f ⟨y, g, hy, hTy⟩ e
        exact ⟨y, e ≫ g, hy, hTy⟩ }
  -- at a flat object, such arrows cover
  have hflat : ∀ w : 𝒳.val.val.obj, flatObject B S hS 𝒳.val w → Rz w ∈ J w := by
    intro w hw
    obtain ⟨I, V, f, hcov, hpres⟩ := hT.locally_hasGlobalPresentation w
    have hT' : Sieve.ofArrows V f ≤ Stacks.SheafOfModules.presentedSieve T w := by
      rintro Z g ⟨Y, h, _, ⟨i⟩, rfl⟩
      exact (Stacks.SheafOfModules.presentedSieve T w).downward_closed (hpres i) h
    obtain ⟨E, hEflat, hEcov, hEle⟩ := exists_flatObject_covering_le_of_mem_associatedTopology
      B S hS 𝒳 .fppf hw (Stacks.SheafOfModules.presentedSieve T w)
      (J.superset_covering hT' hcov)
    refine J.superset_covering ?_ hEcov
    rintro Z g ⟨Y, e, h, ⟨i⟩, rfl⟩
    exact ⟨E.X i, e, hEflat i, hEle _ _ (E.presieve₀_f i)⟩
  have hcover : ∀ x : 𝒳.val.val.obj, Rz x ∈ J x := by
    intro x
    refine J.transitive (FlatFppf.hasLocalFactorizations_inclusion.{u, w} B S hS 𝒳 x) (Rz x) ?_
    rintro z f ⟨d, ⟨ψ⟩⟩
    exact J.pullback_stable ψ (hflat d.obj d.property)
  refine SheafOfModules.eq_zero_of_locally_presented_vanishing φ fun x => ⟨Rz x, hcover x, ?_⟩
  rintro z f ⟨y, g, hy, hTy⟩
  exact ⟨y, g, hTy, hP y hy⟩

end AlgebraicGeometry.Stack

end
