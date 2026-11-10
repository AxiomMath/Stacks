module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionLimit
public import StacksFrontier.AlgebraicGeometry.Limits.FibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksCore.Tactic.StacksAttribute

/-!
# Enlarging a closed subscheme with bounded fibre dimension

Let `f : X ⟶ S` be a morphism of finite presentation onto a quasi-compact and quasi-separated
scheme, and let `Z ⊆ X` be a closed subscheme all of whose fibres over `S` have dimension at
most `d`.  Then `Z` is contained in a closed subscheme `Z' ⊆ X` whose closed immersion into `X`
is of finite presentation and whose fibres over `S` still have dimension at most `d`.

## Main results

* `exists_finitePresentation_closedImmersion_of_forall_topologicalKrullDim_fiber_le`, in the
  `AlgebraicGeometry` namespace: **Stacks 05M6**.

## Implementation notes

Closed subschemes are represented by their closed immersion into the ambient scheme, and the
inclusion `Z ⊆ Z'` by a factorisation of `Z ⟶ X` through `Z' ⟶ X` whose first factor is itself a
closed immersion.  Finite presentation is `AlgebraicGeometry.FinitePresentation`, the
development's spelling of Tag 01TP, and the dimension of a fibre is
`topologicalKrullDim` of `Scheme.Hom.fiber`, which is the spelling used by Tag 05M5 in
`StacksFrontier.AlgebraicGeometry.Limits.FibreDimensionBound`.

The source's proof writes the base as a limit of Noetherian schemes, descends `f` to that
system, and takes the scheme theoretic images of `Z` in the resulting models.  The argument here
replaces that approximation of the base by an approximation of the closed subscheme itself:
`AlgebraicGeometry.exists_isLimit_closedImmersion_finitePresentation` (Tag 09ZP) exhibits
`Z ⟶ X` as the limit of the directed inverse system of those closed subschemes of `X` containing
`Z` whose closed immersion is of finite presentation, which is exactly the system of candidates
for `Z'`.  Composing that system with `f` gives a morphism to the constant system at `S`, whose
limit is `Z ⟶ X ⟶ S`; the transition morphisms of the constant system are identities, hence
affine, and the comparison maps of the source system are closed immersions because they are
closed immersions into `X` after composition.  So Tag 05M5, applied to this morphism of systems,
produces a stage at which the fibre dimension bound already holds, and that stage is `Z'`.  Its
closed immersion into `X` is of finite presentation by construction, and `Z` maps into it by the
limit projection.

## References

* [Stacks Project, Tag 05M6](https://stacks.math.columbia.edu/tag/05M6)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 09ZP](https://stacks.math.columbia.edu/tag/09ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- If `a ≫ b = c` with `b` and `c` closed immersions, then `a` is a closed immersion. -/
private theorem isClosedImmersion_of_comp_eq {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ Z) [IsClosedImmersion b] [IsClosedImmersion c] (h : a ≫ b = c) :
    IsClosedImmersion a := by
  subst h
  exact IsClosedImmersion.of_comp a b

/-- **Stacks Project, Tag 05M6.** Let `S` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ S` be a morphism of finite presentation and let `d` be a natural number.  A closed
subscheme `Z ⊆ X`, given by the closed immersion `i`, all of whose fibres over `S` have
dimension at most `d`, is contained in a closed subscheme `Z' ⊆ X`, given by the closed
immersion `j`, such that `j` is of finite presentation and all fibres of `Z'` over `S` still
have dimension at most `d`. -/
@[stacks 05M6]
theorem exists_finitePresentation_closedImmersion_of_forall_topologicalKrullDim_fiber_le
    {S X Z : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) (hf : FinitePresentation f) (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim ((i ≫ f).fiber s) ≤ (d : WithBot ℕ∞)) :
    ∃ (Z' : Scheme.{u}) (j : Z' ⟶ X) (h : Z ⟶ Z'),
      IsClosedImmersion j ∧ IsClosedImmersion h ∧ i = h ≫ j ∧ FinitePresentation j ∧
        ∀ s : S, topologicalKrullDim ((j ≫ f).fiber s) ≤ (d : WithBot ℕ∞) := by
  classical
  have hfqc : QuasiCompact f := hf.quasiCompact
  have hfqs : QuasiSeparated f := hf.quasiSeparated
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨I, hpre, hnon, hdir, D, t, p, hcZ, hpt, hstage⟩ :=
    exists_isLimit_closedImmersion_finitePresentation i
  let : Preorder I := hpre
  let : Nonempty I := hnon
  let : IsDirected I (· ≤ ·) := hdir
  let : EssentiallySmall.{u} I := essentiallySmallSelf.{u} I
  let : IsFiltered I := inferInstance
  let : IsCofiltered Iᵒᵖ := inferInstance
  let : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  -- The constant system at `S`, and the morphism of systems induced by `f`.
  let F : Iᵒᵖ ⥤ Scheme.{u} := (Functor.const Iᵒᵖ).obj S
  let g : D ⟶ F := t ≫ (Functor.const Iᵒᵖ).map f
  let cZ : Cone D := Cone.mk Z p
  let cS : Cone F := constCone Iᵒᵖ S
  have hcS : IsLimit cS := isLimitConstCone Iᵒᵖ S
  have hfac (k : Iᵒᵖ) : p.app k ≫ t.app k = i := by
    have := congrArg
      (fun η : (Functor.const Iᵒᵖ).obj Z ⟶ (Functor.const Iᵒᵖ).obj X => η.app k) hpt
    simpa using this
  -- The morphism induced on the limits is `i ≫ f`.
  have hlimitMap : hcS.lift ((Cone.postcompose g).obj cZ) = i ≫ f := by
    refine hcS.hom_ext fun k => ?_
    calc
      hcS.lift ((Cone.postcompose g).obj cZ) ≫ cS.π.app k =
          ((Cone.postcompose g).obj cZ).π.app k := hcS.fac _ k
      _ = p.app k ≫ t.app k ≫ f := rfl
      _ = i ≫ f := by rw [← Category.assoc, hfac]
      _ = (i ≫ f) ≫ cS.π.app k := by simp [cS]
  have hdimLimit : ∀ s : cS.pt,
      topologicalKrullDim
        ((hcS.lift ((Cone.postcompose g).obj cZ)).fiber s) ≤ (d : WithBot ℕ∞) :=
    hlimitMap ▸ hdim
  -- The hypotheses of Tag 05M5 for this morphism of systems.
  let : ∀ {a b : Iᵒᵖ} (q : a ⟶ b), IsAffineHom (F.map q) := by
    intro a b q
    change IsAffineHom (𝟙 S)
    infer_instance
  let : ∀ a : Iᵒᵖ, CompactSpace (F.obj a) := fun _ => (inferInstance : CompactSpace S)
  let : ∀ a : Iᵒᵖ, QuasiSeparatedSpace (F.obj a) :=
    fun _ => (inferInstance : QuasiSeparatedSpace S)
  let : ∀ a : Iᵒᵖ, LocallyOfFiniteType (g.app a) := by
    intro a
    let : LocallyOfFinitePresentation (t.app a) :=
      (hstage a).2.locallyOfFinitePresentation
    let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
    change LocallyOfFiniteType (t.app a ≫ f)
    infer_instance
  let : ∀ a : Iᵒᵖ, QuasiCompact (g.app a) := by
    intro a
    let : QuasiCompact (t.app a) := (hstage a).2.quasiCompact
    change QuasiCompact (t.app a ≫ f)
    infer_instance
  have htransition : ∀ {a b : Iᵒᵖ} (q : a ⟶ b), IsClosedImmersion (D.map q) := by
    intro a b q
    let : IsClosedImmersion (t.app b) := (hstage b).1
    let : IsClosedImmersion (t.app a) := (hstage a).1
    exact isClosedImmersion_of_comp_eq (D.map q) (t.app b) (t.app a) (by simp)
  let : ∀ {a b : Iᵒᵖ} (q : a ⟶ b),
      IsClosedImmersion (pullback.lift (D.map q) (g.app a) (g.naturality q)) := by
    intro a b q
    let : IsClosedImmersion (D.map q) := htransition q
    have hfst : IsIso (pullback.fst (g.app b) (F.map q)) := by
      have : IsIso (F.map q) := by
        change IsIso (𝟙 S)
        infer_instance
      infer_instance
    have hlift : pullback.lift (D.map q) (g.app a) (g.naturality q) =
        D.map q ≫ inv (pullback.fst (g.app b) (F.map q)) := by
      refine (cancel_mono (pullback.fst (g.app b) (F.map q))).1 ?_
      calc
        pullback.lift (D.map q) (g.app a) (g.naturality q) ≫
            pullback.fst (g.app b) (F.map q) = D.map q := pullback.lift_fst _ _ _
        _ = (D.map q ≫ inv (pullback.fst (g.app b) (F.map q))) ≫
              pullback.fst (g.app b) (F.map q) := by simp
    rw [hlift]
    infer_instance
  -- Tag 05M5 supplies the stage.
  obtain ⟨k, hk⟩ :=
    exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall D F g cZ hcZ cS hcS d
      hdimLimit
  refine ⟨D.obj k, t.app k, p.app k, (hstage k).1, ?_, (hfac k).symm, (hstage k).2, ?_⟩
  · let : IsClosedImmersion (t.app k) := (hstage k).1
    exact isClosedImmersion_of_comp_eq (p.app k) (t.app k) i (hfac k)
  · intro s
    exact hk s

end AlgebraicGeometry

end
