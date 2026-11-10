module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteFreeActionSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionSpaceQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientPresentationKernelPair

/-!
# The schematic locus of the quotient of an algebraic space by a free finite group action

Let `S` be a scheme, let `X` be an algebraic space over `S`, let `G` be a finite group acting
freely on `X` and let `Y = X/G` be the quotient of Tag 071S, the fppf sheafification of the
presheaf of pointwise orbits. Tag 0B87 says that a point of `Y` lies in the schematic locus
exactly when the whole fibre of `X` above it is contained in an affine open of `X`. This file
proves it, for an *arbitrary* algebraic space `X`: the quotient map `X ⟶ X/G` is surjective
and finite locally free, and Tag 0BA1 then gives the equivalence.

The geometric input is the pseudo-torsor structure of the quotient map. At a surjective étale
chart `φ : h_U ⟶ X` of `X`, the base change of `X ⟶ X/G` along the induced chart
`h_U ⟶ X/G` is the disjoint union `h_{∐_{g ∈ G} U}` of one copy of `U` for each group
element, the copy indexed by `g` sitting in `X` as the twisted chart `g • φ`. The projection
of that disjoint union onto `U` is the descent of the identities, hence finite locally free
because `G` is finite, and Tag 03ZW — finite local freeness is étale local on the target —
carries this back to the quotient map itself, representability included.

## Main results

* `AlgebraicGeometry.Space.exists_groupCopies`: the disjoint union of one copy of an object of
  the site for each element of a finite type is again an object of the site, and its fold map
  is surjective and finite locally free.
* `AlgebraicGeometry.Space.hom_ext_of_comp_fold_of_app` and
  `AlgebraicGeometry.Space.exists_comp_fold_eq_of_app_eq`: a point of the disjoint union of
  the copies of the chart is determined by its image in the chart together with its image in
  the space, and every such pair of images with the same image in the quotient arises.
* `AlgebraicGeometry.Space.isPullback_groupCopies`: the disjoint union of one copy of the
  chart for each group element is the fibre product `X ×_{X/G} h_U`.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_toOrbitQuotient` and
  `AlgebraicGeometry.Space.surjective_presheaf_toOrbitQuotient`: the quotient map `X ⟶ X/G`
  of a free action of a finite group on an algebraic space is finite locally free and
  surjective after every representable base change.
* `AlgebraicGeometry.Space.mem_schematicLocus_orbitQuotient_iff`: **Stacks 0B87**.

## Implementation notes

*Which notion of freeness.* The hypothesis is
`AlgebraicGeometry.Space.IsFreeOnNonemptyPoints`, the action being cancellative on the points
over the test objects whose underlying scheme is nonempty. This is the form in which the
library's Tag 071S — which is what produces the quotient used here — reads freeness; asking
cancellativity over *every* test object is unsatisfiable for a nontrivial group, since over a
test object with empty underlying scheme a sheaf is terminal, by
`AlgebraicGeometry.Space.forall_isCancelSMul_iff_subsingleton`.

*Why the comparison is only a fibre product after base change to the chart.* The presheaf of
pointwise orbits is not separated, so the group element relating two points of `X` with the
same image in `X/G` is only locally constant on the base
(`AlgebraicGeometry.Space.orbitSieve_mem`). The disjoint union of the copies of the chart is a
sheaf and absorbs exactly that locality: a point of it over a test object is a locally
constant choice of group element together with a point of the chart. Freeness enters as the
*injectivity* of the comparison, through
`AlgebraicGeometry.Space.smul_right_cancel_of_nonempty`, and over a test object with empty
underlying scheme there is nothing to prove, any two morphisms out of it being equal.

*Where finiteness of `G` is used.* Only for the fold map `∐_{g ∈ G} U ⟶ U` to be finite: it
is the descent of the identities, finite locally free by
`Stacks.Morphisms.isFiniteLocallyFree_sigmaDesc`. For an infinite group the fold map is still
étale and surjective but not finite, and Tag 0BA1 does not apply.

*The chart of the quotient.* Surjectivity of `h_U ⟶ X/G` after representable base change is
local surjectivity together with representability
(`AlgebraicGeometry.Space.presheaf_surjective_of_isLocallySurjective`), and étaleness is the
kernel-pair descent `AlgebraicGeometry.Space.etale_of_isKernelPair` applied to the relation
`∐_{g ∈ G} U ×_{φ, X, g • φ} U` of Tag 071S, whose source map is étale. Both are needed to
feed the chart into Tag 03ZW.

The case of an action on an object of the site, where the relation is the graph of the action
rather than the kernel pair of a chart, is
`AlgebraicGeometry.Space.mem_schematicLocus_actionQuotient_iff` of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteFreeActionSchematicLocus`.

## References

* [Stacks Project, Tag 0B87](https://stacks.math.columbia.edu/tag/0B87)
* [Stacks Project, Tag 0BA1](https://stacks.math.columbia.edu/tag/0BA1)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

/-! ### The disjoint union of one copy of a test object for each group element -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The disjoint union of one copy of an object of the site for each element of a finite
type is again an object of the site**, with its inclusions and the fold map onto that object.
The underlying scheme is the coproduct of the copies and the inclusions are its canonical
ones, so the fold map is the descent of the identities. -/
theorem exists_groupCopies (G : Type u) [Finite G] [Nonempty G] (U : BigFppfOver B S hS) :
    ∃ (W : BigFppfOver B S hS) (incl : G → (U ⟶ W)) (fold : W ⟶ U),
      (∀ g, AlgebraicGeometry.IsOpenImmersion
          ((BigFppfOver.toScheme B S hS).map (incl g))) ∧
        (∀ g g', g ≠ g' → ∀ (y y' : (BigFppfOver.toScheme B S hS).obj U),
          (BigFppfOver.toScheme B S hS).map (incl g) y ≠
            (BigFppfOver.toScheme B S hS).map (incl g') y') ∧
        (∀ z : (BigFppfOver.toScheme B S hS).obj W,
          ∃ g, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (incl g))) ∧
        (∀ g, incl g ≫ fold = 𝟙 U) ∧
        Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map fold) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map fold) := by
  classical
  set Y : G → Scheme.{u} := fun _ => (BigFppfOver.toScheme B S hS).obj U with hYdef
  have hZsize : (∐ Y).size < B.cutoff := by
    refine (schemeSize_coproduct_le Y ((BigFppfOver.toScheme B S hS).obj U).size
      (Scheme.aleph0_le_size _) ?_ fun _ => le_rfl).trans_lt U.left.property
    exact Cardinal.mk_le_aleph0.trans (Scheme.aleph0_le_size _)
  set τ : (∐ Y) ⟶ S := Sigma.desc fun _ => B.inclusion.map U.hom with hτdef
  set W : BigFppfOver B S hS := Over.mk (B.inclusion.preimage
    (X := B.obj hZsize) (Y := B.obj hS)
    (show B.inclusion.obj (B.obj hZsize) ⟶ B.inclusion.obj (B.obj hS) from τ)) with hWdef
  have hWhom : B.inclusion.map W.hom = τ := B.inclusion.map_preimage _
  have hincl : ∀ g, ∃ ψ : U ⟶ W, (BigFppfOver.toScheme B S hS).map ψ = Sigma.ι Y g := by
    intro g
    refine BigFppfOver.exists_hom_of_comp_eq B S hS (X := U) (Y := W) (Sigma.ι Y g) ?_
    rw [hWhom, hτdef, Sigma.ι_comp_desc]
  choose incl hinclmap using hincl
  have hfold : ∃ ψ : W ⟶ U, (BigFppfOver.toScheme B S hS).map ψ =
      Sigma.desc fun _ : G => 𝟙 ((BigFppfOver.toScheme B S hS).obj U) := by
    refine BigFppfOver.exists_hom_of_comp_eq B S hS (X := W) (Y := U)
      (Sigma.desc fun _ : G => 𝟙 ((BigFppfOver.toScheme B S hS).obj U)) ?_
    rw [hWhom, hτdef]
    refine Sigma.hom_ext _ _ fun g => ?_
    rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc, Category.id_comp]
  obtain ⟨fold, hfoldmap⟩ := hfold
  refine ⟨W, incl, fold, fun g => ?_, fun g g' hgg' y y' => ?_, fun z => ?_, fun g => ?_,
    ?_, ?_⟩
  · rw [hinclmap g]
    infer_instance
  · rw [hinclmap g, hinclmap g']
    intro hy
    exact hgg' (congrArg Sigma.fst ((sigmaι_eq_iff Y g g' y y').1 hy))
  · obtain ⟨g, hg⟩ :=
      ((Scheme.presieve₀_mem_precoverage_iff _).1 (sigmaOpenCover Y).mem₀).1 z
    exact ⟨g, by rwa [hinclmap g, ← sigmaOpenCover_f Y g]⟩
  · refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, hinclmap g, hfoldmap, Sigma.ι_comp_desc]
    exact ((BigFppfOver.toScheme B S hS).map_id U).symm
  · rw [hfoldmap]
    exact Stacks.Morphisms.isFiniteLocallyFree_sigmaDesc _
      fun _ => Stacks.Morphisms.isFiniteLocallyFree_id _
  · rw [hfoldmap]
    have _ : IsSplitEpi (Sigma.desc fun _ : G => 𝟙 ((BigFppfOver.toScheme B S hS).obj U)) :=
      ⟨⟨⟨Sigma.ι Y (Classical.arbitrary G), by rw [Sigma.ι_comp_desc]⟩⟩⟩
    exact surjective_of_isSplitEpi _

/-- A map out of a representable presheaf commutes with precomposition, by naturality. -/
private theorem app_comp_eq_map_app {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS} (j : yoneda.obj W ⟶ X)
    {T V : BigFppfOver B S hS} (k : T ⟶ V) (r : V ⟶ W) :
    j.app (Opposite.op T) (k ≫ r) = X.map k.op (j.app (Opposite.op V) r) :=
  NatTrans.naturality_apply j k.op r

/-- Every map from a representable presheaf to an algebraic space is representable. -/
private theorem relativelyRepresentable_of_isAlgebraicSpace {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X) : yoneda.relativelyRepresentable φ := by
  have hall : ∀ (V : BigFppfOver B S hS) (ξ : X.obj (Opposite.op V)),
      yoneda.relativelyRepresentable (yonedaEquiv.symm ξ) :=
    ((yoneda_relativelyRepresentable_diag_tfae_bigFppfOver B S hS X).out 1 2).mp
      hX.diagonal_representable
  simpa using hall U (yonedaEquiv φ)

/-! ### The chart of the quotient is split by the copies of the chart of the space -/

section Torsor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G : Type u} [Group G]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [∀ T, MulAction G (X.obj T)]
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hnat : IsNaturalAction B S hS G X) {U W : BigFppfOver B S hS}
    (φ : yoneda.obj U ⟶ X) (incl : G → (U ⟶ W)) (fold : W ⟶ U) (j : yoneda.obj W ⟶ X)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The value of the glued map on a point of the summand indexed by `g` is `g` times the value
of the chart. -/
theorem app_comp_incl_eq_smul (hj : ∀ g, yoneda.map (incl g) ≫ j = twistedChart hnat φ g)
    {T : BigFppfOver B S hS} (a : T ⟶ U) (g : G) :
    j.app (Opposite.op T) (a ≫ incl g) = g • φ.app (Opposite.op T) a := by
  simpa [twistedChart] using
    congrArg (fun η : yoneda.obj U ⟶ X => η.app (Opposite.op T) a) (hj g)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
include hnat in
/-- **A point of the disjoint union of the copies of the chart is determined by its image in
the chart together with its image in the space.** The test object is covered by the parts over
which the two given points lie in copies with given indices, and there freeness makes the two
indices agree. -/
theorem hom_ext_of_comp_fold_of_app
    (hfree : IsFreeOnNonemptyPoints B S hS G X)
    (hoi : ∀ g, AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (incl g)))
    (hcov : ∀ z : (BigFppfOver.toScheme B S hS).obj W,
      ∃ g, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (incl g)))
    (hfold : ∀ g, incl g ≫ fold = 𝟙 U)
    (hj : ∀ g, yoneda.map (incl g) ≫ j = twistedChart hnat φ g)
    {T : BigFppfOver B S hS} {r r' : T ⟶ W}
    (hr : r ≫ fold = r' ≫ fold)
    (hx : j.app (Opposite.op T) r = j.app (Opposite.op T) r') : r = r' := by
  classical
  have hoi' : ∀ (z : T ⟶ W) (g : G), AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (pullback.fst z (incl g))) :=
    fun z g => isOpenImmersion_pullbackFst _ _ (hoi g)
  have key : ∀ (Q : BigFppfOver B S hS) (m : Q ⟶ T) (a b : Q ⟶ U) (g g' : G),
      m ≫ r = a ≫ incl g → m ≫ r' = b ≫ incl g' → m ≫ r = m ≫ r' := by
    intro Q m a b g g' h₁ h₂
    have hab : a = b := by
      have h : a ≫ (incl g ≫ fold) = b ≫ (incl g' ≫ fold) := by
        rw [← Category.assoc, ← Category.assoc, ← h₁, ← h₂, Category.assoc, Category.assoc,
          hr]
      rwa [hfold, hfold, Category.comp_id, Category.comp_id] at h
    have hsmul : g • φ.app (Opposite.op Q) a = g' • φ.app (Opposite.op Q) b := by
      rw [← app_comp_incl_eq_smul hnat φ incl j hj a g,
        ← app_comp_incl_eq_smul hnat φ incl j hj b g', ← h₁, ← h₂,
        app_comp_eq_map_app, app_comp_eq_map_app, hx]
    rw [h₁, h₂, hab]
    by_cases hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj Q)
    · exact hom_ext_of_isEmpty hempty _ _
    · rw [hab] at hsmul
      rw [smul_right_cancel_of_nonempty B S hS G X hfree (not_isEmpty_iff.mp hempty) _ hsmul]
  refine BigFppfOver.hom_ext_of_openCover
    (W := fun p : G × G =>
      pullback (pullback.fst r (incl p.1)) (pullback.fst r' (incl p.2)))
    (fun p => pullback.fst _ _ ≫ pullback.fst r (incl p.1))
    (fun p => ?_) (fun z => ?_) (fun p => ?_)
  · rw [Functor.map_comp]
    have := hoi' r p.1
    have := isOpenImmersion_pullbackFst (pullback.fst r (incl p.1))
      (pullback.fst r' (incl p.2)) (hoi' r' p.2)
    infer_instance
  · obtain ⟨g, y, hy⟩ := hcov (((BigFppfOver.toScheme B S hS).map r).base z)
    obtain ⟨g', y', hy'⟩ := hcov (((BigFppfOver.toScheme B S hS).map r').base z)
    obtain ⟨w, hw⟩ := (mem_range_pullbackFst r (incl g) (hoi g) z).2 ⟨y, hy⟩
    obtain ⟨v, hv⟩ := (mem_range_pullbackFst (pullback.fst r (incl g))
      (pullback.fst r' (incl g')) (hoi' r' g') w).2 (by
        rw [hw]
        exact (mem_range_pullbackFst r' (incl g') (hoi g') z).2 ⟨y', hy'⟩)
    refine ⟨(g, g'), v, ?_⟩
    rw [Functor.map_comp]
    change ((BigFppfOver.toScheme B S hS).map (pullback.fst r (incl g))).base
      (((BigFppfOver.toScheme B S hS).map (pullback.fst _ _)).base v) = z
    rw [hv, hw]
  · obtain ⟨g, g'⟩ := p
    refine key _ _ (pullback.fst (pullback.fst r (incl g)) (pullback.fst r' (incl g')) ≫
        pullback.snd r (incl g))
      (pullback.snd (pullback.fst r (incl g)) (pullback.fst r' (incl g')) ≫
        pullback.snd r' (incl g')) g g' ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.condition]
    · rw [pullback.condition (f := pullback.fst r (incl g)) (g := pullback.fst r' (incl g')),
        Category.assoc, Category.assoc, pullback.condition]

include hnat in
/-- **The disjoint union of the copies of the chart surjects onto the fibre product of the
space with the chart over the quotient.** Two points of the space with the same image in the
quotient are translates of each other by a single group element locally on the base, and the
resulting local points of the disjoint union glue, being compatible by the previous result. -/
theorem exists_comp_fold_eq_of_app_eq
    (hfree : IsFreeOnNonemptyPoints B S hS G X)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hoi : ∀ g, AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (incl g)))
    (hcov : ∀ z : (BigFppfOver.toScheme B S hS).obj W,
      ∃ g, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (incl g)))
    (hfold : ∀ g, incl g ≫ fold = 𝟙 U)
    (hj : ∀ g, yoneda.map (incl g) ≫ j = twistedChart hnat φ g)
    {T : BigFppfOver B S hS} (x : X.obj (Opposite.op T)) (u : T ⟶ U)
    (hxu : (toOrbitQuotient B S hS G X hnat).app (Opposite.op T) x =
      (twistQuotientChart hnat φ).app (Opposite.op T) u) :
    ∃ r : T ⟶ W, j.app (Opposite.op T) r = x ∧ r ≫ fold = u := by
  classical
  have hq : (toOrbitQuotient B S hS G X hnat).app (Opposite.op T) x =
      (toOrbitQuotient B S hS G X hnat).app (Opposite.op T)
        (φ.app (Opposite.op T) u) := hxu
  have hsieve := orbitSieve_mem B S hS G X hnat x (φ.app (Opposite.op T) u) hq
  have hlocal : ∀ ⦃V : BigFppfOver B S hS⦄ (k : V ⟶ T),
      (orbitSieve B S hS G X hnat x (φ.app (Opposite.op T) u)).arrows k →
      ∃ ρ : V ⟶ W, j.app (Opposite.op V) ρ = X.map k.op x ∧ ρ ≫ fold = k ≫ u := by
    intro V k hk
    obtain ⟨g, hg⟩ := hk
    refine ⟨(k ≫ u) ≫ incl g, ?_, ?_⟩
    · rw [app_comp_incl_eq_smul hnat φ incl j hj (k ≫ u) g,
        app_comp_eq_map_app φ k u]
      exact hg
    · rw [Category.assoc, hfold g, Category.comp_id]
  choose ρ hρj hρfold using hlocal
  have hcompat : Presieve.FamilyOfElements.Compatible
      (P := yoneda.obj W)
      (R := (orbitSieve B S hS G X hnat x (φ.app (Opposite.op T) u)).arrows)
      (fun _ k hk => ρ k hk) := by
    intro V₁ V₂ Z k₁ k₂ f₁ f₂ h₁ h₂ hcomm
    refine hom_ext_of_comp_fold_of_app hnat φ incl fold j hfree hoi hcov hfold hj ?_ ?_
    · change (k₁ ≫ ρ f₁ h₁) ≫ fold = (k₂ ≫ ρ f₂ h₂) ≫ fold
      rw [Category.assoc, Category.assoc, hρfold f₁ h₁, hρfold f₂ h₂, ← Category.assoc,
        ← Category.assoc, hcomm]
    · change j.app (Opposite.op Z) (k₁ ≫ ρ f₁ h₁) = j.app (Opposite.op Z) (k₂ ≫ ρ f₂ h₂)
      rw [app_comp_eq_map_app, app_comp_eq_map_app, hρj f₁ h₁, hρj f₂ h₂,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← op_comp, ← op_comp, hcomm]
  obtain ⟨σ, hσ, -⟩ := (isSheaf_iff_isSheaf_of_type _ _).1
    (BigFppfOver.isSheaf_yoneda_obj B S hS W) _ hsieve (fun _ k hk => ρ k hk) hcompat
  refine ⟨σ, ?_, ?_⟩
  · refine ((isSheaf_iff_isSheaf_of_type _ _).1 hX _ hsieve).isSeparatedFor.ext ?_
    intro V k hk
    rw [← app_comp_eq_map_app, show k ≫ σ = ρ k hk from hσ k hk, hρj k hk]
  · refine (((isSheaf_iff_isSheaf_of_type _ _).1
      (BigFppfOver.isSheaf_yoneda_obj B S hS U) _ hsieve).isSeparatedFor).ext ?_
    intro V k hk
    change k ≫ σ ≫ fold = k ≫ u
    rw [← Category.assoc, show k ≫ σ = ρ k hk from hσ k hk, hρfold k hk]

include hnat in
/-- **The two maps out of the disjoint union of the copies of the chart agree after the
quotient map.** On the copy indexed by `g` they differ by `g` in the space, and the quotient
map is invariant; the copies cover the disjoint union and the quotient is a sheaf. -/
theorem comp_toOrbitQuotient_eq
    (hoi : ∀ g, AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (incl g)))
    (hcov : ∀ z : (BigFppfOver.toScheme B S hS).obj W,
      ∃ g, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (incl g)))
    (hfold : ∀ g, incl g ≫ fold = 𝟙 U)
    (hj : ∀ g, yoneda.map (incl g) ≫ j = twistedChart hnat φ g) :
    j ≫ toOrbitQuotient B S hS G X hnat =
      yoneda.map fold ≫ twistQuotientChart hnat φ := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  refine (((isSheaf_iff_isSheaf_of_type _ _).1 (orbitQuotientSheaf B S hS G X hnat).property _
    (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS incl hoi
      hcov)).isSeparatedFor).ext ?_
  rintro V e ⟨Z, l, e', ⟨g⟩, hcomp⟩
  have he : e = l ≫ incl g := hcomp.symm
  have h₁ : (orbitQuotientSheaf B S hS G X hnat).obj.map e.op
      ((toOrbitQuotient B S hS G X hnat).app (Opposite.op W) (yonedaEquiv j)) =
      (toOrbitQuotient B S hS G X hnat).app (Opposite.op V)
        (X.map e.op (yonedaEquiv j)) :=
    (NatTrans.naturality_apply (toOrbitQuotient B S hS G X hnat) e.op (yonedaEquiv j)).symm
  have h₂ : X.map e.op (yonedaEquiv j) = j.app (Opposite.op V) e := by
    simpa [yonedaEquiv] using (NatTrans.naturality_apply j e.op (𝟙 W)).symm
  have h₃ : (orbitQuotientSheaf B S hS G X hnat).obj.map e.op
      ((twistQuotientChart hnat φ).app (Opposite.op W) fold) =
      (twistQuotientChart hnat φ).app (Opposite.op V) (e ≫ fold) :=
    (NatTrans.naturality_apply (twistQuotientChart hnat φ) e.op fold).symm
  rw [h₁, h₂, h₃, he, Category.assoc, hfold g, Category.comp_id,
    app_comp_incl_eq_smul hnat φ incl j hj l g]
  change (toOrbitQuotient B S hS G X hnat).app (Opposite.op V)
      (g • φ.app (Opposite.op V) l) =
    (toOrbitQuotient B S hS G X hnat).app (Opposite.op V) (φ.app (Opposite.op V) l)
  exact toOrbitQuotient_smul B S hS G X hnat g _

include hnat in
/-- **The disjoint union of one copy of the chart for each group element is the fibre product
of the space with the chart over the quotient.** This is the statement that the quotient map
`X ⟶ X/G` is a pseudo-torsor under the constant group `G`, pulled back to the chart, where it
becomes split. -/
theorem isPullback_groupCopies
    (hfree : IsFreeOnNonemptyPoints B S hS G X)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hoi : ∀ g, AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (incl g)))
    (hcov : ∀ z : (BigFppfOver.toScheme B S hS).obj W,
      ∃ g, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (incl g)))
    (hfold : ∀ g, incl g ≫ fold = 𝟙 U)
    (hj : ∀ g, yoneda.map (incl g) ≫ j = twistedChart hnat φ g) :
    IsPullback j (yoneda.map fold) (toOrbitQuotient B S hS G X hnat)
      (twistQuotientChart hnat φ) := by
  classical
  have hw := comp_toOrbitQuotient_eq hnat φ incl fold j hoi hcov hfold hj
  refine IsPullback.of_forall_isPullback_app fun Top => ?_
  obtain ⟨T⟩ := Top
  refine (Limits.Types.isPullback_iff _ _ _ _).2
    ⟨NatTrans.congr_app hw (Opposite.op T), fun r r' hrr' =>
      hom_ext_of_comp_fold_of_app hnat φ incl fold j hfree hoi hcov hfold hj
        hrr'.2 hrr'.1, fun x u hxu => ?_⟩
  exact exists_comp_fold_eq_of_app_eq hnat φ incl fold j hfree hX hoi hcov hfold hj x u hxu

end Torsor

/-! ### The quotient map is surjective and finite locally free -/

section Quotient

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G : Type u} [Group G] [Finite G]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [∀ T, MulAction G (X.obj T)]
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_FreeActionSpaceSchematicLocus
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The quotient map of a free action of a finite group on an algebraic space is finite
locally free after every representable base change.**

At a surjective étale chart `φ : U ⟶ X` the base change of `X ⟶ X/G` along the induced chart
`h_U ⟶ X/G` is the disjoint union of one copy of `U` for each group element, whose projection
to `U` is the descent of the identities, so Stacks 03ZW applies. -/
theorem isFiniteLocallyFree_presheaf_toOrbitQuotient
    (hnat : IsNaturalAction B S hS G X) (hX : IsAlgebraicSpace B S hS X)
    (hfree : IsFreeOnNonemptyPoints B S hS G X) :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (toOrbitQuotient B S hS G X hnat) := by
  classical
  obtain ⟨U, φ, hsurj, hetale⟩ := hX.exists_atlas
  have hrep := relativelyRepresentable_of_isAlgebraicSpace hX φ
  have hY : IsAlgebraicSpace B S hS (orbitQuotientSheaf B S hS G X hnat).obj :=
    isAlgebraicSpace_orbitQuotientSheaf_of_isFreeOnNonemptyPoints hnat hX hfree
  have hcrep := relativelyRepresentable_of_isAlgebraicSpace hY (twistQuotientChart hnat φ)
  have h₁ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) φ :=
    isLocallySurjective_of_surjective_etale B S hS φ hsurj hetale
  have h₂ := isLocallySurjective_toOrbitQuotient B S hS G X hnat
  have hcloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (twistQuotientChart hnat φ) :=
    Presheaf.isLocallySurjective_comp (BigFppfOver.topology B S hS) φ
      (toOrbitQuotient B S hS G X hnat)
  have hcsurj := presheaf_surjective_of_isLocallySurjective B S hS hcrep hcloc
  have hcetale := etale_of_isKernelPair B S hS (twistQuotientChart hnat φ)
    (isPullback_twistRelation hnat φ hrep hfree) hcloc hcrep
    (etale_twistRelationSource hnat φ hrep hfree hetale)
  obtain ⟨W, incl, fold, hoi, hdisj, hcov, hfold, hflf, -⟩ :=
    exists_groupCopies B S hS G U
  obtain ⟨ξ, hξ⟩ := BigFppfOver.exists_section_of_disjoint_openCover
    (H := X) ((isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf) incl hoi hdisj hcov
    (fun g => yonedaEquiv (twistedChart hnat φ g))
  have hj : ∀ g : G, yoneda.map (incl g) ≫ yonedaEquiv.symm ξ = twistedChart hnat φ g :=
    fun g => yonedaEquiv.injective <| by
      rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
      exact hξ g
  have hsq := isPullback_groupCopies hnat φ incl fold (yonedaEquiv.symm ξ) hfree hX.isSheaf
    hoi hcov hfold hj
  refine (isFiniteLocallyFree_presheaf_iff_exists_etaleChart B S hS hX hY
    (toOrbitQuotient B S hS G X hnat)).2 ⟨U, twistQuotientChart hnat φ, hcsurj, hcetale, ?_⟩
  have hyon : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map fold) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ fold).2 hflf
  have hid : ((IsPullback.of_hasPullback (toOrbitQuotient B S hS G X hnat)
        (twistQuotientChart hnat φ)).isoIsPullback _ _ hsq).hom ≫ yoneda.map fold =
      pullback.snd (toOrbitQuotient B S hS G X hnat) (twistQuotientChart hnat φ) :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  rw [← hid]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 hyon

/-- **The quotient map of a free action of a finite group on an algebraic space is surjective
after every representable base change.** It is a surjection of fppf sheaves, and it is
representable by the previous result. -/
theorem surjective_presheaf_toOrbitQuotient
    (hnat : IsNaturalAction B S hS G X) (hX : IsAlgebraicSpace B S hS X)
    (hfree : IsFreeOnNonemptyPoints B S hS G X) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (toOrbitQuotient B S hS G X hnat) :=
  presheaf_surjective_of_isLocallySurjective B S hS
    (isFiniteLocallyFree_presheaf_toOrbitQuotient hnat hX hfree).rep
    (isLocallySurjective_toOrbitQuotient B S hS G X hnat)

/-! ### Stacks 0B87 -/

/-- **Stacks 0B87.** Let `S` be a scheme, let `X` be an algebraic space over `S`, let `G` be a
finite group acting freely on `X` and let `Y = X/G` be the quotient of Tag 071S. For a point
`y` of `Y` the following are equivalent:

1. `y` lies in the schematic locus of `Y` — the point set of
   `AlgebraicGeometry.Space.schematicLocus`, the largest open subspace of `Y` which is a
   scheme (Tag 03JH); and
2. there is an affine open subspace of `X`, presented as an open immersion `i : h_V ⟶ X` from
   an affine object `V` of the site, whose point set contains the whole fibre of `y`.

The quotient map `X ⟶ X/G` is surjective and finite locally free after every representable
base change, so this is Stacks 0BA1 for it. Freeness is read on the points over the test
objects with nonempty underlying scheme, which is how the library's form of Tag 071S — the form
producing the quotient here — reads it. -/
@[stacks 0B87]
theorem mem_schematicLocus_orbitQuotient_iff
    (hnat : IsNaturalAction B S hS G X) (hX : IsAlgebraicSpace B S hS X)
    (hfree : IsFreeOnNonemptyPoints B S hS G X)
    (y : points B S hS (orbitQuotientSheaf B S hS G X hnat).obj) :
    y ∈ Set.range (pointsMap B S hS
        (schematicLocus B S hS (orbitQuotientSheaf B S hS G X hnat).obj).toFunctor
        (schematicLocus B S hS (orbitQuotientSheaf B S hS G X hnat).obj).ι) ↔
      ∃ (V : BigFppfOver B S hS) (i : yoneda.obj V ⟶ X),
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ IsOpenImmersion B S hS i ∧
        ∀ x : points B S hS X,
          pointsMap B S hS X (toOrbitQuotient B S hS G X hnat) x = y →
            x ∈ Set.range (pointsMap B S hS (yoneda.obj V) i) :=
  mem_range_pointsMap_schematicLocus_iff_exists_isAffine_isOpenImmersion B S hS
    (X := ⟨X, hX⟩)
    (Y := ⟨(orbitQuotientSheaf B S hS G X hnat).obj,
      isAlgebraicSpace_orbitQuotientSheaf_of_isFreeOnNonemptyPoints hnat hX hfree⟩)
    (ObjectProperty.homMk (toOrbitQuotient B S hS G X hnat))
    (surjective_presheaf_toOrbitQuotient hnat hX hfree)
    (isFiniteLocallyFree_presheaf_toOrbitQuotient hnat hX hfree) y

end Quotient

end AlgebraicGeometry.Space

end
