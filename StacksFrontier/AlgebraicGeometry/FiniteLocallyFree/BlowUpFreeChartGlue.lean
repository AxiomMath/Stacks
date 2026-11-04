module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueRestrictIso
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleRestrictChart
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction

/-!
# Glueing a sheaf of modules on a scheme from two opens

Two sheaves of modules given on two opens covering a scheme, together with an identification of
their restrictions to the overlap, come from a sheaf of modules on the scheme.  This is
[Stacks, Tag 00AM] for a **two**-member covering, in the shape the Zariski glueing of the
essential surjectivity half of [Stacks, Tag 0EXD] consumes: there the base `Spec A` is covered by
an open `U` containing the centre, over whose preimage the bundle on the modification is free, and
by the complement of the centre, over which the modification maps isomorphically.

`AlgebraicGeometry.RestrictIsoGlueData` is the shape of [Stacks, Tag 00AM] whose cocycle condition
is an equality of morphisms **over a single open** -- not over a triple overlap -- so for two
charts every instance of it is either formal or one of two mutually inverse comparisons.  What
remains is its `iso_restrict` field, the compatibility of the comparisons with shrinking the open,
and that is supplied once and for all by `AlgebraicGeometry.restrictMiddleIso`: a comparison of the
two chart modules *through a module on the overlap* restricts to the comparison through that same
module, by `AlgebraicGeometry.openLiftShrinkIso_restrictMiddleIso`.  So the whole glueing datum is
determined by two isomorphisms `σ i` of the restrictions of the two chart modules to the overlap
with one module `L` there, and no cocycle is asked of the caller at all.

## Main definitions

* `AlgebraicGeometry.middleChartIso`: **the comparison of two charts over an open inside both,
  through a module on a middle chart**, ascribed at the spelling the `iso` field of
  `AlgebraicGeometry.RestrictIsoGlueData` asks for -- a comparison of the restrictions to that
  open of the two pushforwards.
* `AlgebraicGeometry.TwoOpensGlue.opn`, `...mdl`, `...mid`: the two opens of the covering, the two
  modules, and the inclusion of the overlap into each open, as families indexed by `ULift Bool`,
  which is the form `AlgebraicGeometry.RestrictIsoGlueData` indexes its charts by.
* `AlgebraicGeometry.TwoOpensGlue.transIso`: the transition isomorphisms of the datum -- the
  identity on the diagonal and `AlgebraicGeometry.middleChartIso` off it.
* `AlgebraicGeometry.TwoOpensGlue.glueData`: **the glueing datum itself.**

## Main results

* `AlgebraicGeometry.restrictLocal_middleChartIso`: **the comparison through a middle chart is
  compatible with shrinking the open**, which is the `iso_restrict` field.
* `AlgebraicGeometry.middleChartIso_hom_comp_hom` and
  `AlgebraicGeometry.middleChartIso_hom_comp_hom_trans`: **the comparison through a middle chart
  is self-inverse in its two charts, and transitive in three**, which is the `iso_trans` field.
* `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_fac`: **a morphism of sheaves of
  modules invertible over one chart is invertible over any chart factoring through it.** This is
  `AlgebraicGeometry.isIso_restrictFunctor_map_of_le` with the two inclusions of opens replaced by
  an arbitrary factorisation of open immersions, which is what the comparison over the overlap
  needs: the overlap maps to the modification through a section of it, not through an open of the
  base.
* `AlgebraicGeometry.TwoOpensGlue.exists_restrict_iso_of_middle`: **two sheaves of modules on two
  opens covering a scheme, identified over the overlap through a module there, come from a sheaf
  of modules on the scheme**, restricting to each of them.

## Implementation notes

The index type is `ULift Bool` rather than `Fin 2` so that the two charts can be named by `false`
and `true` and the four cases of a transition and the eight of a cocycle are discharged by a
`match` whose arms reduce by `rfl`.  The family of opens is a non-dependent function
`ULift Bool → S.Opens`, so the family of chart *schemes* `fun i => (opn U₁ U₂ i).toScheme` needs
no dependent pattern match; only the family of modules does.

The two comparisons `σ` are stated at `AlgebraicGeometry.TwoOpensGlue.mdl ... i` rather than at the
two modules separately: writing `Scheme.Modules.restrict M₁ (mid U₁ U₂ ⟨false⟩)` makes Lean unify
the target of `mid` with `U₁.toScheme` while the instance `IsOpenImmersion (mid ...)` is still
being synthesised, and the synthesis then fails on a metavariable.  At the `mdl` spelling the
scheme is syntactically the one `mid` lands in and no unification is needed.

The fields of `AlgebraicGeometry.RestrictIsoGlueData` are supplied as `fun i j {W} hi hj => ...`
with the open bound explicitly: a `fun` matches its binders against *all* the binders of the
expected type, implicit ones included, so `fun i j hi hj => ...` binds `hi` to the open.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Invertibility over a chart that factors through another -/

/-- **A morphism of sheaves of modules invertible over one chart is invertible over any chart
factoring through it.** Restriction along the factoring chart is, by
`AlgebraicGeometry.restrictCompIso`, the iterated restriction, and a functor carries isomorphisms
to isomorphisms.

The two charts are arbitrary open immersions rather than inclusions of opens, which is what the
comparison over an overlap needs: there the overlap maps to the modification through a section of
it, not through an open of the base. -/
theorem Scheme.Modules.isIso_restrictFunctor_map_of_fac {Y Z W : Scheme.{u}} {M N : Y.Modules}
    (φ : M ⟶ N) (g : Z ⟶ Y) [IsOpenImmersion g] (h : W ⟶ Z) [IsOpenImmersion h] {k : W ⟶ Y}
    (hk : h ≫ g = k) [IsOpenImmersion k]
    (hφ : IsIso ((Scheme.Modules.restrictFunctor g).map φ)) :
    IsIso ((Scheme.Modules.restrictFunctor k).map φ) := by
  have hiso : IsIso ((Scheme.Modules.restrictFunctor h).map
      ((Scheme.Modules.restrictFunctor g).map φ)) :=
    have := hφ
    inferInstanceAs (IsIso ((Scheme.Modules.restrictFunctor h).map
      ((Scheme.Modules.restrictFunctor g).map φ)))
  have heq : (Scheme.Modules.restrictFunctor k).map φ =
      (restrictCompIso h g hk M).hom ≫
        (Scheme.Modules.restrictFunctor h).map ((Scheme.Modules.restrictFunctor g).map φ) ≫
          (restrictCompIso h g hk N).inv := by
    rw [← Category.assoc, ← restrictCompIso_naturality h g hk φ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [heq]
  have := hiso
  infer_instance

/-! ### The two generic steps, for arbitrary charts -/

section Middle

variable {S A B T : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S) (t : T ⟶ S)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion t]
  {pa : T ⟶ A} {pb : T ⟶ B} [IsOpenImmersion pa] [IsOpenImmersion pb]
  (hpa : pa ≫ a = t) (hpb : pb ≫ b = t)
  {M : A.Modules} {N : B.Modules} {L : T.Modules}
  (σa : Scheme.Modules.restrict M pa ≅ L) (σb : Scheme.Modules.restrict N pb ≅ L)

/-- **The chart comparison of two charts through a middle chart**, in the shape of the `iso`
field of `AlgebraicGeometry.RestrictIsoGlueData`. -/
def middleChartIso {W : S.Opens} (hW : W ≤ t.opensRange) (ha : W ≤ a.opensRange)
    (hb : W ≤ b.opensRange) :
    Scheme.Modules.restrict ((Scheme.Modules.pushforward a).obj M) W.ι ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward b).obj N) W.ι :=
  restrictPushforwardIsoOfRestrictIso a b M N ha hb
    (restrictMiddleIso a b t hpa hpb σa σb hW ha hb)

/-- **The `iso_restrict` field for `AlgebraicGeometry.middleChartIso`.** -/
theorem restrictLocal_middleChartIso {W W' : S.Opens} (hW : W ≤ t.opensRange)
    (ha : W ≤ a.opensRange) (hb : W ≤ b.opensRange) (hW' : W' ≤ W) :
    restrictLocal (middleChartIso a b t hpa hpb σa σb hW ha hb).hom hW' =
      (middleChartIso a b t hpa hpb σa σb (hW'.trans hW) (hW'.trans ha) (hW'.trans hb)).hom := by
  rw [middleChartIso, restrictLocal_restrictPushforwardIsoOfRestrictIso,
    openLiftShrinkIso_restrictMiddleIso, middleChartIso]

/-- **The comparison through a middle chart is self-inverse in its two charts.** This is the
`iso_trans` field of `AlgebraicGeometry.RestrictIsoGlueData` in the one case that is not formal:
the comparison from the first chart to the second followed by the comparison back is the
identity. -/
theorem middleChartIso_hom_comp_hom {W : S.Opens} (hW : W ≤ t.opensRange)
    (ha : W ≤ a.opensRange) (hb : W ≤ b.opensRange) :
    (middleChartIso a b t hpa hpb σa σb hW ha hb).hom ≫
        (middleChartIso b a t hpb hpa σb σa hW hb ha).hom = 𝟙 _ := by
  simp only [middleChartIso, restrictPushforwardIsoOfRestrictIso, restrictMiddleIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id]

/-- **The comparison through a middle chart is transitive in the three charts.** -/
theorem middleChartIso_hom_comp_hom_trans {C : Scheme.{u}} (c : C ⟶ S) [IsOpenImmersion c]
    {pc : T ⟶ C} [IsOpenImmersion pc] (hpc : pc ≫ c = t) {P : C.Modules}
    (σc : Scheme.Modules.restrict P pc ≅ L) {W : S.Opens} (hW : W ≤ t.opensRange)
    (ha : W ≤ a.opensRange) (hb : W ≤ b.opensRange) (hc : W ≤ c.opensRange) :
    (middleChartIso a b t hpa hpb σa σb hW ha hb).hom ≫
        (middleChartIso b c t hpb hpc σb σc hW hb hc).hom =
      (middleChartIso a c t hpa hpc σa σc hW ha hc).hom := by
  simp only [middleChartIso, restrictPushforwardIsoOfRestrictIso, restrictMiddleIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

end Middle

namespace TwoOpensGlue

variable {S : Scheme.{u}} (U₁ U₂ : S.Opens)

/-! ### The two-element family of opens -/

/-- The two opens of the glueing, indexed by a two-element type. -/
def opn : ULift.{u} Bool → S.Opens
  | ⟨false⟩ => U₁
  | ⟨true⟩ => U₂

/-- The open indexed by `false` is `U₁`. -/
@[simp] lemma opn_false : opn U₁ U₂ ⟨false⟩ = U₁ := rfl

/-- The open indexed by `true` is `U₂`. -/
@[simp] lemma opn_true : opn U₁ U₂ ⟨true⟩ = U₂ := rfl

/-- The overlap `U₁ ⊓ U₂` is contained in each of the two opens. -/
lemma inf_le_opn : ∀ i, U₁ ⊓ U₂ ≤ opn U₁ U₂ i
  | ⟨false⟩ => inf_le_left
  | ⟨true⟩ => inf_le_right

/-- The overlap `U₁ ⊓ U₂` is contained in the range of the inclusion of each of the two opens. -/
lemma inf_le_opensRange_opn (i : ULift.{u} Bool) :
    U₁ ⊓ U₂ ≤ (opn U₁ U₂ i).ι.opensRange := by
  rw [Scheme.Opens.opensRange_ι]
  exact inf_le_opn U₁ U₂ i

/-- If `U₁ ⊔ U₂ = ⊤`, the ranges of the inclusions of the two opens cover the scheme. -/
lemma iSup_opensRange_opn (h : U₁ ⊔ U₂ = ⊤) :
    ⨆ i, ((opn U₁ U₂ i).ι).opensRange = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← h]
  exact sup_le (le_iSup_of_le ⟨false⟩ (Scheme.Opens.opensRange_ι _).ge)
    (le_iSup_of_le ⟨true⟩ (Scheme.Opens.opensRange_ι _).ge)

/-- The inclusion of the overlap into the `i`-th open, as the canonical factorisation. -/
def mid (i : ULift.{u} Bool) : (U₁ ⊓ U₂).toScheme ⟶ (opn U₁ U₂ i).toScheme :=
  openLift (opn U₁ U₂ i).ι (inf_le_opensRange_opn U₁ U₂ i)

/-- The inclusion of the overlap into each of the two opens is an open immersion. -/
instance isOpenImmersion_mid (i : ULift.{u} Bool) : IsOpenImmersion (mid U₁ U₂ i) :=
  inferInstanceAs
    (IsOpenImmersion (openLift (opn U₁ U₂ i).ι (inf_le_opensRange_opn U₁ U₂ i)))

/-- The inclusion of the overlap into the `i`-th open, followed by the inclusion of that open,
is the inclusion of the overlap. -/
@[simp] lemma mid_comp (i : ULift.{u} Bool) :
    mid U₁ U₂ i ≫ (opn U₁ U₂ i).ι = (U₁ ⊓ U₂).ι :=
  openLift_comp _ _

/-- An open contained in the ranges of the inclusions of two distinct opens of the family is
contained in the range of the inclusion of the overlap. -/
lemma le_opensRange_inf (i j : ULift.{u} Bool) {W : S.Opens}
    (hi : W ≤ (opn U₁ U₂ i).ι.opensRange) (hj : W ≤ (opn U₁ U₂ j).ι.opensRange) (hne : i ≠ j) :
    W ≤ ((U₁ ⊓ U₂).ι).opensRange := by
  rw [Scheme.Opens.opensRange_ι] at hi hj ⊢
  match i, j with
  | ⟨false⟩, ⟨false⟩ => exact absurd rfl hne
  | ⟨true⟩, ⟨true⟩ => exact absurd rfl hne
  | ⟨false⟩, ⟨true⟩ => exact le_inf hi hj
  | ⟨true⟩, ⟨false⟩ => exact le_inf hj hi

/-! ### The two-element family of modules and of comparisons -/

variable (M₁ : U₁.toScheme.Modules) (M₂ : U₂.toScheme.Modules)

/-- The two modules of the glueing. -/
def mdl : ∀ i, (opn U₁ U₂ i).toScheme.Modules
  | ⟨false⟩ => M₁
  | ⟨true⟩ => M₂

/-- The module indexed by `false` is `M₁`. -/
@[simp] lemma mdl_false : mdl U₁ U₂ M₁ M₂ ⟨false⟩ = M₁ := rfl

/-- The module indexed by `true` is `M₂`. -/
@[simp] lemma mdl_true : mdl U₁ U₂ M₁ M₂ ⟨true⟩ = M₂ := rfl

variable {L : (U₁ ⊓ U₂).toScheme.Modules}
  (σ : ∀ i, Scheme.Modules.restrict (mdl U₁ U₂ M₁ M₂ i) (mid U₁ U₂ i) ≅ L)

/-! ### The transition isomorphisms -/

/-- The two indices `⟨false⟩` and `⟨true⟩` of `ULift Bool` are distinct. -/
lemma ne_false_true : (⟨false⟩ : ULift.{u} Bool) ≠ ⟨true⟩ := fun h => by
  simpa using congrArg ULift.down h

/-- The two indices `⟨true⟩` and `⟨false⟩` of `ULift Bool` are distinct. -/
lemma ne_true_false : (⟨true⟩ : ULift.{u} Bool) ≠ ⟨false⟩ := ne_false_true.symm

/-- **The comparison of the two charts over an open contained in both.** On the diagonal it is
the identity; off the diagonal it is the comparison through the overlap. -/
def transIso : ∀ (i j : ULift.{u} Bool) {W : S.Opens},
    W ≤ ((opn U₁ U₂ i).ι).opensRange → W ≤ ((opn U₁ U₂ j).ι).opensRange →
    (Scheme.Modules.restrict ((Scheme.Modules.pushforward (opn U₁ U₂ i).ι).obj
        (mdl U₁ U₂ M₁ M₂ i)) W.ι ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward (opn U₁ U₂ j).ι).obj
        (mdl U₁ U₂ M₁ M₂ j)) W.ι)
  | ⟨false⟩, ⟨false⟩ => fun _ _ => Iso.refl _
  | ⟨true⟩, ⟨true⟩ => fun _ _ => Iso.refl _
  | ⟨false⟩, ⟨true⟩ => fun hi hj =>
      middleChartIso _ _ (U₁ ⊓ U₂).ι (mid_comp U₁ U₂ ⟨false⟩) (mid_comp U₁ U₂ ⟨true⟩)
        (σ ⟨false⟩) (σ ⟨true⟩)
        (le_opensRange_inf U₁ U₂ ⟨false⟩ ⟨true⟩ hi hj ne_false_true) hi hj
  | ⟨true⟩, ⟨false⟩ => fun hi hj =>
      middleChartIso _ _ (U₁ ⊓ U₂).ι (mid_comp U₁ U₂ ⟨true⟩) (mid_comp U₁ U₂ ⟨false⟩)
        (σ ⟨true⟩) (σ ⟨false⟩)
        (le_opensRange_inf U₁ U₂ ⟨true⟩ ⟨false⟩ hi hj ne_true_false) hi hj

/-- Restricting the comparison `transIso` over `W` to a smaller open `W'` gives the comparison
over `W'`. -/
theorem restrictLocal_transIso (i j : ULift.{u} Bool) {W W' : S.Opens}
    (hi : W ≤ ((opn U₁ U₂ i).ι).opensRange) (hj : W ≤ ((opn U₁ U₂ j).ι).opensRange)
    (hW' : W' ≤ W) :
    restrictLocal (transIso U₁ U₂ M₁ M₂ σ i j hi hj).hom hW' =
      (transIso U₁ U₂ M₁ M₂ σ i j (hW'.trans hi) (hW'.trans hj)).hom := by
  rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩ <;>
    simp only [transIso, Iso.refl_hom, restrictLocal_id, restrictLocal_middleChartIso]

/-- The comparisons `transIso` satisfy the cocycle condition: the comparison from the `i`-th
chart to the `j`-th followed by that from the `j`-th to the `k`-th is the comparison from the
`i`-th to the `k`-th. -/
theorem transIso_hom_comp_hom (i j k : ULift.{u} Bool) {W : S.Opens}
    (hi : W ≤ ((opn U₁ U₂ i).ι).opensRange) (hj : W ≤ ((opn U₁ U₂ j).ι).opensRange)
    (hk : W ≤ ((opn U₁ U₂ k).ι).opensRange) :
    (transIso U₁ U₂ M₁ M₂ σ i j hi hj).hom ≫ (transIso U₁ U₂ M₁ M₂ σ j k hj hk).hom =
      (transIso U₁ U₂ M₁ M₂ σ i k hi hk).hom := by
  rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩ <;> rcases k with ⟨_ | _⟩ <;>
    simp only [transIso, Iso.refl_hom, Category.id_comp, Category.comp_id,
      middleChartIso_hom_comp_hom]


/-- **The glueing datum of two sheaves of modules on two opens covering the base, compared
through a module on their overlap.** -/
def glueData : RestrictIsoGlueData S (fun i => (opn U₁ U₂ i).ι) where
  mod := mdl U₁ U₂ M₁ M₂
  iso := fun i j {_W} hi hj => transIso U₁ U₂ M₁ M₂ σ i j hi hj
  iso_restrict := fun i j {_W _W'} hi hj hW' =>
    restrictLocal_transIso U₁ U₂ M₁ M₂ σ i j hi hj hW'
  iso_trans := fun i j k {_W} hi hj hk => transIso_hom_comp_hom U₁ U₂ M₁ M₂ σ i j k hi hj hk

include σ in
/-- **Two sheaves of modules on two opens covering a scheme, identified over the overlap through
a module there, come from a sheaf of modules on the scheme.** -/
theorem exists_restrict_iso_of_middle :
    ∃ K : S.Modules, Nonempty (Scheme.Modules.restrict K U₁.ι ≅ M₁) ∧
      Nonempty (Scheme.Modules.restrict K U₂.ι ≅ M₂) :=
  ⟨(glueData U₁ U₂ M₁ M₂ σ).glued,
    ⟨(glueData U₁ U₂ M₁ M₂ σ).chartIso ⟨false⟩⟩,
    ⟨(glueData U₁ U₂ M₁ M₂ σ).chartIso ⟨true⟩⟩⟩

end TwoOpensGlue

end AlgebraicGeometry

end
