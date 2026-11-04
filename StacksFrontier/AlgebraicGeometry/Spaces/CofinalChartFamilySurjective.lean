module

public import StacksFrontier.AlgebraicGeometry.Spaces.CofinalChartGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.CofinalChartTwoIsoGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.CategoryTheory.Sites.JointlyLocallySurjective

/-!
# A cofinal class of charts from a surjection onto the final sheaf

Let `F` be a presheaf on the big fppf site of a scheme `S` and let `G i`, for `i` in an index
type, be sheaves on the small étale site of `F`.  Call an affine étale chart of `F` *selected*
when one of the `G i` has a section over it.  This file proves that the selected charts are
cofinal among the affine étale charts of `F` — `AlgebraicGeometry.Space.IsCofinalChartFamily` —
as soon as the morphism `∐ᵢ Gᵢ ⟶ *` onto the final sheaf of the small étale site is a surjection
of sheaves.

This is the "surjectivity to local sections" step in the proof of [Stacks Project, Tag 04KL]: the
`G i` there are the sheaves `g⁻¹h_{V_i}` for an affine étale cover `V i` of the target, a section
of `g⁻¹h_{V_i}` over a chart is what the recovery theorem is applied to, and only a *cover* of a
given chart admits such a section, because the surjectivity of `∐ᵢ g⁻¹h_{V_i} ⟶ *` is local.  The
gluing statements that consume the cofinality are
`AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso_of_cofinal` and
`AlgebraicGeometry.Space.inducesSmallEtaleRingedToposHom_of_cofinal`.

The hypothesis is *supplied* in
`StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartFamilyInverseImage.lean`: for `G i` the inverse
images under a morphism of topoi of the sheaves represented by a family of étale charts of the
target covering its final object, both the surjectivity and the cofinality are proved there.
Note that the coproduct-free form
`AlgebraicGeometry.Space.isCofinalChartFamily_hasSomeChartSection` is what the general case needs:
`HasCoproduct G` constrains the index universe, and the cover of affine étale charts that
`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts` produces is indexed by a
`Type (u + 1)`, for which no coproduct of `Type u`-valued sheaves exists.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.HasSomeSection` — one of the `G i` has a section over an
  object of the small étale site.
* `AlgebraicGeometry.Space.HasSomeChartSection` — the resulting class of charts of `F`: a chart
  is selected when it is étale and one of the `G i` has a section over it.

## Main results

* `AlgebraicGeometry.Space.isCofinalChartFamily_hasSomeChartSection` — the selected charts are
  cofinal, given that every object of the small étale site is covered by objects over which some
  `G i` has a section.
* `AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_sigmaDesc` — the same from
  the surjectivity of `∐ᵢ Gᵢ ⟶ *` onto the final sheaf, which is the form the proof of
  [Stacks Project, Tag 04KL] produces.
* `AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_finalSheaf` — the same
  with the final sheaf spelled as the constant sheaf `PUnit`.
* `AlgebraicGeometry.Space.isCofinalChartFamily_hasSomeChartSection_terminal` — the one-member
  family consisting of the final sheaf selects every affine étale chart and is cofinal, so
  neither the hypothesis nor the selected class is empty.
* `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso_of_isLocallySurjective_sigmaDesc` and
  `AlgebraicGeometry.Space.inducesSmallEtaleRingedToposHom_of_isLocallySurjective_sigmaDesc` —
  the two gluing statements of
  `StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartGluing.lean` and
  `StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartTwoIsoGluing.lean` with their cofinality
  hypothesis discharged by the surjectivity.

## Implementation notes

### Why the two topologies both occur

`AlgebraicGeometry.Space.IsCofinalChartFamily` asks for a covering family of the **big fppf**
site, because it is a condition on charts of a presheaf on that site, while the surjectivity is
local for the **small étale** topology of `F`.  The passage between the two is
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le`, which refines a
covering sieve of the small étale site over an object with affine underlying scheme to a finite
family of charts with affine underlying scheme whose family of underlying morphisms of schemes
is an étale covering family; an étale covering family of schemes is an fppf one
(`AlgebraicGeometry.Scheme.etalePrecoverage_le_fppfPrecoverage`), so
`AlgebraicGeometry.BigFppfOver.sieve_generate_ofArrows_mem_topology` turns it into a covering
sieve of the big fppf site.  That refinement is also what makes the members affine, which is
what the cofinality condition asks for, and it is why the condition is proved here for affine
charts only — the form `AlgebraicGeometry.Space.IsCofinalChartFamily` has, raised to arbitrary
étale charts by `AlgebraicGeometry.Space.IsCofinalChartFamily.exists_cover`.

### Why the selected class carries an existential over the étaleness

`AlgebraicGeometry.Space.IsCofinalChartFamily` applies its predicate `P` to a chart with no
proof of étaleness, while a section of `G i` lives over an *object of the small étale site*,
which is a chart together with such a proof.  So
`AlgebraicGeometry.Space.HasSomeChartSection` quantifies existentially over the proof.  Nothing
is lost: étaleness is a proposition, so any two proofs give the same object of the site and the
same sections.

### Why the surjectivity is onto an arbitrary terminal sheaf

The final sheaf `*` of a site is the terminal object, and the statement to be used does not
depend on which presentation of it the caller has: the only thing the argument uses is that the
target has a section over every object, which
`AlgebraicGeometry.Space.isCofinalChartFamily_hasSomeChartSection_of_nonempty` asks for
directly.  A terminal sheaf has one, by mapping the constant sheaf `PUnit` into it, and that is
what the two named forms of the statement supply.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {I : Type w'}

/-- **One of the sheaves `G i` has a section over an object of the small étale site of `F`.**
By the Yoneda lemma for the small étale site this says that the chart underlying the object
factors through one of the `G i`. -/
def SmallEtale.HasSomeSection (G : I → Sheaf (SmallEtale.topology B S hS F) (Type w))
    (W : SmallEtale B S hS F) : Prop :=
  ∃ i, Nonempty ((G i).obj.obj (op W))

/-- **The class of charts of `F` selected by a family of sheaves on its small étale site**: a
chart `b : h_T ⟶ F` is selected when it is an étale chart and one of the `G i` has a section
over the resulting object of the small étale site.

This is the predicate `AlgebraicGeometry.Space.IsCofinalChartFamily` is proved for below.  The
étaleness is existentially quantified because `AlgebraicGeometry.Space.IsCofinalChartFamily`
applies its predicate to a bare chart; see the implementation notes. -/
def HasSomeChartSection (G : I → Sheaf (SmallEtale.topology B S hS F) (Type w))
    (T : BigFppfOver B S hS) (b : yoneda.obj T ⟶ F) : Prop :=
  ∃ hb : IsEtaleChart B S hS F (CostructuredArrow.mk b),
    SmallEtale.HasSomeSection B S hS F G ⟨CostructuredArrow.mk b, hb⟩

/-- An object of the small étale site over which one of the `G i` has a section is a selected
chart.  This is the identification of the object with the chart it consists of, which is a
matter of the structure's own projections. -/
theorem hasSomeChartSection_of_hasSomeSection
    {G : I → Sheaf (SmallEtale.topology B S hS F) (Type w)} {W : SmallEtale B S hS F}
    (hW : SmallEtale.HasSomeSection B S hS F G W) :
    HasSomeChartSection B S hS F G ((SmallEtale.toOver B S hS F).obj W) W.1.hom :=
  ⟨W.2, hW⟩

/-- **Reading the selected class at a chart already known to be étale**: the existential over
the étaleness carries no information, because étaleness is a proposition.  This is how a
consumer gets the section of `G i` out of the predicate. -/
theorem hasSomeChartSection_iff {G : I → Sheaf (SmallEtale.topology B S hS F) (Type w)}
    {T : BigFppfOver B S hS} {b : yoneda.obj T ⟶ F}
    (hb : IsEtaleChart B S hS F (CostructuredArrow.mk b)) :
    HasSomeChartSection B S hS F G T b ↔
      SmallEtale.HasSomeSection B S hS F G ⟨CostructuredArrow.mk b, hb⟩ :=
  ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩

/-- **The final sheaf has a section over every object of the small étale site.**  Together with
`AlgebraicGeometry.Space.isCofinalChartFamily_hasSomeChartSection_terminal` this shows that
neither the selected class nor the hypothesis of
`AlgebraicGeometry.Space.isCofinalChartFamily_hasSomeChartSection` is vacuous. -/
theorem SmallEtale.hasSomeSection_terminal (W : SmallEtale B S hS F) :
    SmallEtale.HasSomeSection B S hS F
      (fun _ : PUnit.{w' + 1} =>
        Sheaf.terminal (SmallEtale.topology B S hS F) Types.isTerminalPUnit.{w}) W :=
  ⟨PUnit.unit, ⟨PUnit.unit⟩⟩

/-- **The selected charts are cofinal among the affine étale charts of `F`, given that the
sheaves `G i` have sections locally on the small étale site.**

Over an affine étale chart `c` of `F` the hypothesis supplies a covering sieve of the
corresponding object of the small étale site all of whose arrows have a section of some `G i`
over their source.  Refining that sieve to a finite family of charts with affine underlying
scheme whose underlying morphisms of schemes form an étale covering family
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le`) gives a family of
affine objects of the big fppf site which is covering there, because an étale covering family of
schemes is an fppf one, and each of whose members is a selected chart. -/
theorem isCofinalChartFamily_hasSomeChartSection
    (G : I → Sheaf (SmallEtale.topology B S hS F) (Type w))
    (hG : ∀ W : SmallEtale B S hS F, ∃ T : Sieve W, T ∈ SmallEtale.topology B S hS F W ∧
      ∀ ⦃V : SmallEtale B S hS F⦄ (g : V ⟶ W), T g → SmallEtale.HasSomeSection B S hS F G V) :
    IsCofinalChartFamily B S hS (F := F) (HasSomeChartSection B S hS F G) := by
  intro R hR c hc
  have hEt : IsEtaleChart B S hS F (CostructuredArrow.mk c) :=
    (isEtale_iff_presheaf_of_yoneda B S hS c).1 hc
  obtain ⟨T, hT, hTsec⟩ := hG ⟨CostructuredArrow.mk c, hEt⟩
  obtain ⟨n, z, φ, hzaff, hzT, -, hzet⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS F
      (x := (⟨CostructuredArrow.mk c, hEt⟩ : SmallEtale B S hS F)) hR hT
  refine ⟨ULift.{u} (Fin n), fun j => (SmallEtale.toOver B S hS F).obj (z j.down),
    fun j => (SmallEtale.toOver B S hS F).map (φ j.down), fun j => hzaff j.down,
    fun j => ?_, ?_, fun j => ?_⟩
  · refine (isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((presheaf_yoneda_map_etale_iff B S hS _).2 ?_)
    exact etale_of_etale_charts B S hS (z j.down).1.hom c (z j.down).2 hEt
      ((SmallEtale.toOver B S hS F).map (φ j.down)) (CostructuredArrow.w (φ j.down).hom)
  · refine BigFppfOver.sieve_generate_ofArrows_mem_topology _ _ ?_
    exact Scheme.etalePrecoverage_le_fppfPrecoverage _
      (Scheme.mem_etalePrecoverage_of_equiv Equiv.ulift.{u} hzet)
  · rw [show (yoneda.map ((SmallEtale.toOver B S hS F).map (φ j.down)) ≫ c) =
      (z j.down).1.hom from CostructuredArrow.w (φ j.down).hom]
    exact hasSomeChartSection_of_hasSomeSection B S hS F
      (hTsec (φ j.down) (hzT j.down))

/-- **The selected charts are cofinal, given a surjection of the coproduct of the `G i` onto a
sheaf with a section over every object.**

This is `AlgebraicGeometry.Space.isCofinalChartFamily_hasSomeChartSection`, whose hypothesis is
supplied by `CategoryTheory.Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc`: a family whose
induced morphism out of the coproduct is locally surjective is jointly locally surjective on
sections, so a section of the target over an object restricts, along the arrows of a covering
sieve, into the image of one of the `G i`.  In particular each such arrow has a section of some
`G i` over its source. -/
theorem isCofinalChartFamily_hasSomeChartSection_of_nonempty
    {G : I → Sheaf (SmallEtale.topology B S hS F) (Type w)} [HasCoproduct G]
    {Y : Sheaf (SmallEtale.topology B S hS F) (Type w)} (c : ∀ i, G i ⟶ Y)
    (hY : ∀ W : SmallEtale B S hS F, Nonempty (Y.obj.obj (op W)))
    (hc : Sheaf.IsLocallySurjective (Sigma.desc c)) :
    IsCofinalChartFamily B S hS (F := F) (HasSomeChartSection B S hS F G) := by
  refine isCofinalChartFamily_hasSomeChartSection B S hS F G fun W => ?_
  obtain ⟨T, hT, hTsec⟩ :=
    Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc c hc (hY W).some
  exact ⟨T, hT, fun {V} g hg => by
    obtain ⟨i, t, -⟩ := hTsec g hg
    exact ⟨i, ⟨t⟩⟩⟩

/-- **The selected charts are cofinal, given that `∐ᵢ Gᵢ ⟶ *` is a surjection onto the final
sheaf of the small étale site of `F`.**  This is the form the proof of
[Stacks Project, Tag 04KL] produces: there the `G i` are the sheaves `g⁻¹h_{V_i}` of an affine
étale cover `V i` of the target, and their joint surjectivity onto the final sheaf is what makes
a chart of the source admit, locally, a section of one of them.

The target is an arbitrary terminal sheaf, since the statement does not depend on which
presentation of the final sheaf the caller has; a terminal sheaf has a section over every object
because the constant sheaf `PUnit` maps into it. -/
theorem isCofinalChartFamily_of_isLocallySurjective_sigmaDesc
    {G : I → Sheaf (SmallEtale.topology B S hS F) (Type w)} [HasCoproduct G]
    {Y : Sheaf (SmallEtale.topology B S hS F) (Type w)} (hYterm : IsTerminal Y)
    (c : ∀ i, G i ⟶ Y) (hc : Sheaf.IsLocallySurjective (Sigma.desc c)) :
    IsCofinalChartFamily B S hS (F := F) (HasSomeChartSection B S hS F G) :=
  isCofinalChartFamily_hasSomeChartSection_of_nonempty B S hS F c
    (fun W => ⟨(hYterm.from (Sheaf.terminal _ Types.isTerminalPUnit)).hom.app (op W) PUnit.unit⟩)
    hc

/-- **The selected charts are cofinal, given that `∐ᵢ Gᵢ ⟶ *` is a surjection onto the constant
sheaf `PUnit`.**  This is
`AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_sigmaDesc` with the final
sheaf of the small étale site spelled out, so that a caller producing the surjectivity need not
also produce a terminal object of the category of sheaves. -/
theorem isCofinalChartFamily_of_isLocallySurjective_finalSheaf
    {G : I → Sheaf (SmallEtale.topology B S hS F) (Type w)} [HasCoproduct G]
    (c : ∀ i, G i ⟶ Sheaf.terminal (SmallEtale.topology B S hS F) Types.isTerminalPUnit)
    (hc : Sheaf.IsLocallySurjective (Sigma.desc c)) :
    IsCofinalChartFamily B S hS (F := F) (HasSomeChartSection B S hS F G) :=
  isCofinalChartFamily_of_isLocallySurjective_sigmaDesc B S hS F
    (Sheaf.isTerminalTerminal _ Types.isTerminalPUnit) c hc

/-- **The class selected by the one-member family consisting of the final sheaf is cofinal**, and
it holds at every affine étale chart.  So the hypothesis of
`AlgebraicGeometry.Space.isCofinalChartFamily_hasSomeChartSection` is satisfiable and the class
it selects can be the whole of the affine étale charts: none of the statements above is empty. -/
theorem isCofinalChartFamily_hasSomeChartSection_terminal :
    IsCofinalChartFamily B S hS (F := F) (HasSomeChartSection B S hS F
      (fun _ : PUnit.{w' + 1} =>
        Sheaf.terminal (SmallEtale.topology B S hS F) Types.isTerminalPUnit.{w})) :=
  isCofinalChartFamily_hasSomeChartSection B S hS F _ fun W =>
    ⟨⊤, (SmallEtale.topology B S hS F).top_mem W,
      fun {V} _ _ => SmallEtale.hasSomeSection_terminal B S hS F V⟩

/-! ### The two gluing statements with their cofinality hypothesis discharged -/

section Gluing

variable {X Y : AlgebraicSpaces B S hS}
  {G : I → Sheaf (SmallEtale.topology B S hS X.1) (Type u)} [HasCoproduct G]
  {Z : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}

/-- **A family of morphisms to an algebraic space `Y`, given on the charts of `X` selected by a
family of sheaves whose coproduct surjects onto the final sheaf of the small étale site of `X`
and compatible up to 2-isomorphism, glues to a morphism `X ⟶ Y`.**

This is `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso_of_cofinal` with its cofinality
hypothesis discharged by
`AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_sigmaDesc`.  It is the form
step 5 of the proof of [Stacks Project, Tag 04KL] consumes: the morphism over a selected chart
is read off the section of one of the `G i` there, and the surjectivity is what makes the
selected charts cover. -/
theorem exists_hom_of_chartHoms_twoIso_of_isLocallySurjective_sigmaDesc
    (hZ : IsTerminal Z) (cz : ∀ i, G i ⟶ Z)
    (hcz : Sheaf.IsLocallySurjective (Sigma.desc cz))
    (k : ∀ T : BigFppfOver B S hS, IsAffineOver B S hS T →
      ∀ b : yoneda.obj T ⟶ X.1, IsEtale B S hS b →
        HasSomeChartSection B S hS X.1 G T b → (yoneda.obj T ⟶ Y.1))
    (hk : ∀ (T U : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
      (hU : IsAffineOver B S hS U) (r : T ⟶ U) (b : yoneda.obj U ⟶ X.1)
      (hb : IsEtale B S hS b) (hrb : IsEtale B S hS (yoneda.map r ≫ b))
      (hPb : HasSomeChartSection B S hS X.1 G U b)
      (hPrb : HasSomeChartSection B S hS X.1 G T (yoneda.map r ≫ b)),
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS
          (ObjectProperty.homMk (yoneda.map r ≫ k U hU b hb hPb) :
            (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y))
        (smallEtaleRingedToposHom B S hS
          (ObjectProperty.homMk (k T hT (yoneda.map r ≫ b) hrb hPrb) :
            (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y))))
    (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ X.1) (hb : IsEtale B S hS b)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ l : X.1 ⟶ Y.1, ∀ (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T) (r : T ⟶ U)
      (hrb : IsEtale B S hS (yoneda.map r ≫ b))
      (hPrb : HasSomeChartSection B S hS X.1 G T (yoneda.map r ≫ b)),
      yoneda.map r ≫ b ≫ l = k T hT (yoneda.map r ≫ b) hrb hPrb :=
  exists_hom_of_chartHoms_twoIso_of_cofinal B S hS X.property.isSheaf
    (isCofinalChartFamily_of_isLocallySurjective_sigmaDesc B S hS X.1 hZ cz hcz) k hk U b hb hsurj

/-- **Chartwise 2-isomorphisms over the charts selected by a family of sheaves whose coproduct
surjects onto the final sheaf of the small étale site of `X` glue to a global one.**

This is `AlgebraicGeometry.Space.inducesSmallEtaleRingedToposHom_of_cofinal` — step 6 of the
proof of [Stacks Project, Tag 04KL] — with its cofinality hypothesis discharged by
`AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_sigmaDesc`. -/
theorem inducesSmallEtaleRingedToposHom_of_isLocallySurjective_sigmaDesc
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (l : X ⟶ Y) (hZ : IsTerminal Z) (cz : ∀ i, G i ⟶ Z)
    (hcz : Sheaf.IsLocallySurjective (Sigma.desc cz))
    (ht : ∀ T : BigFppfOver B S hS, IsAffineOver B S hS T →
      ∀ b : yoneda.obj T ⟶ X.1, IsEtale B S hS b →
        HasSomeChartSection B S hS X.1 G T b →
        InducesSmallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l)
          (smallEtaleComp B S hS ψ
            (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b)))) :
    InducesSmallEtaleRingedToposHom B S hS l ψ :=
  inducesSmallEtaleRingedToposHom_of_cofinal B S hS ψ l _
    (isCofinalChartFamily_of_isLocallySurjective_sigmaDesc B S hS X.1 hZ cz hcz) ht

end Gluing

end AlgebraicGeometry.Space

end
