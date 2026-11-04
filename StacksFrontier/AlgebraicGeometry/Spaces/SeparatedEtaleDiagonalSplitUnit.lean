module

public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalChartFunctoriality

/-!
# Extension by zero across the diagonal of a separated étale morphism

Let `f : X ⟶ Y` be a separated étale morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, with relative diagonal `Δ : X ⟶ X ×_Y X`, and let `ℳ` be an
`𝒪_{X ×_Y X}`-module.  The diagonal cuts every étale chart `V` of `X ×_Y X` into two disjoint
clopen pieces, `V ×_{X ×_Y X} X` and its complement
(`StacksFrontier/AlgebraicGeometry/Spaces/SeparatedEtaleDiagonalChartDecomposition.lean`), so a
section of `ℳ` over the first piece extends uniquely to a section over `V` vanishing on the
second.  That is **extension by zero**, and this file builds it and shows that it is additive,
`𝒪`-semilinear and natural in the chart — hence a morphism of `𝒪_{X ×_Y X}`-modules

`Δ_*Δ^*ℳ ⟶ ℳ`,

`AlgebraicGeometry.Space.diagonalExtendByZeroHom`, where the direct image along `Δ` is read on
charts through `AlgebraicGeometry.Space.diagonalSmallBaseChangeAdjunction`.

This morphism is the splitting that the proof of Stacks 0HAP needs: composed with the unit
`ℳ ⟶ Δ_*Δ^*ℳ` of that adjunction it is the identity, because over each chart the unit is
restriction to the piece cut out by the diagonal and extension by zero is a section of that
restriction (`AlgebraicGeometry.Space.extendByZeroRestrictFun_res`).  That last composition
identity is **not** proved here; see the implementation notes for why, and
`StacksFrontier/AlgebraicGeometry/Spaces/SeparatedEtaleDiagonalPushforward.lean` for what it would
feed.  Nothing here carries the tag of Stacks 0HAP.

## Main definitions

* `AlgebraicGeometry.Space.diagonalExtendByZero`: the section of `ℳ` over a chart extending a
  given section on the diagonal piece by zero on the complement.
* `AlgebraicGeometry.Space.diagonalExtendByZeroHom`: that construction as a morphism of
  `𝒪_{X ×_Y X}`-modules `Δ_*Δ^*ℳ ⟶ ℳ`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_glue_diagonalChartPair`: a pair of sections on the two
  pieces of a chart extends to a unique section over the chart.
* `AlgebraicGeometry.Space.diagonalExtendByZero_res` and
  `AlgebraicGeometry.Space.diagonalExtendByZero_res_complement`: the two defining restrictions.
* `AlgebraicGeometry.Space.diagonalExtendByZero_add`,
  `AlgebraicGeometry.Space.diagonalExtendByZero_smul` and
  `AlgebraicGeometry.Space.diagonalExtendByZero_naturality`: extension by zero is additive,
  semilinear and natural in the chart.
* `AlgebraicGeometry.Space.smallBaseChangeSharp_app_diagonalChartHom`: the structure map of base
  change at a chart is restriction of regular functions along the cartesian projection, which is
  what makes extension by zero `𝒪`-linear for the module structure on the direct image.

## Implementation notes

The sheaf condition is used only through its type-valued form,
`AlgebraicGeometry.Space.isSheaf_type_modules_val_presheaf`: the gluing is produced by
`CategoryTheory.Presieve.IsSheaf.existsUnique_section_of_pair` for sheaves of sets, and
additivity, semilinearity and naturality are then all consequences of the *uniqueness* clause,
not of any further sheaf-theoretic input.  That is what keeps the module-theoretic part of the
argument short: a morphism out of a sheaf of modules is pinned down by what it does to
restrictions.

Everything is phrased twice, once on the sections of `Δ^*ℳ` over a base-changed chart and once
on the sections of `Δ_*Δ^*ℳ` over the chart itself.  The two are definitionally the same type,
but only through *two* successive restrictions of scalars — the direct image along base change
and the identity structure map of étale restriction — and comparing them in one step makes the
elaborator unfold the chosen fibre products of
`CategoryTheory.Functor.relativelyRepresentable.pullback`, which are `Classical.choose`s; the
comparison then does not terminate within the default heartbeat budget.  Peeling one restriction
of scalars at a time is cheap, which is why each statement appears in both readings and the
pushforward reading is always deduced from the pullback reading.

## What is missing

The identity `AlgebraicGeometry.Space.diagonalExtendByZeroHom ≫ unit = 𝟙` is exactly
`AlgebraicGeometry.Space.extendByZeroRestrictFun_res` read over every chart, and
`AlgebraicGeometry.Space.diagonalSmallBaseChangeAdjunction_unit_app_val_app` identifies the unit
with the restriction it needs.  Both are available; what is not available is a *cheap* way to
compare the equation at the two spellings of the sections.  The equation of elements has its two
sides naturally typed in the sections of `Δ_*Δ^*ℳ` and in the sections of `ℳ` over the
base-changed chart, two restrictions of scalars apart, and that one comparison is the step the
elaborator does not complete within the default budget.  It is a performance obstruction and not
a mathematical one: with the heartbeat limit raised the proof

`fun V x ↦ (diagonalSmallBaseChangeAdjunction_unit_app_val_app … ).trans
  (extendByZeroRestrictFun_res … )`

closes it, and feeding the resulting `SplitEpi` to
`AlgebraicGeometry.Space.counitSplitEpiOfSplitEpiChartUnit` proves Stacks 0HAP.

## References

* [Stacks Project, Tag 0HAP](https://stacks.math.columbia.edu/tag/0HAP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
  (hsep : IsSeparated B S hS f.hom)
  (M : Modules.{u, u} B S hS (selfFibreSquare B S hS f).1 (selfFibreSquare B S hS f).2)

/-- The presheaf of sets of sections of an `𝒪`-module on the small étale site is a sheaf. -/
theorem isSheaf_type_modules_val_presheaf :
    Presieve.IsSheaf (SmallEtale.topology B S hS (selfFibreSquare B S hS f).1)
      (M.val.presheaf ⋙ forget AddCommGrpCat.{u}) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf

/-- **Prescribing a section of a module on the two clopen pieces of a chart.**  A section of `M`
over the base-changed piece `V ×_{X ×_Y X} X` and one over the complementary piece extend to a
unique section over `V`. -/
theorem existsUnique_glue_diagonalChartPair
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (s : M.val.obj (op (diagonalChart B S hS f het hsep V)))
    (t : M.val.obj (op (diagonalChartComplement B S hS f het hsep V))) :
    ∃! x : M.val.obj (op V),
      M.val.map (diagonalChartHom B S hS f het hsep V).op x = s ∧
        M.val.map (diagonalChartComplementHom B S hS f het hsep V).op x = t :=
  existsUnique_section_of_diagonalChartPair B S hS f het hsep
    (isSheaf_type_modules_val_presheaf B S hS f M) V s t

/-- **Extension by zero across the diagonal.**  The section of `M` over an étale chart `V` of
`X ×_Y X` which restricts to a prescribed section on the piece `V ×_{X ×_Y X} X` cut out by the
diagonal and to zero on the complementary piece. -/
noncomputable def diagonalExtendByZero (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (s : M.val.obj (op (diagonalChart B S hS f het hsep V))) : M.val.obj (op V) :=
  (existsUnique_glue_diagonalChartPair B S hS f het hsep M V s 0).choose

/-- Extension by zero restricts to the prescribed section on the piece cut out by the
diagonal. -/
theorem diagonalExtendByZero_res (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (s : M.val.obj (op (diagonalChart B S hS f het hsep V))) :
    M.val.map (diagonalChartHom B S hS f het hsep V).op
        (diagonalExtendByZero B S hS f het hsep M V s) = s :=
  (existsUnique_glue_diagonalChartPair B S hS f het hsep M V s 0).choose_spec.1.1

/-- Extension by zero restricts to zero on the complementary piece. -/
theorem diagonalExtendByZero_res_complement
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (s : M.val.obj (op (diagonalChart B S hS f het hsep V))) :
    M.val.map (diagonalChartComplementHom B S hS f het hsep V).op
        (diagonalExtendByZero B S hS f het hsep M V s) = 0 :=
  (existsUnique_glue_diagonalChartPair B S hS f het hsep M V s 0).choose_spec.1.2

/-- Extension by zero is the only section with the two prescribed restrictions. -/
theorem eq_diagonalExtendByZero (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (s : M.val.obj (op (diagonalChart B S hS f het hsep V))) (x : M.val.obj (op V))
    (h₁ : M.val.map (diagonalChartHom B S hS f het hsep V).op x = s)
    (h₂ : M.val.map (diagonalChartComplementHom B S hS f het hsep V).op x = 0) :
    x = diagonalExtendByZero B S hS f het hsep M V s :=
  (existsUnique_glue_diagonalChartPair B S hS f het hsep M V s 0).choose_spec.2 x ⟨h₁, h₂⟩

/-- Extension by zero is additive. -/
theorem diagonalExtendByZero_add (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (s s' : M.val.obj (op (diagonalChart B S hS f het hsep V))) :
    diagonalExtendByZero B S hS f het hsep M V (s + s') =
      diagonalExtendByZero B S hS f het hsep M V s +
        diagonalExtendByZero B S hS f het hsep M V s' := by
  refine (eq_diagonalExtendByZero B S hS f het hsep M V (s + s') _ ?_ ?_).symm
  · refine Eq.trans (map_add _ _ _) ?_
    rw [diagonalExtendByZero_res, diagonalExtendByZero_res]
    rfl
  · refine Eq.trans (map_add _ _ _) ?_
    rw [diagonalExtendByZero_res_complement, diagonalExtendByZero_res_complement, add_zero]

/-- **Extension by zero is semilinear.**  For a regular function `r` on `V` whose restriction
to the piece cut out by the diagonal is `r'`, extending `r' • s` by zero is `r` times the
extension of `s` by zero.

The restricted scalar is passed as a separate argument with its defining equation rather than
written out, because the elaborated type of an applied morphism of `RingCat` is not the sort
coercion of its target and the scalar action on the sections is then not found. -/
theorem diagonalExtendByZero_smul (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      (selfFibreSquare B S hS f).1 (selfFibreSquare B S hS f).2).O)).obj.obj (op V))
    (r' : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      (selfFibreSquare B S hS f).1
      (selfFibreSquare B S hS f).2).O)).obj.obj (op (diagonalChart B S hS f het hsep V)))
    (hr : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      (selfFibreSquare B S hS f).1
      (selfFibreSquare B S hS f).2).O)).obj.map (diagonalChartHom B S hS f het hsep V).op r = r')
    (s : M.val.obj (op (diagonalChart B S hS f het hsep V))) :
    diagonalExtendByZero B S hS f het hsep M V (r' • s) =
      r • diagonalExtendByZero B S hS f het hsep M V s := by
  subst hr
  refine (eq_diagonalExtendByZero B S hS f het hsep M V _ _ ?_ ?_).symm
  · refine Eq.trans (PresheafOfModules.map_smul M.val _ r _) ?_
    congr 1
    exact diagonalExtendByZero_res B S hS f het hsep M V s
  · refine Eq.trans (PresheafOfModules.map_smul M.val _ r _) ?_
    exact Eq.trans (congrArg _ (diagonalExtendByZero_res_complement B S hS f het hsep M V s))
      (smul_zero _)

/-- Restricting along `j` and then `c` agrees with restricting along `b` and then `a`, when
`a ≫ b = c ≫ j`. -/
private theorem map_map_eq_of_comp_eq {P Q W V : SmallEtale B S hS (selfFibreSquare B S hS f).1}
    (a : P ⟶ Q) (b : Q ⟶ V) (c : P ⟶ W) (j : W ⟶ V) (h : a ≫ b = c ≫ j)
    (x : M.val.obj (op V)) :
    M.val.map c.op (M.val.map j.op x) = M.val.map a.op (M.val.map b.op x) :=
  (M.val.map_comp_apply j.op c.op x).symm.trans
    ((M.val.congr_map_apply (congrArg Quiver.Hom.op h.symm) x).trans
      (M.val.map_comp_apply b.op a.op x))

/-- **Extension by zero is natural in the chart.**  Restricting the extension of a section
along a morphism of charts is the extension of the restricted section: the two pieces of the
smaller chart map to the two pieces of the larger one. -/
theorem diagonalExtendByZero_naturality
    {W V : SmallEtale B S hS (selfFibreSquare B S hS f).1} (j : W ⟶ V)
    (s : M.val.obj (op (diagonalChart B S hS f het hsep V))) :
    M.val.map j.op (diagonalExtendByZero B S hS f het hsep M V s) =
      diagonalExtendByZero B S hS f het hsep M W
        (M.val.map (diagonalChartMap B S hS f het hsep j).op s) := by
  refine eq_diagonalExtendByZero B S hS f het hsep M W _ _ ?_ ?_
  · refine (map_map_eq_of_comp_eq B S hS f M _ _ _ j
      (diagonalChartMap_comp_diagonalChartHom B S hS f het hsep j) _).trans ?_
    exact congrArg _ (diagonalExtendByZero_res B S hS f het hsep M V s)
  · refine (map_map_eq_of_comp_eq B S hS f M _ _ _ j
      (diagonalChartComplementMap_comp_diagonalChartComplementHom B S hS f het hsep j) _).trans ?_
    exact Eq.trans
      (congrArg _ (diagonalExtendByZero_res_complement B S hS f het hsep M V s))
      (map_zero _)

/-- **The structure map of base change at a chart is restriction of regular functions along the
cartesian projection.**  This is
`AlgebraicGeometry.Space.smallBaseChangeSharp_counit` read at one chart, the comparison being
with the identity structure map of étale restriction. -/
theorem smallBaseChangeSharp_app_diagonalChartHom
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    (smallBaseChangeSharp B S hS (selfFibreDiagonal B S hS f)
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).hom.app (op V) =
      (smallEtaleRingSheaf B S hS (selfFibreSquare B S hS f).1
        (selfFibreSquare B S hS f).2).obj.map
        (diagonalChartHom B S hS f het hsep V).op :=
  ((NatTrans.congr_app (smallBaseChangeSharp_counit B S hS (selfFibreDiagonal B S hS f)
    (isEtale_selfFibreDiagonal B S hS f het)
    (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)) (op V)).trans
      (Category.comp_id _)).symm

/-- `Δ^*ℳ`: the restriction of an `𝒪_{X ×_Y X}`-module to `X` along the diagonal, as étale
restriction of modules. -/
noncomputable abbrev diagonalRestrict :=
  (etaleModulePullback.{u, u} B S hS (selfFibreDiagonal B S hS f)
    (isEtale_selfFibreDiagonal B S hS f het)).obj M

/-- `Δ_*Δ^*ℳ`: the direct image along the diagonal of the restriction of `ℳ`, taken through
base change of charts.  This is the target of the unit of
`AlgebraicGeometry.Space.diagonalSmallBaseChangeAdjunction` at `ℳ`. -/
noncomputable def diagonalPushforwardRestrict : Modules.{u, u} B S hS (selfFibreSquare B S hS f).1
    (selfFibreSquare B S hS f).2 :=
  (smallBaseChangeModulePushforward.{u, u} B S hS (selfFibreDiagonal B S hS f)
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).obj
    (diagonalRestrict B S hS f het M)

/-- **Extension by zero, on the sections of `Δ^*ℳ` over a base-changed chart.**  The sections of
`Δ^*ℳ` over `V ×_{X ×_Y X} X` are the sections of `ℳ` over the chart `V ×_{X ×_Y X} X` of
`X ×_Y X`, and this is `AlgebraicGeometry.Space.diagonalExtendByZero` read through that
identification. -/
noncomputable def extendByZeroRestrictFun (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    (diagonalRestrict B S hS f het M).val.obj
      (op ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).obj V)) →
      M.val.obj (op V) :=
  fun s ↦ diagonalExtendByZero B S hS f het hsep M V s

/-- **Extension by zero, on the sections of `Δ_*Δ^*ℳ` over a chart.**  The same map, read on the
sections of the direct image, which are the sections of `Δ^*ℳ` over the base-changed chart. -/
noncomputable def extendByZeroFun (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    (diagonalPushforwardRestrict B S hS f het hsep M).val.obj (op V) → M.val.obj (op V) :=
  extendByZeroRestrictFun B S hS f het hsep M V

/-- Extension by zero is additive, on the sections of `Δ^*ℳ`. -/
theorem extendByZeroRestrictFun_add (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (x y : (diagonalRestrict B S hS f het M).val.obj
      (op ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).obj V))) :
    extendByZeroRestrictFun B S hS f het hsep M V (x + y) =
      extendByZeroRestrictFun B S hS f het hsep M V x +
        extendByZeroRestrictFun B S hS f het hsep M V y :=
  diagonalExtendByZero_add B S hS f het hsep M V x y

/-- Extension by zero is additive, on the sections of `Δ_*Δ^*ℳ`. -/
theorem extendByZeroFun_add (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (x y : (diagonalPushforwardRestrict B S hS f het hsep M).val.obj (op V)) :
    extendByZeroFun B S hS f het hsep M V (x + y) =
      extendByZeroFun B S hS f het hsep M V x + extendByZeroFun B S hS f het hsep M V y :=
  extendByZeroRestrictFun_add B S hS f het hsep M V x y

/-- Extension by zero is semilinear, on the sections of `Δ^*ℳ`: the scalar is restricted along
the cartesian projection.  As in `AlgebraicGeometry.Space.diagonalExtendByZero_smul` the
restricted scalar is a separate argument with its defining equation. -/
theorem extendByZeroRestrictFun_smul (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      (selfFibreSquare B S hS f).1 (selfFibreSquare B S hS f).2).O)).obj.obj (op V))
    (r₁ : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj
      (op ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
        (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).obj V)))
    (hr : (smallBaseChangeSharp B S hS (selfFibreDiagonal B S hS f)
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).hom.app (op V) r = r₁)
    (x : (diagonalRestrict B S hS f het M).val.obj
      (op ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).obj V))) :
    extendByZeroRestrictFun B S hS f het hsep M V (r₁ • x) =
      r • extendByZeroRestrictFun B S hS f het hsep M V x :=
  diagonalExtendByZero_smul B S hS f het hsep M V r r₁
    (((ConcreteCategory.congr_hom
      (smallBaseChangeSharp_app_diagonalChartHom B S hS f het hsep V) r).symm).trans hr) x

/-- **Extension by zero is `𝒪`-linear on the sections of `Δ_*Δ^*ℳ`.**  The scalar action on those
sections is restriction of scalars along the structure map of base change, which is restriction
of regular functions along the cartesian projection by
`AlgebraicGeometry.Space.smallBaseChangeSharp_app_diagonalChartHom`. -/
theorem extendByZeroFun_smul (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      (selfFibreSquare B S hS f).1 (selfFibreSquare B S hS f).2).O)).obj.obj (op V))
    (x : (diagonalPushforwardRestrict B S hS f het hsep M).val.obj (op V)) :
    extendByZeroFun B S hS f het hsep M V (r • x) =
      r • extendByZeroFun B S hS f het hsep M V x :=
  extendByZeroRestrictFun_smul B S hS f het hsep M V r _ rfl x


/-- Extension by zero restricts to the given section on the piece cut out by the diagonal. -/
theorem extendByZeroRestrictFun_res (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (x : (diagonalRestrict B S hS f het M).val.obj
      (op ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).obj V))) :
    M.val.map (diagonalChartHom B S hS f het hsep V).op
        (extendByZeroRestrictFun B S hS f het hsep M V x) = x :=
  diagonalExtendByZero_res B S hS f het hsep M V x

/-- Extension by zero is natural in the chart, on the sections of `Δ^*ℳ`. -/
theorem extendByZeroRestrictFun_naturality
    {W V : SmallEtale B S hS (selfFibreSquare B S hS f).1} (j : W ⟶ V)
    (x : (diagonalRestrict B S hS f het M).val.obj
      (op ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).obj V))) :
    extendByZeroRestrictFun B S hS f het hsep M W
        ((diagonalRestrict B S hS f het M).val.map
          ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
          (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).map j).op x) =
      M.val.map j.op (extendByZeroRestrictFun B S hS f het hsep M V x) :=
  (diagonalExtendByZero_naturality B S hS f het hsep M j x).symm

/-- Extension by zero is natural in the chart, on the sections of `Δ_*Δ^*ℳ`. -/
theorem extendByZeroFun_naturality
    {W V : SmallEtale B S hS (selfFibreSquare B S hS f).1} (j : W ⟶ V)
    (x : (diagonalPushforwardRestrict B S hS f het hsep M).val.obj (op V)) :
    extendByZeroFun B S hS f het hsep M W
        ((diagonalPushforwardRestrict B S hS f het hsep M).val.map j.op x) =
      M.val.map j.op (extendByZeroFun B S hS f het hsep M V x) :=
  extendByZeroRestrictFun_naturality B S hS f het hsep M j x

/-- Extension by zero over one chart, as an `𝒪(V)`-linear map. -/
noncomputable def extendByZeroLinear (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    (diagonalPushforwardRestrict B S hS f het hsep M).val.obj (op V) →ₗ[
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (selfFibreSquare B S hS f).1 (selfFibreSquare B S hS f).2).O)).obj.obj (op V)]
      M.val.obj (op V) where
  toFun := extendByZeroFun B S hS f het hsep M V
  map_add' := extendByZeroFun_add B S hS f het hsep M V
  map_smul' := extendByZeroFun_smul B S hS f het hsep M V

/-- **Extension by zero as a morphism of presheaves of modules `Δ_*Δ^*ℳ ⟶ ℳ`.**  Its naturality
is `AlgebraicGeometry.Space.extendByZeroFun_naturality`.

The two `letI`s bridge the two spellings of the structure sheaf of rings: the sheaves of modules
are indexed through `AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does
not unfold, so the scalar action on the sections is not found through the spelling in which the
category of the `app` field is phrased. -/
noncomputable def diagonalExtendByZeroHomVal :
    (diagonalPushforwardRestrict B S hS f het hsep M).val ⟶ M.val where
  app V :=
    letI : Module ((smallEtaleRingSheaf B S hS (selfFibreSquare B S hS f).1
        (selfFibreSquare B S hS f).2).obj.obj V)
        ((diagonalPushforwardRestrict B S hS f het hsep M).val.obj V) :=
      ((diagonalPushforwardRestrict B S hS f het hsep M).val.obj V).isModule
    letI : Module ((smallEtaleRingSheaf B S hS (selfFibreSquare B S hS f).1
        (selfFibreSquare B S hS f).2).obj.obj V) (M.val.obj V) :=
      (M.val.obj V).isModule
    ModuleCat.ofHom (X := (diagonalPushforwardRestrict B S hS f het hsep M).val.obj V)
      (Y := M.val.obj V)
      (extendByZeroLinear B S hS f het hsep M V.unop)
  naturality {_V _W} k :=
    ModuleCat.hom_ext (LinearMap.ext fun x ↦
      extendByZeroFun_naturality B S hS f het hsep M k.unop x)


/-- **Extension by zero across the diagonal, as a morphism of `𝒪_{X ×_Y X}`-modules
`Δ_*Δ^*ℳ ⟶ ℳ`.**  Over an étale chart `V` it sends a section of `ℳ` on the piece
`V ×_{X ×_Y X} X` cut out by the diagonal to the section of `ℳ` on `V` extending it by zero on
the complementary piece.

This is the morphism which splits the unit `ℳ ⟶ Δ_*Δ^*ℳ` of
`AlgebraicGeometry.Space.diagonalSmallBaseChangeAdjunction`; that it does so is the one step of
Stacks 0HAP still missing here, see the module documentation. -/
noncomputable def diagonalExtendByZeroHom : (diagonalPushforwardRestrict B S hS f het hsep M) ⟶ M :=
  { val := diagonalExtendByZeroHomVal B S hS f het hsep M }

end AlgebraicGeometry.Space

end
