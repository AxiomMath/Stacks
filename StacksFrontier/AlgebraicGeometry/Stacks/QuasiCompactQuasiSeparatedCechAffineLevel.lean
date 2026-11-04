module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineRepresentableStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageRuleCechNerve
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactSmoothAffineChart
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveTargetFunctor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# A quasi-compact quasi-separated algebraic stack over an affine is of Čech level three

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks with `𝒴`
representable by an affine scheme. Then `𝒳` is of Čech level `3`
(`AlgebraicGeometry.Stack.AlgebraicStacks.CechAffineLevel`): it has a smooth surjective chart
whose Čech terms are of level `2`, whose own charts have Čech terms of level `1`, and so on down to
Čech terms representable by affine schemes. A quasi-compact stack with a fully faithful
1-morphism to a stack representable by an affine scheme is of level `1`, and one with a
quasi-separated 1-morphism of faithful underlying functor to such a stack is of level `2`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveTargetMap`: the map from the Čech nerve of
  `c` to the Čech nerve of `c ≫ q`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveHead`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveTail`: the first entry of a tuple, and the
  remaining entries.
* `AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveHeadTailSquare`: the square exhibiting the
  degree `n + 1` term of the Čech nerve of `c` as a base change of `c`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasAffineRepresentableBaseChange`: every base change
  along a stack representable by an affine scheme is representable by an affine scheme.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_cechNerveHeadTailSquare`: the
  degree `n + 1` term is the 2-fibre product of the chart with the degree `n` term.
* `AlgebraicGeometry.Stack.AlgebraicStacks.cechAffineLevel_three_of_isQuasiCompactMorphism`: a
  quasi-compact quasi-separated algebraic stack over a stack representable by an affine scheme is
  of Čech level `3`.

## References

* [Stacks Project, Tag 06X3](https://stacks.math.columbia.edu/tag/06X3)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 050M](https://stacks.math.columbia.edu/tag/050M)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Nerve

variable {𝒰 𝒲 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The comparison of Čech nerves along a 1-morphism of the target.** The degree `n` term of
the nerve of `c : 𝒰 ⟶ 𝒲` maps to the degree `n` term of the nerve of `c ≫ q`, by applying `q` to
the common target and to the comparison isomorphisms of a tuple. -/
def cechNerveTargetMap (c : 𝒰 ⟶ 𝒲) (q : 𝒲 ⟶ 𝒴) (n : ℕ) :
    cechNerveStack B S hS c n ⟶ cechNerveStack B S hS (c ≫ q) n :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨Stacks.RelativeCech.Tuple.mapTarget 𝒲.val.val.p (CatFiberedInGroupoids.homFunctor c.hom)
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor q.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p q.hom) n, by
      change (Stacks.RelativeCech.Tuple.projection _ _ n ⋙
        CatFiberedInGroupoids.homFunctor q.hom) ⋙ 𝒴.val.val.p = _
      rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p]
      rfl⟩)

/-- The comparison of Čech nerves lies over `q`, on the nose. -/
theorem cechNerveTargetMap_comp_cechNerveStackProjection (c : 𝒰 ⟶ 𝒲) (q : 𝒲 ⟶ 𝒴) (n : ℕ) :
    cechNerveTargetMap B S hS c q n ≫ cechNerveStackProjection B S hS (c ≫ q) n =
      cechNerveStackProjection B S hS c n ≫ q :=
  rfl

/-- The comparison of Čech nerves along a 1-morphism with faithful underlying functor is fully
faithful. -/
theorem full_cechNerveTargetMap (c : 𝒰 ⟶ 𝒲) (q : 𝒲 ⟶ 𝒴)
    [(CatFiberedInGroupoids.homFunctor q.hom).Faithful] (n : ℕ) :
    (CatFiberedInGroupoids.homFunctor (cechNerveTargetMap B S hS c q n).hom).Full :=
  Stacks.RelativeCech.Tuple.full_mapTarget _ _ _ _ (CatFiberedInGroupoids.homFunctor_comp_p q.hom) n

/-- The comparison of Čech nerves is faithful. -/
theorem faithful_cechNerveTargetMap (c : 𝒰 ⟶ 𝒲) (q : 𝒲 ⟶ 𝒴) (n : ℕ) :
    (CatFiberedInGroupoids.homFunctor (cechNerveTargetMap B S hS c q n).hom).Faithful :=
  Stacks.RelativeCech.Tuple.faithful_mapTarget _ _ _ _
    (CatFiberedInGroupoids.homFunctor_comp_p q.hom) n

/-- The source of a 1-morphism `c : 𝒰 ⟶ 𝒲` of algebraic stacks, re-presented over the base
through `c`: the same category, with structure functor the functor of `c` followed by that of
`𝒲`. -/
def rebasedSource (c : 𝒰 ⟶ 𝒲) : AlgebraicStacks.{u, w} B S hS :=
  ⟨⟨BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor c.hom ⋙ 𝒲.val.val.p),
    (isAlgebraicStack_ofFunctor_homFunctor_comp B S hS c).elim fun h _ => h⟩,
    isAlgebraicStack_ofFunctor_homFunctor_comp B S hS c⟩

/-- The 1-morphism `c`, out of its re-presented source. Its functor is that of `c`. -/
def rebasedHom (c : 𝒰 ⟶ 𝒲) : rebasedSource B S hS c ⟶ 𝒲 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨c.hom.hom.toFunctor, rfl⟩)

/-- The re-presented source is equivalent over the base to the source. -/
def rebasedSourceEquivalenceOver (c : 𝒰 ⟶ 𝒲) :
    StacksRepresentableCFG.EquivalenceOver (rebasedSource B S hS c).val.val.p 𝒰.val.val.p :=
  StacksRepresentableCFG.EquivalenceOver.ofEq (CatFiberedInGroupoids.homFunctor_comp_p c.hom).symm
    (StacksRepresentableCFG.EquivalenceOver.refl _)

/-- The first entry of a tuple, as a 1-morphism from a term of the Čech nerve to the re-presented
source. -/
def cechNerveHead (c : 𝒰 ⟶ 𝒲) (n : ℕ) : cechNerveStack B S hS c n ⟶ rebasedSource B S hS c :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨Stacks.RelativeCech.Tuple.coordinate 𝒲.val.val.p (CatFiberedInGroupoids.homFunctor c.hom) 0,
      CategoryTheory.Functor.ext
        (fun a => Stacks.RelativeCech.Tuple.obj_source_eq 𝒲.val.val.p
          (CatFiberedInGroupoids.homFunctor c.hom) a 0)
        (fun _ _ φ => Stacks.RelativeCech.Tuple.map_source_eq 𝒲.val.val.p
          (CatFiberedInGroupoids.homFunctor c.hom) φ 0)⟩)

/-- Forgetting the first entry of a tuple, as a 1-morphism between consecutive terms of the Čech
nerve. -/
def cechNerveTail (c : 𝒰 ⟶ 𝒲) (n : ℕ) :
    cechNerveStack B S hS c (n + 1) ⟶ cechNerveStack B S hS c n :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨Stacks.RelativeCech.Tuple.reindex 𝒲.val.val.p (CatFiberedInGroupoids.homFunctor c.hom)
      (Fin.succ : Fin (n + 1) → Fin (n + 2)), rfl⟩)

/-- The projection of a term of the Čech nerve factors through forgetting an entry, on the
nose. -/
theorem cechNerveTail_comp_cechNerveStackProjection (c : 𝒰 ⟶ 𝒲) (n : ℕ) :
    cechNerveTail B S hS c n ≫ cechNerveStackProjection B S hS c n =
      cechNerveStackProjection B S hS c (n + 1) :=
  rfl

/-- **The square exhibiting the degree `n + 1` term of the Čech nerve of `c` as the base change
of `c` along the projection of the degree `n` term.** Its legs are the first entry and the
remaining entries of a tuple, and its 2-cell is the first comparison isomorphism. -/
def cechNerveHeadTailSquare (c : 𝒰 ⟶ 𝒲) (n : ℕ) :
    Bicategory.TwoCommSq (rebasedHom B S hS c) (cechNerveStackProjection B S hS c n) where
  pt := cechNerveStack B S hS c (n + 1)
  fst := cechNerveHead B S hS c (n + 1)
  snd := cechNerveTail B S hS c n
  iso := Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso
      (NatIso.ofComponents (fun A => A.comparison 0)
        (fun φ => Stacks.RelativeCech.Tuple.Hom.comparison_naturality φ 0))
      (fun A => A.comparison_lift 0)))

/-- The degree `n + 1` term of the Čech nerve of `c` is a 2-fibre product of `c` with the
projection of the degree `n` term. -/
noncomputable def isTwoFibreProduct_cechNerveHeadTailSquare (c : 𝒰 ⟶ 𝒲) (n : ℕ) :
    Bicategory.IsTwoFibreProduct (cechNerveHeadTailSquare B S hS c n) := by
  refine Bicategory.isTwoFibreProduct_of_underlying ?_
  let a : Bicategory.TwoCommSq.PreHom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} (rebasedHom B S hS c).hom
        (cechNerveStackProjection B S hS c n).hom)
      (cechNerveHeadTailSquare B S hS c n).underlying :=
    { hom := Bicategory.InducedBicategory.mkHom
        ⟨Stacks.RelativeCech.fibreProductToNerve 𝒲.val.val.p
          (CatFiberedInGroupoids.homFunctor c.hom) n,
          Stacks.RelativeCech.fibreProductToNerve_comp_eq _ _ n⟩
      isoFst := Iso.refl _
      isoSnd := Iso.refl _
      compat := by
        apply Bicategory.InducedBicategory.hom₂_ext
        apply BasedNatTrans.ext
        ext P
        change P.iso.hom ≫ (Stacks.RelativeCech.Tuple.projection 𝒲.val.val.p
            (CatFiberedInGroupoids.homFunctor c.hom) n).map (𝟙 _) ≫ 𝟙 _ =
          (CatFiberedInGroupoids.homFunctor c.hom).map (𝟙 _) ≫ 𝟙 _ ≫ P.iso.hom
        rw [(Stacks.RelativeCech.Tuple.projection 𝒲.val.val.p
          (CatFiberedInGroupoids.homFunctor c.hom) n).map_id P.y,
          (CatFiberedInGroupoids.homFunctor c.hom).map_id P.x]
        exact (congrArg (P.iso.hom ≫ ·) (Category.id_comp _)).trans
          ((Category.comp_id _).trans
            ((Category.id_comp _).trans (Category.id_comp _)).symm) }
  exact Bicategory.isTwoFibreProduct_of_isEquivalence_from
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (rebasedHom B S hS c).hom (cechNerveStackProjection B S hS c n).hom) a
    (Stacks.RelativeCech.isEquivalence_fibreProductToNerve _ _ n)

end Nerve

section Transport

variable {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- Representability by an affine scheme passes to the source of a 1-morphism whose underlying
functor is an equivalence, with representable target. -/
private theorem isAffineRepresentable_of_isEquivalence_functor (k : 𝒳 ⟶ 𝒴)
    (hk : k.hom.hom.toFunctor.IsEquivalence) (h : IsAffineRepresentable B S hS 𝒴) :
    IsAffineRepresentable B S hS 𝒳 := by
  obtain ⟨e⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids k.hom.hom.toFunctor k.hom.hom.w hk
  exact isAffineRepresentable_of_equivalenceOver B S hS e h

/-- **Representability by an affine scheme of the apex of a 2-fibre product does not depend on
the 2-fibre product chosen.** -/
theorem isAffineRepresentable_pt_of_isTwoFibreProduct {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵}
    {P Q : Bicategory.TwoCommSq f g} (hP : Bicategory.IsTwoFibreProduct P)
    (hQ : Bicategory.IsTwoFibreProduct Q) (h : IsAffineRepresentable B S hS Q.pt) :
    IsAffineRepresentable B S hS P.pt := by
  let a : Bicategory.TwoCommSq.PreHom P Q := Quotient.out (hQ.from P)
  exact isAffineRepresentable_of_isEquivalence_functor B S hS a.hom
    (isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hP hQ a) h

end Transport

section AffineBaseChange

variable {𝒰 𝒲 𝒬 : AlgebraicStacks.{u, w} B S hS}

/-- A 1-morphism of algebraic stacks **has affine base changes** when its base change along every
1-morphism from a stack representable by an affine scheme is again representable by an affine
scheme. -/
def HasAffineRepresentableBaseChange (c : 𝒰 ⟶ 𝒲) : Prop :=
  ∀ ⦃𝒯 : AlgebraicStacks.{u, w} B S hS⦄ (t : 𝒯 ⟶ 𝒲), IsAffineRepresentable B S hS 𝒯 →
    IsAffineRepresentable B S hS (twoFibreProductAlgebraicStack B S hS c t)

/-- A 1-morphism between stacks representable by affine schemes has affine base changes. -/
theorem hasAffineRepresentableBaseChange_of_isAffineRepresentable (c : 𝒰 ⟶ 𝒲)
    (hU : IsAffineRepresentable B S hS 𝒰) (hW : IsAffineRepresentable B S hS 𝒲) :
    HasAffineRepresentableBaseChange B S hS c :=
  fun _ t hT => isAffineRepresentable_twoFibreProductAlgebraicStack B S hS c t hU hW hT

/-- **Affine base changes are inherited along a fully faithful 1-morphism of the target.** If
`m : 𝒲 ⟶ 𝒬` is fully faithful and `c ≫ m` has affine base changes, then so does `c`. -/
theorem hasAffineRepresentableBaseChange_of_comp (c : 𝒰 ⟶ 𝒲) (m : 𝒲 ⟶ 𝒬)
    [(CatFiberedInGroupoids.homFunctor m.hom).Full]
    [(CatFiberedInGroupoids.homFunctor m.hom).Faithful]
    (h : HasAffineRepresentableBaseChange B S hS (c ≫ m)) :
    HasAffineRepresentableBaseChange B S hS c := by
  intro 𝒯 t hT
  have hcmp : (comparison B S hS c t m).hom.hom.toFunctor.IsEquivalence :=
    TwoFibreProductOver.isEquivalence_mapBase
      (CatFiberedInGroupoids.homFunctor_comp_p m.hom)
  exact isAffineRepresentable_of_isEquivalence_functor B S hS (comparison B S hS c t m) hcmp
    (h (t ≫ m) hT)

/-- The re-presented source of a 1-morphism out of a stack representable by an affine scheme is
representable by an affine scheme. -/
theorem isAffineRepresentable_rebasedSource (c : 𝒰 ⟶ 𝒲) (hU : IsAffineRepresentable B S hS 𝒰) :
    IsAffineRepresentable B S hS (rebasedSource B S hS c) :=
  isAffineRepresentable_of_equivalenceOver B S hS (rebasedSourceEquivalenceOver B S hS c) hU

/-- The degree `0` term of the Čech nerve of a 1-morphism is equivalent over the base to its
source. -/
def cechNerveZeroEquivalenceOver (c : 𝒰 ⟶ 𝒲) :
    StacksRepresentableCFG.EquivalenceOver (cechNerveStack B S hS c 0).val.val.p 𝒰.val.val.p :=
  (Stacks.RelativeCech.tupleZeroEquivalenceOver 𝒲.val.val.p
    (CatFiberedInGroupoids.homFunctor c.hom)).symm.trans (rebasedSourceEquivalenceOver B S hS c)

/-- **The terms of the Čech nerve of a 1-morphism with affine base changes, out of a stack
representable by an affine scheme, are representable by affine schemes.** -/
theorem isAffineRepresentable_cechNerveStack (c : 𝒰 ⟶ 𝒲) (hU : IsAffineRepresentable B S hS 𝒰)
    (hc : HasAffineRepresentableBaseChange B S hS (rebasedHom B S hS c)) :
    ∀ n, IsAffineRepresentable B S hS (cechNerveStack B S hS c n)
  | 0 => isAffineRepresentable_of_equivalenceOver B S hS (cechNerveZeroEquivalenceOver B S hS c) hU
  | n + 1 =>
    isAffineRepresentable_pt_of_isTwoFibreProduct B S hS
      (isTwoFibreProduct_cechNerveHeadTailSquare B S hS c n)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (rebasedHom B S hS c)
        (cechNerveStackProjection B S hS c n))
      (hc _ (isAffineRepresentable_cechNerveStack c hU hc n))

/-- A 1-morphism between stacks representable by affine schemes is quasi-compact. -/
theorem isQuasiCompactMorphism_of_isAffineRepresentable (g : 𝒰 ⟶ 𝒬)
    (hU : IsAffineRepresentable B S hS 𝒰) (hQ : IsAffineRepresentable B S hS 𝒬) :
    IsQuasiCompactMorphism B S hS g := by
  intro 𝒵 k h𝒵
  obtain ⟨V, a, hV, -, hasurj, -⟩ := exists_affine_smooth_surjective_of_isQuasiCompactStack
    B S hS 𝒵 h𝒵
  exact isQuasiCompactStack_twoFibreProduct_of_isSurjective_of_isSurjective B S hS k g a (𝟙 _)
    hasurj (isSurjective_id B S hS _) (isQuasiCompactStack_of_isAffineRepresentable B S hS
      (isAffineRepresentable_twoFibreProductAlgebraicStack B S hS (a ≫ k) (𝟙 _ ≫ g)
        (isAffineRepresentable_schemeStack.{u, w} B S hS V hV) hQ hU))

/-- **The terms of the Čech nerve of a quasi-compact 1-morphism out of a quasi-compact stack are
quasi-compact.** -/
theorem isQuasiCompactStack_cechNerveStack (c : 𝒰 ⟶ 𝒲)
    (hU : IsQuasiCompactStack B S hS 𝒰.val 𝒰.property)
    (hc : IsQuasiCompactMorphism B S hS (rebasedHom B S hS c)) :
    ∀ n, IsQuasiCompactStack B S hS (cechNerveStack B S hS c n).val
      (cechNerveStack B S hS c n).property
  | 0 => by
    let e := (cechNerveZeroEquivalenceOver B S hS c).symm
    have := e.isEquivalence_hom_functor
    let k : 𝒰 ⟶ cechNerveStack B S hS c 0 :=
      Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
        ⟨e.hom.functor, e.hom.w⟩)
    have : k.hom.hom.toFunctor.EssSurj := inferInstanceAs e.hom.functor.EssSurj
    exact isQuasiCompactStack_of_essSurj B S hS k hU
  | n + 1 =>
    isQuasiCompactStack_of_isTwoFibreProduct B S hS
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
          (cechNerveStackProjection B S hS c n) (rebasedHom B S hS c)))
      (isTwoFibreProduct_cechNerveHeadTailSquare B S hS c n)
      (hc _ (cechNerveStackProjection B S hS c n)
        (isQuasiCompactStack_cechNerveStack c hU hc n))

end AffineBaseChange

section Levels

/-- The re-presented chart of a 1-morphism `q` out of the source of `c`, with `q`
quasi-separated and `c`'s source and the target of `q` representable by affine schemes, is
quasi-compact. -/
private theorem isQuasiCompactMorphism_rebasedHom_of_isQuasiSeparated
    {𝒰 𝒲 𝒴 : AlgebraicStacks.{u, w} B S hS} (c : 𝒰 ⟶ 𝒲) (q : 𝒲 ⟶ 𝒴)
    (hU : IsAffineRepresentable B S hS 𝒰) (h𝒴 : IsAffineRepresentable B S hS 𝒴)
    (hqs : IsQuasiSeparated B S hS q) :
    IsQuasiCompactMorphism B S hS (rebasedHom B S hS c) :=
  isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS _ q
    (isQuasiCompactMorphism_of_isAffineRepresentable B S hS _
      (isAffineRepresentable_rebasedSource B S hS c hU) h𝒴) hqs

/-- **Level one.** A quasi-compact algebraic stack admitting a fully faithful 1-morphism to a
stack representable by an affine scheme is of Čech level `1`: the terms of the Čech nerve of a
smooth affine chart are representable by affine schemes. -/
theorem cechAffineLevel_one_of_full_faithful {𝒲 𝒬 : AlgebraicStacks.{u, w} B S hS}
    (h𝒲 : IsQuasiCompactStack B S hS 𝒲.val 𝒲.property) (m : 𝒲 ⟶ 𝒬)
    (hQ : IsAffineRepresentable B S hS 𝒬)
    [(CatFiberedInGroupoids.homFunctor m.hom).Full]
    [(CatFiberedInGroupoids.homFunctor m.hom).Faithful] :
    CechAffineLevel B S hS 1 𝒲 := by
  obtain ⟨A, c, hA, hsm, hsurj, hrep⟩ := exists_affine_smooth_surjective_of_isQuasiCompactStack
    B S hS 𝒲 h𝒲
  have hAr := isAffineRepresentable_schemeStack.{u, w} B S hS A hA
  refine ⟨_, c, hrep, hsurj, hsm, fun n => ?_⟩
  exact isAffineRepresentable_cechNerveStack B S hS c hAr
    (hasAffineRepresentableBaseChange_of_comp B S hS (rebasedHom B S hS c) m
      (hasAffineRepresentableBaseChange_of_isAffineRepresentable B S hS _
        (isAffineRepresentable_rebasedSource B S hS c hAr) hQ)) n

/-- **Level two.** A quasi-compact algebraic stack with a quasi-separated 1-morphism of faithful
underlying functor to a stack representable by an affine scheme is of Čech level `2`. -/
theorem cechAffineLevel_two_of_isQuasiSeparated {𝒲 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (h𝒲 : IsQuasiCompactStack B S hS 𝒲.val 𝒲.property) (q : 𝒲 ⟶ 𝒴)
    (h𝒴 : IsAffineRepresentable B S hS 𝒴) (hqs : IsQuasiSeparated B S hS q)
    [(CatFiberedInGroupoids.homFunctor q.hom).Faithful] :
    CechAffineLevel B S hS 2 𝒲 := by
  obtain ⟨A, c, hA, hsm, hsurj, hrep⟩ := exists_affine_smooth_surjective_of_isQuasiCompactStack
    B S hS 𝒲 h𝒲
  have hAr := isAffineRepresentable_schemeStack.{u, w} B S hS A hA
  have hc := isQuasiCompactMorphism_rebasedHom_of_isQuasiSeparated B S hS c q hAr h𝒴 hqs
  refine ⟨_, c, hrep, hsurj, hsm, fun n => ?_⟩
  have := full_cechNerveTargetMap B S hS c q n
  have := faithful_cechNerveTargetMap B S hS c q n
  exact cechAffineLevel_one_of_full_faithful B S hS
    (isQuasiCompactStack_cechNerveStack B S hS c
      (isQuasiCompactStack_of_isAffineRepresentable B S hS hAr) hc n)
    (cechNerveTargetMap B S hS c q n)
    (isAffineRepresentable_cechNerveStack B S hS (c ≫ q) hAr
      (hasAffineRepresentableBaseChange_of_isAffineRepresentable B S hS _
        (isAffineRepresentable_rebasedSource B S hS (c ≫ q) hAr) h𝒴) n)

/-- The composite of a projection of the Čech nerve of a 1-morphism from a stack representable by
an affine scheme with a quasi-separated 1-morphism to a stack representable by an affine scheme is
quasi-separated. -/
theorem isQuasiSeparated_cechNerveStackProjection_comp {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (c : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴) (hU : IsAffineRepresentable B S hS 𝒰)
    (h𝒴 : IsAffineRepresentable B S hS 𝒴) (hf : IsQuasiSeparated B S hS f) :
    ∀ n, IsQuasiSeparated B S hS (cechNerveStackProjection B S hS c n ≫ f) := by
  have hΔ := (isQuasiSeparatedOver_of_isAffineRepresentable B S hS h𝒴).2
  have hc : IsQuasiSeparated B S hS (rebasedHom B S hS c) :=
    isQuasiSeparated_of_isQuasiSeparated_comp B S hS _ f
      (isQuasiSeparated_of_isQuasiSeparatedOver B S hS _
        (isQuasiSeparatedOver_of_isAffineRepresentable B S hS
          (isAffineRepresentable_rebasedSource B S hS c hU)) hΔ) hf.2
  intro n
  induction n with
  | zero =>
    exact isQuasiSeparated_of_isQuasiSeparatedOver B S hS _
      (isQuasiSeparatedOver_of_isAffineRepresentable B S hS
        (isAffineRepresentable_of_equivalenceOver B S hS (cechNerveZeroEquivalenceOver B S hS c)
          hU)) hΔ
  | succ n ih =>
    rw [← cechNerveTail_comp_cechNerveStackProjection B S hS c n, Category.assoc]
    exact isQuasiSeparated_comp B S hS _ _
      (isQuasiSeparated_baseChange_of_isTwoFibreProduct B S hS (rebasedHom B S hS c)
        (cechNerveStackProjection B S hS c n) (cechNerveHeadTailSquare B S hS c n)
        (isTwoFibreProduct_cechNerveHeadTailSquare B S hS c n) hc) ih

/-- **A quasi-compact quasi-separated algebraic stack over a stack representable by an affine
scheme is of Čech level `3`.** -/
theorem cechAffineLevel_three_of_isQuasiCompactMorphism {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (h𝒴 : IsAffineRepresentable B S hS 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    CechAffineLevel B S hS 3 𝒳 := by
  have h𝒳 := isQuasiCompactStack_of_isQuasiCompactMorphism B S hS f hqc
    (isQuasiCompactStack_of_isAffineRepresentable B S hS h𝒴)
  obtain ⟨A, c, hA, hsm, hsurj, hrep⟩ := exists_affine_smooth_surjective_of_isQuasiCompactStack
    B S hS 𝒳 h𝒳
  have hAr := isAffineRepresentable_schemeStack.{u, w} B S hS A hA
  have hc := isQuasiCompactMorphism_rebasedHom_of_isQuasiSeparated B S hS c f hAr h𝒴 hqs
  refine ⟨_, c, hrep, hsurj, hsm, fun n => ?_⟩
  have hpA : (CatFiberedInGroupoids.homFunctor c.hom ⋙ 𝒳.val.val.p).Faithful :=
    faithful_p_of_isAffineRepresentable B S hS (isAffineRepresentable_rebasedSource B S hS c hAr)
  have hpn : ((cechNerveStack B S hS c n).val.val.p).Faithful :=
    Stacks.RelativeCech.Tuple.faithful_projection_comp _ _ n
  have : (CatFiberedInGroupoids.homFunctor
      (cechNerveStackProjection B S hS c n ≫ f).hom).Faithful := by
    rw [← CatFiberedInGroupoids.homFunctor_comp_p (cechNerveStackProjection B S hS c n ≫ f).hom]
      at hpn
    exact Functor.Faithful.of_comp _ 𝒴.val.val.p
  exact cechAffineLevel_two_of_isQuasiSeparated B S hS
    (isQuasiCompactStack_cechNerveStack B S hS c
      (isQuasiCompactStack_of_isAffineRepresentable B S hS hAr) hc n)
    (cechNerveStackProjection B S hS c n ≫ f) h𝒴
    (isQuasiSeparated_cechNerveStackProjection_comp B S hS c f hAr h𝒴 hqs n)

end Levels

end AlgebraicGeometry.Stack.AlgebraicStacks

end
