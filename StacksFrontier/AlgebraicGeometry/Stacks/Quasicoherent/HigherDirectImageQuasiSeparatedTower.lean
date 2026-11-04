module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismEquivalenceQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.HigherDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageAffineTower
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationUniversallyInjectiveCover

/-!
# The quasi-compact quasi-separated case of Stacks 076Z over an affine scheme

Let `M` be a rule satisfying hypotheses (1), (2) and (4) of **Stacks 076Z**. This file proves
that the higher direct images along a quasi-compact quasi-separated 1-morphism
`f : 𝒲 ⟶ (Sch/X)_fppf` into the stack of an affine scheme carry `M` into `M`, completing the
induction begun in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageAffineTower`.

The source improves the source of `f` along smooth charts by affine schemes, by the Čech step of
**Stacks 072G**. Sorted by the diagonal hypothesis, the two remaining steps are:

* *Charts with affine diagonal.* If `𝒲` is quasi-compact, `f` is quasi-separated, and every
  1-morphism from a stack representable by an affine scheme to `𝒲` has affine diagonal, then the
  terms `𝒰ₙ` of the relative Čech nerve of an affine chart are quasi-compact and their composites
  to `(Sch/X)_fppf` have affine diagonal: the projection `𝒰ₙ₊₁ ⟶ 𝒰ₙ` is a base change of the
  chart, and the diagonal of the chart is affine by assumption. This is the case of an algebraic
  space, which the source passes to schemes and then to separated schemes.
* *Quasi-compact quasi-separated.* For a quasi-compact quasi-separated `f`, the terms of the Čech
  nerve of an affine chart are fibred in setoids over the site, so their composites to
  `(Sch/X)_fppf` are representable by algebraic spaces (**Stacks 04Y5**) and quasi-separated; and
  every 1-morphism `d` from a stack representable by an affine scheme to such a term has affine
  diagonal, by **Stacks 0GQE**: `Δ_d` followed by the comparison to the diagonal of the composite
  to `(Sch/X)_fppf` is a 1-morphism between stacks representable by affine schemes, and the
  comparison is a base change of the relative diagonal of a monomorphism (**Stacks 04YQ (3)**),
  whose own diagonal is an equivalence (**Stacks 0AHJ**), hence affine. This is the passage from
  a stack to an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_hasAffineDiagonal_charts`
* `AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_isQuasiCompact_of_isQuasiSeparated`
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t

namespace Stacks.RelativeCech

variable {C : Type*} [Category C] {U : Type*} [Category U] {X : Type*} [Category X]

/-- **The terms of a relative Čech nerve are fibred in setoids when the covering is.** If
`f ⋙ p` is faithful, so is the structure functor `Uₙ ⥤ X ⥤ C` of each term: a morphism of
tuples is determined by its entries, each entry by its image in `C` (which is that of the
morphism of targets, the comparison isomorphisms being vertical), and the morphism of targets by
the first entry. -/
theorem Tuple.faithful_projection_comp_of_faithful (p : X ⥤ C) (f : U ⥤ X) [(f ⋙ p).Faithful]
    (n : ℕ) :
    (Tuple.projection p f n ⋙ p).Faithful where
  map_injective {a b} g h hgh := by
    have hgh' : p.map (Tuple.Hom.target g) = p.map (Tuple.Hom.target h) := hgh
    have hsrc : ∀ i, Tuple.Hom.source g i = Tuple.Hom.source h i := fun i => by
      apply (f ⋙ p).map_injective
      have eg : f.map (Tuple.Hom.source g i) =
          (a.comparison i).hom ≫ Tuple.Hom.target g ≫ (b.comparison i).inv := by
        rw [← Category.assoc, ← Tuple.Hom.comparison_naturality g i, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      have eh : f.map (Tuple.Hom.source h i) =
          (a.comparison i).hom ≫ Tuple.Hom.target h ≫ (b.comparison i).inv := by
        rw [← Category.assoc, ← Tuple.Hom.comparison_naturality h i, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      simp only [Functor.comp_map, eg, eh, Functor.map_comp, hgh']
    have htgt : Tuple.Hom.target g = Tuple.Hom.target h := by
      rw [← cancel_epi (a.comparison 0).hom, ← Tuple.Hom.comparison_naturality g 0,
        ← Tuple.Hom.comparison_naturality h 0, hsrc 0]
    exact Stacks.Cech.tupleHom_ext htgt (funext hsrc)

end Stacks.RelativeCech

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- A 1-morphism of algebraic stacks whose functor is an equivalence has a quasi-inverse over
the site (**Stacks 003Z (2)**), whose functor is again an equivalence. -/
theorem exists_quasiInverse {𝒜 𝒦 : AlgebraicStacks.{u, t} B S hS} (e : 𝒜 ⟶ 𝒦)
    (he : (CatFiberedInGroupoids.homFunctor e.hom).IsEquivalence) :
    ∃ j : 𝒦 ⟶ 𝒜, (CatFiberedInGroupoids.homFunctor j.hom).IsEquivalence ∧
      Nonempty (j ≫ e ≅ 𝟙 𝒦) := by
  obtain ⟨F, hF, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒜.val.val.p 𝒦.val.val.p
      𝒜.val.isFiberedInGroupoids 𝒦.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor e.hom) (CatFiberedInGroupoids.homFunctor_comp_p e.hom) he
  refine ⟨Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩),
    (CategoryTheory.Equivalence.mk (CatFiberedInGroupoids.homFunctor e.hom) F η.symm
      ε).isEquivalence_inverse, ⟨?_⟩⟩
  exact Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso ε hε))

/-- **Affine diagonal cancels against an equivalence on the left.** -/
theorem hasAffineDiagonal_of_isEquivalence_comp {𝒜 𝒦 𝒲 : AlgebraicStacks.{u, t} B S hS}
    (e : 𝒜 ⟶ 𝒦) (φ : 𝒦 ⟶ 𝒲) (he : (CatFiberedInGroupoids.homFunctor e.hom).IsEquivalence)
    (h : HasAffineDiagonal B S hS (e ≫ φ)) : HasAffineDiagonal B S hS φ := by
  obtain ⟨j, hj, ⟨hje⟩⟩ := exists_quasiInverse B S hS e he
  exact hasAffineDiagonal_of_equivalence B S hS (e ≫ φ) φ j.hom.hom
    (algStackHomHomIso B S hS ((Bicategory.associator j e φ).symm ≪≫
      Bicategory.whiskerRightIso hje φ ≪≫ Bicategory.leftUnitor φ)) hj h

/-- **Quasi-separatedness cancels against an equivalence on the left.** -/
theorem isQuasiSeparated_of_isEquivalence_comp {𝒜 𝒦 𝒲 : AlgebraicStacks.{u, t} B S hS}
    (e : 𝒜 ⟶ 𝒦) (φ : 𝒦 ⟶ 𝒲) (he : (CatFiberedInGroupoids.homFunctor e.hom).IsEquivalence)
    (h : IsQuasiSeparated B S hS (e ≫ φ)) : IsQuasiSeparated B S hS φ := by
  obtain ⟨j, hj, ⟨hje⟩⟩ := exists_quasiInverse B S hS e he
  exact isQuasiSeparated_of_equivalence B S hS (e ≫ φ) φ j.hom.hom
    (algStackHomHomIso B S hS ((Bicategory.associator j e φ).symm ≪≫
      Bicategory.whiskerRightIso hje φ ≪≫ Bicategory.leftUnitor φ)) hj h

/-- **A property passes along the relative Čech nerve.** Let `P` be a property of 1-morphisms of
algebraic stacks which cancels against an equivalence on the left, is stable under base change
and under composition. If `P` holds for `c : 𝒰 ⟶ 𝒳` (read on its strict presentation) and for
`c ≫ f`, then it holds for every composite `𝒰ₙ ⟶ 𝒳 ⟶ 𝒴` of a projection of the relative Čech
nerve of `c` with `f`: `𝒰₀` is equivalent to `𝒰`, and `𝒰ₙ₊₁` is equivalent to `𝒰 ×_𝒳 𝒰ₙ`, whose
projection to `𝒰ₙ` is a base change of `c` (**Stacks 06X3**). -/
theorem cechProjection_comp_induction
    (P : ∀ {𝒜 𝒦 : AlgebraicStacks.{u, t} B S hS}, (𝒜 ⟶ 𝒦) → Prop)
    (hcancel : ∀ {𝒜 𝒦 𝒲 : AlgebraicStacks.{u, t} B S hS} (e : 𝒜 ⟶ 𝒦) (φ : 𝒦 ⟶ 𝒲),
      (CatFiberedInGroupoids.homFunctor e.hom).IsEquivalence → P (e ≫ φ) → P φ)
    (hbc : ∀ {𝒜 𝒦 𝒦' : AlgebraicStacks.{u, t} B S hS} (a : 𝒜 ⟶ 𝒦) (b : 𝒦' ⟶ 𝒦),
      P a → P (twoFibreProductSquareAlgebraicStacks B S hS a b).snd)
    (hcomp : ∀ {𝒜 𝒦 𝒲 : AlgebraicStacks.{u, t} B S hS} (a : 𝒜 ⟶ 𝒦) (b : 𝒦 ⟶ 𝒲),
      P a → P b → P (a ≫ b))
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (c : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (hc : P (strictHom B S hS c)) (hcf : P (c ≫ f)) (n : ℕ) :
    P (cechProjection B S hS c n ≫ f) := by
  induction n with
  | zero =>
    exact hcancel (cechSingleHom B S hS c) _ (isEquivalence_cechTermSingle B S hS c) hcf
  | succ n ih =>
    have h := hcomp _ _ (hbc (strictHom B S hS c) (cechProjection B S hS c n) hc) ih
    exact hcancel (cechPrependHom B S hS c n) _
      (Stacks.RelativeCech.isEquivalence_fibreProductToNerve _ _ n) h

/-- **The terms of the relative Čech nerve of a quasi-compact 1-morphism out of a quasi-compact
algebraic stack are quasi-compact**: `𝒰₀ ≃ 𝒰`, and `𝒰ₙ₊₁ ≃ 𝒰 ×_𝒳 𝒰ₙ` is quasi-compact over `𝒰ₙ`
as a base change of `c`. -/
theorem isQuasiCompactStack_cechTerm {𝒰 𝒳 : AlgebraicStacks.{u, t} B S hS} (c : 𝒰 ⟶ 𝒳)
    (h𝒰 : IsQuasiCompactStack.{u, t} B S hS 𝒰.val 𝒰.property)
    (hc : IsQuasiCompactMorphism.{u, t} B S hS (strictHom B S hS c)) (n : ℕ) :
    IsQuasiCompactStack.{u, t} B S hS (cechTerm B S hS c n).val
      (cechTerm B S hS c n).property := by
  induction n with
  | zero =>
    have : (cechSingleHom B S hS c).hom.hom.toFunctor.IsEquivalence :=
      isEquivalence_cechTermSingle B S hS c
    exact isQuasiCompactStack_of_essSurj B S hS (cechSingleHom B S hS c) h𝒰
  | succ n ih =>
    have hsnd : IsQuasiCompactMorphism.{u, t} B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS (strictHom B S hS c)
          (cechProjection B S hS c n)).snd :=
      isQuasiCompactMorphism_baseChange B S hS (strictHom B S hS c) (cechProjection B S hS c n)
        (twoFibreProductSquareAlgebraicStacks B S hS _ _).swap
        (Bicategory.isTwoFibreProduct_swap
          (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _)) hc
    have hpt := isQuasiCompactStack_of_isQuasiCompactMorphism B S hS _ hsnd ih
    have : (cechPrependHom B S hS c n).hom.hom.toFunctor.IsEquivalence :=
      Stacks.RelativeCech.isEquivalence_fibreProductToNerve _ _ n
    exact isQuasiCompactStack_of_essSurj B S hS (cechPrependHom B S hS c n) hpt

/-- The terms of the relative Čech nerve of a 1-morphism out of a category fibred in setoids are
fibred in setoids. -/
theorem faithful_cechTerm_p {𝒰 𝒳 : AlgebraicStacks.{u, t} B S hS} (c : 𝒰 ⟶ 𝒳)
    (h𝒰 : 𝒰.val.val.p.Faithful) (n : ℕ) : (cechTerm B S hS c n).val.val.p.Faithful := by
  have : (CatFiberedInGroupoids.homFunctor c.hom ⋙ 𝒳.val.val.p).Faithful := by
    rw [CatFiberedInGroupoids.homFunctor_comp_p]
    exact h𝒰
  exact Stacks.RelativeCech.Tuple.faithful_projection_comp_of_faithful _ _ n

/-- The 2-fibre product of a 1-morphism between stacks representable by affine schemes with
itself is representable by an affine scheme: its projection to the source is a base change of
an affine 1-morphism (**Stacks 0CHR**). -/
theorem isAffineRepresentable_twoFibreProduct {𝒜 𝒦 : AlgebraicStacks.{u, t} B S hS}
    (h𝒜 : IsAffineRepresentable B S hS 𝒜) (h𝒦 : IsAffineRepresentable B S hS 𝒦) (k : 𝒜 ⟶ 𝒦) :
    IsAffineRepresentable B S hS (twoFibreProduct B S hS k k) :=
  isAffineRepresentable_of_isAffineHom B S hS h𝒜 _
    (isAffineHom_snd_of_isTwoFibreProduct B S hS (twoFibreProductSquare B S hS k k)
      (isTwoFibreProduct_twoFibreProductSquare B S hS k k)
      (isAffineHom_of_isAffineRepresentable B S hS h𝒜 h𝒦 k))

/-- **The relative diagonal of a 1-morphism between stacks representable by affine schemes is
affine**: it is a 1-morphism between stacks representable by affine schemes. -/
theorem isAffineHom_relativeDiagonal_of_isAffineRepresentable
    {𝒜 𝒦 : AlgebraicStacks.{u, t} B S hS} (h𝒜 : IsAffineRepresentable B S hS 𝒜)
    (h𝒦 : IsAffineRepresentable B S hS 𝒦) (k : 𝒜 ⟶ 𝒦) :
    IsAffineHom B S hS (relativeDiagonal B S hS k) :=
  isAffineHom_of_isAffineRepresentable B S hS h𝒜
    (isAffineRepresentable_twoFibreProduct B S hS h𝒜 h𝒦 k) _

/-- A 1-morphism between stacks representable by affine schemes has affine diagonal. -/
theorem hasAffineDiagonal_of_isAffineRepresentable {𝒜 𝒦 : AlgebraicStacks.{u, t} B S hS}
    (h𝒜 : IsAffineRepresentable B S hS 𝒜) (h𝒦 : IsAffineRepresentable B S hS 𝒦) (k : 𝒜 ⟶ 𝒦) :
    HasAffineDiagonal B S hS k :=
  (isAffineHom_relativeDiagonal_of_isAffineRepresentable B S hS h𝒜 h𝒦 k).2

/-- A 1-morphism between stacks representable by affine schemes is quasi-separated. -/
theorem isQuasiSeparated_of_isAffineRepresentable {𝒜 𝒦 : AlgebraicStacks.{u, t} B S hS}
    (h𝒜 : IsAffineRepresentable B S hS 𝒜) (h𝒦 : IsAffineRepresentable B S hS 𝒦) (k : 𝒜 ⟶ 𝒦) :
    IsQuasiSeparated B S hS k :=
  isQuasiSeparated_of_hasAffineDiagonal B S hS k
    (isAffineHom_of_isAffineRepresentable B S hS h𝒜 h𝒦 k).1
    (hasAffineDiagonal_of_isAffineRepresentable B S hS h𝒜 h𝒦 k)

/-- **A 1-morphism from a stack representable by an affine scheme into a source representable by
algebraic spaces over a stack representable by an affine scheme has affine diagonal.** Let
`d : 𝒰 ⟶ 𝒲` and `g : 𝒲 ⟶ 𝒵` with `𝒰`, `𝒵` representable by affine schemes and `g` representable
by algebraic spaces. Then `Δ_{d ≫ g} = Δ_d ≫ m` with `m : 𝒰 ×_𝒲 𝒰 ⟶ 𝒰 ×_𝒵 𝒰` the comparison
1-morphism, `Δ_{d ≫ g}` is affine as a 1-morphism between stacks representable by affine
schemes, and `m` is a base change of `Δ_g` (**Stacks 050H**), which is a monomorphism
(**Stacks 04YQ (3)**) and so has an equivalence for diagonal (**Stacks 0AHJ**), which is affine.
**Stacks 0GQE** concludes. -/
theorem hasAffineDiagonal_of_isRepresentableByAlgebraicSpaces_comp
    {𝒰 𝒲 𝒵 : AlgebraicStacks.{u, t} B S hS} (h𝒰 : IsAffineRepresentable B S hS 𝒰)
    (h𝒵 : IsAffineRepresentable B S hS 𝒵) (d : 𝒰 ⟶ 𝒲) (g : 𝒲 ⟶ 𝒵)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom) : HasAffineDiagonal B S hS d := by
  have hΔg : HasAffineDiagonal B S hS (relativeDiagonal B S hS g) :=
    Stack.isAffineHom_of_isEquivalence B S hS _
      ((isMonomorphism_iff_isEquivalence_relativeDiagonal B S hS
        (relativeDiagonalAlgebraicStacks B S hS g)).1
        (isMonomorphism_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS g hg))
  have hm : HasAffineDiagonal B S hS (mapBase B S hS d d g) :=
    hasAffineDiagonal_baseChange_of_isTwoFibreProduct B S hS (relativeDiagonal B S hS g)
      (mapCospan B S hS d d g) (mapBaseSquareStacks B S hS d g).swap
      (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_mapBaseSquareStacks B S hS d g)) hΔg
  exact (isAffineHom_of_comp_of_isAffineHom_relativeDiagonal B S hS (relativeDiagonal B S hS d)
    (relativeDiagonal B S hS (d ≫ g)) (mapBase B S hS d d g)
    (eqToIso (AlgebraicStacks.relativeDiagonal_comp B S hS d g))
    (isAffineHom_relativeDiagonal_of_isAffineRepresentable B S hS h𝒰 h𝒵 (d ≫ g)) hm).2

end AlgebraicStacks

namespace StackEtaleModuleRule

/-- **The case of charts with affine diagonal.** Let `M` satisfy hypotheses (1), (2) and (4) of
**Stacks 076Z** and let `f : 𝒲 ⟶ (Sch/X)_fppf` be a quasi-separated 1-morphism from a
quasi-compact algebraic stack into the stack of an affine scheme, such that every 1-morphism to
(the strict presentation of) `𝒲` from a stack representable by an affine scheme has affine
diagonal. Then the higher direct images along `f` carry `M` into `M`.

Take a smooth surjective chart `c` by an affine scheme (**Stacks 04YC**). It is quasi-compact,
its composite to `(Sch/X)_fppf` being affine and `f` quasi-separated (**Stacks 050Y**), so the
terms of its relative Čech nerve are quasi-compact; and their composites to `(Sch/X)_fppf` have
affine diagonal, by `AlgebraicGeometry.Stack.AlgebraicStacks.cechProjection_comp_induction`, from
the affine diagonal of `c` and of its composite to `(Sch/X)_fppf`.
`AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_hasAffineDiagonal` treats each term
and the Čech step concludes. -/
theorem preservedBy_of_hasAffineDiagonal_charts (M : StackEtaleModuleRule B S hS)
    (hserre : IsWeakSerre.{u, t} B S hS M)
    (hpull : IsStableUnderSmoothPullback.{u, t} B S hS M)
    (haff : PreservesHigherDirectImagesOfAffine.{u, t} B S hS M)
    {𝒲 : AlgebraicStacks.{u, t} B S hS} {X : BigFppfOver B S hS}
    (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (f : 𝒲 ⟶ schemeStack.{u, t} B S hS X)
    (h𝒲 : IsQuasiCompactStack.{u, t} B S hS 𝒲.val 𝒲.property)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (hD : ∀ {𝒰 : AlgebraicStacks.{u, t} B S hS}, AlgebraicStacks.IsAffineRepresentable B S hS 𝒰 →
      ∀ d : 𝒰 ⟶ AlgebraicStacks.strictSource B S hS f, AlgebraicStacks.HasAffineDiagonal B S hS d)
    (i : ℕ) : PreservedBy B S hS M f i := by
  obtain ⟨U, hU, c, hrep, hsurj, hsm⟩ := AlgebraicStacks.exists_affineChart B S hS 𝒲 h𝒲
  have hUa := AlgebraicStacks.isAffineRepresentable_schemeStack_of_isAffine B S hS hU
  have hXa := AlgebraicStacks.isAffineRepresentable_schemeStack_of_isAffine B S hS hX
  have hU' : AlgebraicStacks.IsAffineRepresentable B S hS
      (AlgebraicStacks.strictSource B S hS (strictChart B S hS c f)) :=
    (AlgebraicStacks.isAffineRepresentable_iff_of_isEquivalence B S hS
      (AlgebraicStacks.strictSourceEquiv B S hS (strictChart B S hS c f))
      (inferInstanceAs (𝟭 _).IsEquivalence)).2 hUa
  have hfqs : AlgebraicStacks.IsQuasiSeparated B S hS (AlgebraicStacks.strictHom B S hS f) :=
    AlgebraicStacks.isQuasiSeparated_of_equivalence B S hS f (AlgebraicStacks.strictHom B S hS f)
      (AlgebraicStacks.strictSourceEquiv B S hS f).hom.hom
      (algStackHomHomIso B S hS (Iso.refl (AlgebraicStacks.strictSourceEquiv B S hS f ≫ f)))
      (inferInstanceAs (𝟭 _).IsEquivalence) hqs
  have hcqc : IsQuasiCompactMorphism.{u, t} B S hS
      (AlgebraicStacks.strictHom B S hS (strictChart B S hS c f)) :=
    isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS _
      (AlgebraicStacks.strictHom B S hS f)
      (AlgebraicStacks.isQuasiCompactMorphism_of_isAffineHom B S hS _
        (AlgebraicStacks.isAffineHom_of_isAffineRepresentable B S hS hU' hXa _)) hfqs
  refine preservedBy_of_cechTerms B S hS c f M hserre hpull hrep hsurj hsm (fun n j => ?_) i
  exact preservedBy_of_hasAffineDiagonal B S hS M hserre hpull haff hX _
    (AlgebraicStacks.isQuasiCompactStack_cechTerm B S hS _
      (isQuasiCompactStack_schemeStack_of_isAffine.{u, t} B S hS U hU) hcqc n)
    (AlgebraicStacks.cechProjection_comp_induction B S hS
      (fun φ => AlgebraicStacks.HasAffineDiagonal B S hS φ)
      (fun e φ he h => AlgebraicStacks.hasAffineDiagonal_of_isEquivalence_comp B S hS e φ he h)
      (fun a b h => AlgebraicStacks.hasAffineDiagonal_baseChange_of_isTwoFibreProduct B S hS a b
        _ (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a b) h)
      (fun a b ha hb => AlgebraicStacks.hasAffineDiagonal_comp B S hS a b ha hb) _
      (AlgebraicStacks.strictHom B S hS f)
      (AlgebraicStacks.hasAffineDiagonal_strictHom B S hS _ (hD hUa _))
      (AlgebraicStacks.hasAffineDiagonal_of_isAffineRepresentable B S hS hUa hXa _) n) j

/-- **The quasi-compact quasi-separated case of Stacks 076Z over an affine scheme.** Let `M`
satisfy hypotheses (1), (2) and (4) of **Stacks 076Z** and let `f : 𝒲 ⟶ (Sch/X)_fppf` be a
quasi-compact quasi-separated 1-morphism into the stack of an affine scheme. Then the higher
direct images along `f` carry `M` into `M`.

The source `𝒲` is quasi-compact; take a smooth surjective chart `c` by an affine scheme
(**Stacks 04YC**). The terms `𝒰ₙ` of its relative Čech nerve are quasi-compact, fibred in
setoids over the site, and quasi-separated over `(Sch/X)_fppf`; their composites to
`(Sch/X)_fppf` are therefore representable by algebraic spaces (**Stacks 04Y5**), so every
1-morphism into `𝒰ₙ` from a stack representable by an affine scheme has affine diagonal
(`AlgebraicStacks.hasAffineDiagonal_of_isRepresentableByAlgebraicSpaces_comp`).
`AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_hasAffineDiagonal_charts` treats
each term and the Čech step concludes. -/
theorem preservedBy_of_isQuasiCompact_of_isQuasiSeparated (M : StackEtaleModuleRule B S hS)
    (hserre : IsWeakSerre.{u, t} B S hS M)
    (hpull : IsStableUnderSmoothPullback.{u, t} B S hS M)
    (haff : PreservesHigherDirectImagesOfAffine.{u, t} B S hS M)
    {𝒲 : AlgebraicStacks.{u, t} B S hS} {X : BigFppfOver B S hS}
    (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (f : 𝒲 ⟶ schemeStack.{u, t} B S hS X) (hqc : IsQuasiCompactMorphism.{u, t} B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f) (i : ℕ) : PreservedBy B S hS M f i := by
  have h𝒲 := isQuasiCompactStack_of_isQuasiCompactMorphism B S hS f hqc
    (isQuasiCompactStack_schemeStack_of_isAffine.{u, t} B S hS X hX)
  obtain ⟨U, hU, c, hrep, hsurj, hsm⟩ := AlgebraicStacks.exists_affineChart B S hS 𝒲 h𝒲
  have hUa := AlgebraicStacks.isAffineRepresentable_schemeStack_of_isAffine B S hS hU
  have hXa := AlgebraicStacks.isAffineRepresentable_schemeStack_of_isAffine B S hS hX
  have hU' : AlgebraicStacks.IsAffineRepresentable B S hS
      (AlgebraicStacks.strictSource B S hS (strictChart B S hS c f)) :=
    (AlgebraicStacks.isAffineRepresentable_iff_of_isEquivalence B S hS
      (AlgebraicStacks.strictSourceEquiv B S hS (strictChart B S hS c f))
      (inferInstanceAs (𝟭 _).IsEquivalence)).2 hUa
  have hfqs : AlgebraicStacks.IsQuasiSeparated B S hS (AlgebraicStacks.strictHom B S hS f) :=
    AlgebraicStacks.isQuasiSeparated_of_equivalence B S hS f (AlgebraicStacks.strictHom B S hS f)
      (AlgebraicStacks.strictSourceEquiv B S hS f).hom.hom
      (algStackHomHomIso B S hS (Iso.refl (AlgebraicStacks.strictSourceEquiv B S hS f ≫ f)))
      (inferInstanceAs (𝟭 _).IsEquivalence) hqs
  have hcqc : IsQuasiCompactMorphism.{u, t} B S hS
      (AlgebraicStacks.strictHom B S hS (strictChart B S hS c f)) :=
    isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS _
      (AlgebraicStacks.strictHom B S hS f)
      (AlgebraicStacks.isQuasiCompactMorphism_of_isAffineHom B S hS _
        (AlgebraicStacks.isAffineHom_of_isAffineRepresentable B S hS hU' hXa _)) hfqs
  have hcqs : AlgebraicStacks.IsQuasiSeparated B S hS
      (AlgebraicStacks.strictHom B S hS (strictChart B S hS c f)) :=
    AlgebraicStacks.isQuasiSeparated_of_comp_of_isQuasiSeparated_diagonal B S hS _
      (AlgebraicStacks.strictHom B S hS f)
      (AlgebraicStacks.isQuasiSeparated_of_isAffineRepresentable B S hS hU' hXa _) hfqs.2
  have hUp : (schemeStack.{u, t} B S hS U).val.val.p.Faithful :=
    inferInstanceAs (Over.forget _).Faithful
  refine preservedBy_of_cechTerms B S hS c f M hserre hpull hrep hsurj hsm (fun n j => ?_) i
  have hgqs : AlgebraicStacks.IsQuasiSeparated B S hS
      (AlgebraicStacks.cechProjection B S hS (strictChart B S hS c f) n ≫
        AlgebraicStacks.strictHom B S hS f) :=
    AlgebraicStacks.cechProjection_comp_induction B S hS
      (fun φ => AlgebraicStacks.IsQuasiSeparated B S hS φ)
      (fun e φ he h => AlgebraicStacks.isQuasiSeparated_of_isEquivalence_comp B S hS e φ he h)
      (fun a b h => AlgebraicStacks.isQuasiSeparated_baseChange_of_isTwoFibreProduct B S hS a b
        _ (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a b) h)
      (fun a b ha hb => AlgebraicStacks.isQuasiSeparated_comp B S hS a b ha hb) _
      (AlgebraicStacks.strictHom B S hS f) hcqs
      (AlgebraicStacks.isQuasiSeparated_of_isAffineRepresentable B S hS hUa hXa _) n
  have hfaith := AlgebraicStacks.faithful_cechTerm_p B S hS (strictChart B S hS c f) hUp n
  have hgfaith : (CatFiberedInGroupoids.homFunctor (AlgebraicStacks.strictHom B S hS
      (AlgebraicStacks.cechProjection B S hS (strictChart B S hS c f) n ≫
        AlgebraicStacks.strictHom B S hS f)).hom).Faithful := by
    have : (CatFiberedInGroupoids.homFunctor (AlgebraicStacks.strictHom B S hS
        (AlgebraicStacks.cechProjection B S hS (strictChart B S hS c f) n ≫
          AlgebraicStacks.strictHom B S hS f)).hom ⋙
        (schemeStack.{u, t} B S hS X).val.val.p).Faithful := hfaith
    exact Functor.Faithful.of_comp _ (schemeStack.{u, t} B S hS X).val.val.p
  exact preservedBy_of_hasAffineDiagonal_charts B S hS M hserre hpull haff hX _
    (AlgebraicStacks.isQuasiCompactStack_cechTerm B S hS _
      (isQuasiCompactStack_schemeStack_of_isAffine.{u, t} B S hS U hU) hcqc n) hgqs
    (fun h𝒰 d => AlgebraicStacks.hasAffineDiagonal_of_isRepresentableByAlgebraicSpaces_comp
      B S hS h𝒰 hXa d _
      (AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful B S hS _ hgfaith)) j

end StackEtaleModuleRule

end AlgebraicGeometry.Stack

end
