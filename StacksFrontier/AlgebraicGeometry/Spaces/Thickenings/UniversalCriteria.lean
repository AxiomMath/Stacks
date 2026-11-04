module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedThickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Universal

/-!
# Testing the universal first-order thickening on scheme-valued and affine thickenings

Let `h : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S`, presented as a first-order
thickening `Z ⊂ Z'` together with `p : Z' ⟶ X`. The universal lifting property of Stacks 0602
quantifies over *all* first-order thickenings `T ⊂ T'` of algebraic spaces over `X`; this file
shows that it is enough to test it on those whose ambient space `T'` is a scheme, and in fact
already on those whose ambient space is an affine scheme.

## Main results

* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_iff_representable`:
  **Stacks 0603**, the equivalence of (1) and (2).
* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_iff_affine_lifting`:
  **Stacks 0603**, the equivalence of (1) and (3).

## Implementation notes

A scheme over the base is an algebraic space whose functor of points is representable by an
object of the chosen big fppf site, so condition (2) is the lifting property restricted to
`CategoryTheory.Functor.IsRepresentable` ambient spaces, and condition (3) is the lifting
property restricted to the ambient spaces satisfying
`AlgebraicGeometry.Space.IsAffineSpace`, which pins an affine scheme object only up to
isomorphism and so does not depend on a chosen presentation. The first-order condition on the
given inclusion `Z ⊂ Z'` is implied by neither, and so is carried as a hypothesis, as in the
source.

Both reductions descend a lift along a surjective étale atlas `U ⟶ T'`. The inverse image of
the thickening along any étale morphism is again a first-order thickening, because the defining
ideal of an inverse image along an étale morphism is, on every étale chart of the source, the
defining ideal of the original closed subspace on the composed chart. So conditions (2) and (3)
both give a solution of the lifting problem over the atlas; the two restrictions of that
solution to the kernel pair `R = U ×_{T'} U` solve one and the same lifting problem over `R`,
hence agree, and an atlas presents an algebraic space as the coequalizer of its kernel pair in
fppf sheaves (Stacks 0262, part (3)), so the solution descends. That the descended arrow
restricts to the given `a : T ⟶ Z` is checked after the surjective étale cover of `T` obtained
by base-changing the atlas along the inclusion of `T`.

Condition (3) is weaker than condition (2) in two ways, and both are bridged over the affine
opens of the test object: the solution over an étale chart `W` of `T'` is assembled from the
solutions over the affine opens of `W`, whose pairwise intersections are again étale over `T'`
and carry a unique solution, and the fppf sheaf condition of `Z'` glues the local solutions.
That the glued arrow restricts to the given one is an equality of arrows out of the smaller
space of the thickening, which is not representable; it is therefore read through the cartesian
square `AlgebraicGeometry.Space.exists_nthOrderThickening_chart_pullback` provides over the
chart, whose source is an object of the site, and tested on the covering sieve the affine opens
pull back to.

## References

* [Stacks Project, Tag 0603](https://stacks.math.columbia.edu/tag/0603)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse image of an `n`th-order thickening along an étale morphism of algebraic spaces
is an `n`th-order thickening: on an étale chart `V` of the source the defining ideal of the
inverse image is the defining ideal of the original closed subspace on the étale chart of the
target obtained by composing `V` with the morphism. -/
private theorem isNthOrderThickening_preimage_of_etale {n : ℕ} {X Y : AlgebraicSpaces B S hS}
    (f : Y.1 ⟶ X.1)
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (G : Subfunctor X.1) (hG : IsNthOrderThickening B S hS n X G) :
    IsNthOrderThickening B S hS n Y (G.preimage f) := by
  obtain ⟨hthick, hpow⟩ := hG
  refine ⟨isThickening_preimage B S hS G (ObjectProperty.homMk f : Y ⟶ X) hthick, fun V ↦ ?_⟩
  have hmul := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
  let W : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (V.1.hom ≫ f), MorphismProperty.comp_mem _ _ _ V.2 hf⟩
  have key := definingIdealAt_preimage B S hS (ObjectProperty.homMk f : Y ⟶ X) ⟨G, hthick.1⟩ V
  have key2 := definingIdealAt_eq_ker B S hS X ⟨G, hthick.1⟩ W
  exact (congrArg (· ^ (n + 1)) (key.trans key2.symm)).trans (hpow W)

/-- The inverse image of a first-order thickening along an étale morphism of algebraic spaces
is a first-order thickening. -/
private theorem isFirstOrderThickening_preimage_of_etale {X Y : AlgebraicSpaces B S hS}
    (f : Y.1 ⟶ X.1)
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (G : Subfunctor X.1) (hG : IsFirstOrderThickening B S hS X G) :
    IsFirstOrderThickening B S hS Y (G.preimage f) :=
  isNthOrderThickening_preimage_of_etale B S hS f hf G hG


/-- The étale charts of an algebraic space are closed under composition with a morphism of the
site which is étale on underlying schemes. -/
private theorem presheaf_etale_yoneda_map_comp {T' : AlgebraicSpaces B S hS}
    {V W : BigFppfOver B S hS} (j : V ⟶ W)
    (hj : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map j))
    (m : yoneda.obj W ⟶ T'.1)
    (hm : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) m) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map j ≫ m) := by
  have hmul := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
  exact MorphismProperty.comp_mem _ _ _
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ j).2 hj) hm

/-- **A solution restricts.** A dotted arrow over a chart `m` of the ambient space of a
thickening restricts, along any morphism `n` into the source of `m`, to a dotted arrow over
the chart `n ≫ m`. -/
private theorem lift_cond_restrict
    {X Z' T' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1) (p : Z' ⟶ X)
    (T : Subfunctor T'.1) (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    {A A' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : A ⟶ T'.1) (n : A' ⟶ A) (c : A ⟶ Z'.1)
    (hc1 : (T.preimage m).ι ≫ c = T.fromPreimage m ≫ a ≫ Z.ι)
    (hc2 : c ≫ p.hom = m ≫ b) :
    (T.preimage (n ≫ m)).ι ≫ (n ≫ c) = T.fromPreimage (n ≫ m) ≫ a ≫ Z.ι ∧
      (n ≫ c) ≫ p.hom = (n ≫ m) ≫ b := by
  refine ⟨?_, by rw [Category.assoc, hc2, Category.assoc]⟩
  have hsq : T.fromPreimage (n ≫ m) ≫ T.ι = ((T.preimage (n ≫ m)).ι ≫ n) ≫ m := by
    rw [Subfunctor.fromPreimage_ι, Category.assoc]
  have hpb := Subfunctor.isPullback_preimage m T
  obtain ⟨ψ, h1, h2⟩ : ∃ ψ : (T.preimage (n ≫ m)).toFunctor ⟶ (T.preimage m).toFunctor,
      ψ ≫ T.fromPreimage m = T.fromPreimage (n ≫ m) ∧
        ψ ≫ (T.preimage m).ι = (T.preimage (n ≫ m)).ι ≫ n :=
    ⟨hpb.lift _ _ hsq, hpb.lift_fst _ _ hsq, hpb.lift_snd _ _ hsq⟩
  calc (T.preimage (n ≫ m)).ι ≫ n ≫ c
      = ((T.preimage (n ≫ m)).ι ≫ n) ≫ c := by rw [Category.assoc]
    _ = (ψ ≫ (T.preimage m).ι) ≫ c := by rw [h2]
    _ = ψ ≫ ((T.preimage m).ι ≫ c) := by rw [Category.assoc]
    _ = ψ ≫ (T.fromPreimage m ≫ a ≫ Z.ι) := by rw [hc1]
    _ = (ψ ≫ T.fromPreimage m) ≫ a ≫ Z.ι := by rw [Category.assoc]
    _ = T.fromPreimage (n ≫ m) ≫ a ≫ Z.ι := by rw [h1]

/-- A commuting square for a thickening restricts to a commuting square over any chart `m` of
its ambient space. -/
private theorem lift_comm_restrict
    {X Z' T' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1) (p : Z' ⟶ X)
    (T : Subfunctor T'.1) (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    (comm : T.ι ≫ b = a ≫ Z.ι ≫ p.hom) {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : A ⟶ T'.1) :
    (T.preimage m).ι ≫ m ≫ b = (T.fromPreimage m ≫ a) ≫ Z.ι ≫ p.hom := by
  rw [← Category.assoc _ m b, ← Subfunctor.fromPreimage_ι, Category.assoc _ T.ι b, comm,
    ← Category.assoc]

/-- **Descent along an atlas.** For a surjective étale atlas `f : U ⟶ T'` of an algebraic space
and an fppf sheaf `Y`, arrows `T' ⟶ Y` are determined by their composite with `f`, and every
arrow `U ⟶ Y` which agrees on the two projections of any kernel pair of `f` comes from one. -/
private theorem atlas_descent {T' : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ T'.1)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) :
    (∀ c d : T'.1 ⟶ Y, f ≫ c = f ≫ d → c = d) ∧
      ∀ l : yoneda.obj U ⟶ Y, (∀ {R : BigFppfOver B S hS} (s t : R ⟶ U),
        IsPullback (yoneda.map s) (yoneda.map t) f f → yoneda.map s ≫ l = yoneda.map t ≫ l) →
      ∃ c : T'.1 ⟶ Y, f ≫ c = l := by
  classical
  let _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let hrel : yoneda.relativelyRepresentable f :=
    Functor.relativelyRepresentable.of_diag T'.property.diagonal_representable f
  let s := hrel.snd f
  let t := yoneda.preimage (hrel.fst f)
  have hR : IsPullback (yoneda.map s) (yoneda.map t) f f := by
    simpa [s, t, yoneda.map_preimage] using (hrel.isPullback f).flip
  obtain ⟨hRsh, hUsh, hcoeq⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS f s t hR T'.property hsurj hetale
  let J := BigFppfOver.topology B S hS
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
  let TF : Sheaf J (Type u) := ⟨T'.1, T'.property.isSheaf⟩
  let YF : Sheaf J (Type u) := ⟨Y, hY⟩
  let RF : Sheaf J (Type u) := ⟨yoneda.obj (hrel.pullback f), hRsh⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let ff : UF ⟶ TF := ⟨f⟩
  have hcol := Classical.choice hcoeq
  refine ⟨fun c d h ↦ ?_, fun l hl ↦ ?_⟩
  · have : Epi ff := Cofork.IsColimit.epi hcol
    have h' : ff ≫ (⟨c⟩ : TF ⟶ YF) = ff ≫ ⟨d⟩ := Sheaf.hom_ext h
    exact Sheaf.hom_ext_iff.mp ((cancel_epi ff).1 h')
  · let lF : UF ⟶ YF := ⟨l⟩
    have hl' : sf ≫ lF = tf ≫ lF := Sheaf.hom_ext (hl s t hR)
    let cZ : Cofork sf tf := Cofork.ofπ lF hl'
    exact ⟨(hcol.desc cZ).hom, congrArg (fun k => k.hom) (hcol.fac cZ WalkingParallelPair.one)⟩

/-- **Descent of the dotted arrow of Stacks 0602 along an atlas.** If the lifting problem has a
unique solution over every étale chart of the ambient space, it has a unique solution: the
solution over a surjective étale atlas is invariant under the kernel pair, hence descends. -/
private theorem lift_existsUnique_of_chart_lifting
    {X Z' T' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1) (p : Z' ⟶ X)
    (T : Subfunctor T'.1) (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    (hchart : ∀ {W : BigFppfOver B S hS} (m : yoneda.obj W ⟶ T'.1),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) m →
      ∃! c : yoneda.obj W ⟶ Z'.1,
        (T.preimage m).ι ≫ c = T.fromPreimage m ≫ a ≫ Z.ι ∧ c ≫ p.hom = m ≫ b) :
    ∃! c : T'.1 ⟶ Z'.1, (T.ι ≫ c = a ≫ Z.ι) ∧ (c ≫ p.hom = b) := by
  obtain ⟨U, f, hsurj, hetale⟩ := T'.property.exists_atlas
  obtain ⟨l, hl1, hl2⟩ := (hchart f hetale).exists
  have hZ := atlas_descent B S hS f hsurj hetale Z'.property.isSheaf
  obtain ⟨c, hc⟩ := hZ.2 l fun s t hR ↦ by
    have hgEtale := presheaf_etale_yoneda_map_comp B S hS s
      (hetale.property f (yoneda.map t) s hR.flip) f hetale
    obtain ⟨hs1, hs2⟩ := lift_cond_restrict B S hS Z p T a b f (yoneda.map s) l hl1 hl2
    obtain ⟨ht1, ht2⟩ := lift_cond_restrict B S hS Z p T a b f (yoneda.map t) l hl1 hl2
    rw [← hR.w] at ht1 ht2
    exact (hchart _ hgEtale).unique ⟨hs1, hs2⟩ ⟨ht1, ht2⟩
  have hZX := atlas_descent B S hS f hsurj hetale X.property.isSheaf
  have hdown : c ≫ p.hom = b :=
    hZX.1 _ _ (by rw [← Category.assoc, hc, hl2])
  refine ⟨c, ⟨?_, hdown⟩, fun d hd ↦ hZ.1 _ _ ?_⟩
  · let J := BigFppfOver.topology B S hS
    let hTU := isFirstOrderThickening_preimage_of_etale B S hS (X := T')
      (Y := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) f hetale T hT
    let hTClosed : IsClosedSubspace B S hS T := hT.choose.1
    let hTUClosed : IsClosedSubspace B S hS (T.preimage f) := hTU.choose.1
    let qSh : (⟨(T.preimage f).toFunctor, hTUClosed.1.isSheaf⟩ : Sheaf J (Type u)) ⟶
        ⟨T.toFunctor, hTClosed.1.isSheaf⟩ := ⟨T.fromPreimage f⟩
    have : Sheaf.IsLocallySurjective qSh := isLocallySurjective_of_surjective_etale B S hS
      (T.fromPreimage f)
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (Subfunctor.isPullback_preimage f T).flip hsurj)
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (Subfunctor.isPullback_preimage f T).flip hetale)
    have : Epi qSh := inferInstance
    let ZF : Sheaf J (Type u) := ⟨Z'.1, Z'.property.isSheaf⟩
    have h' : qSh ≫ (⟨T.ι ≫ c⟩ : _ ⟶ ZF) = qSh ≫ ⟨a ≫ Z.ι⟩ := by
      apply Sheaf.hom_ext
      change T.fromPreimage f ≫ T.ι ≫ c = T.fromPreimage f ≫ a ≫ Z.ι
      rw [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc, hc, hl1]
    exact Sheaf.hom_ext_iff.mp ((cancel_epi qSh).1 h')
  · have hd' := (hchart f hetale).unique (y₁ := f ≫ d)
      ⟨by rw [← Category.assoc _ f d, ← Subfunctor.fromPreimage_ι, Category.assoc, hd.1],
        by rw [Category.assoc, hd.2]⟩ ⟨hl1, hl2⟩
    rw [hd', hc]

/-- **Unique dotted arrow over an étale chart, from the scheme-valued case.** Granted the lifting
property for thickenings whose ambient space is representable, the lifting problem restricted to
an étale chart of the ambient space has a unique solution, because the inverse image of the
thickening along the chart is a first-order thickening of a representable algebraic space. -/
private theorem lift_chart_existsUnique_of_scheme_lifting
    {X Z' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1) (p : Z' ⟶ X)
    (h : ∀ {T' : AlgebraicSpaces B S hS}
      (_hT' : T'.1.IsRepresentable) (T : Subfunctor T'.1),
      IsFirstOrderThickening B S hS T' T →
      ∀ (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1),
        T.ι ≫ b = a ≫ Z.ι ≫ p.hom →
        ∃! c : T'.1 ⟶ Z'.1, (T.ι ≫ c = a ≫ Z.ι) ∧ (c ≫ p.hom = b))
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.1)
    (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    (comm : T.ι ≫ b = a ≫ Z.ι ≫ p.hom)
    {W : BigFppfOver B S hS} (m : yoneda.obj W ⟶ T'.1)
    (hm : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) m) :
    ∃! c : yoneda.obj W ⟶ Z'.1,
      (T.preimage m).ι ≫ c = T.fromPreimage m ≫ a ≫ Z.ι ∧ c ≫ p.hom = m ≫ b := by
  simpa only [Category.assoc] using
    h (T' := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩) inferInstance (T.preimage m)
      (isFirstOrderThickening_preimage_of_etale B S hS
        (Y := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩) m hm T hT)
      (T.fromPreimage m ≫ a) (m ≫ b) (lift_comm_restrict B S hS Z p T a b comm m)

/-- **Existence of the dotted arrow of Stacks 0602 from the scheme-valued case.** Granted the
lifting property for thickenings whose ambient space is representable, every solid diagram
over a first-order thickening of algebraic spaces admits a dotted arrow. -/
private theorem lift_exists_of_scheme_lifting
    {X Z' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1) (p : Z' ⟶ X)
    (h : ∀ {T' : AlgebraicSpaces B S hS}
      (_hT' : T'.1.IsRepresentable) (T : Subfunctor T'.1),
      IsFirstOrderThickening B S hS T' T →
      ∀ (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1),
        T.ι ≫ b = a ≫ Z.ι ≫ p.hom →
        ∃! c : T'.1 ⟶ Z'.1, (T.ι ≫ c = a ≫ Z.ι) ∧ (c ≫ p.hom = b))
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.1)
    (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    (comm : T.ι ≫ b = a ≫ Z.ι ≫ p.hom) :
    ∃ c : T'.1 ⟶ Z'.1, (T.ι ≫ c = a ≫ Z.ι) ∧ (c ≫ p.hom = b) :=
  (lift_existsUnique_of_chart_lifting B S hS Z p T hT a b
    (lift_chart_existsUnique_of_scheme_lifting B S hS Z p h T hT a b comm)).exists

/-- **Uniqueness of the dotted arrow of Stacks 0602 from the scheme-valued case.** Granted the
lifting property for thickenings whose ambient space is representable, two dotted arrows of
one solid diagram agree. -/
private theorem lift_unique_of_scheme_lifting
    {X Z' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1) (p : Z' ⟶ X)
    (h : ∀ {T' : AlgebraicSpaces B S hS}
      (_hT' : T'.1.IsRepresentable) (T : Subfunctor T'.1),
      IsFirstOrderThickening B S hS T' T →
      ∀ (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1),
        T.ι ≫ b = a ≫ Z.ι ≫ p.hom →
        ∃! c : T'.1 ⟶ Z'.1, (T.ι ≫ c = a ≫ Z.ι) ∧ (c ≫ p.hom = b))
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.1)
    (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    (comm : T.ι ≫ b = a ≫ Z.ι ≫ p.hom)
    (c d : T'.1 ⟶ Z'.1)
    (hc : (T.ι ≫ c = a ≫ Z.ι) ∧ (c ≫ p.hom = b))
    (hd : (T.ι ≫ d = a ≫ Z.ι) ∧ (d ≫ p.hom = b)) : c = d :=
  (lift_existsUnique_of_chart_lifting B S hS Z p T hT a b
    (lift_chart_existsUnique_of_scheme_lifting B S hS Z p h T hT a b comm)).unique hc hd

/-! ### Testing on affine thickenings -/

/-- **A chart through the smaller space.** The inverse image of a closed subspace along a
chart which factors through its inclusion is everything, so a dotted arrow over such a chart
is determined: it is the factorisation composed with the given arrow out of the subspace. -/
private theorem lift_cond_of_factors {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.1)
    {A Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (n : A ⟶ T.toFunctor) (φ : A ⟶ Y)
    (α : T.toFunctor ⟶ Y)
    (H : (T.preimage (n ≫ T.ι)).ι ≫ φ = T.fromPreimage (n ≫ T.ι) ≫ α) :
    φ = n ≫ α := by
  have htop : T.preimage (n ≫ T.ι) = ⊤ :=
    le_antisymm le_top fun i x _ ↦ (n.app i x).2
  have _ : IsIso (T.preimage (n ≫ T.ι)).ι := (Subfunctor.eq_top_iff_isIso _).1 htop
  have hfrom : T.fromPreimage (n ≫ T.ι) = (T.preimage (n ≫ T.ι)).ι ≫ n := by
    refine (cancel_mono T.ι).1 ?_
    rw [Subfunctor.fromPreimage_ι, Category.assoc]
  rw [hfrom, Category.assoc] at H
  exact (cancel_epi (T.preimage (n ≫ T.ι)).ι).1 H

/-- **The two shapes of the lifting condition agree.** For any cartesian square exhibiting a
morphism as the base change of the inclusion of the thickening along a chart `m`, a dotted
arrow restricting to the given arrow along that morphism also restricts to it along the
inclusion of the inverse image of the thickening. -/
private theorem preimage_cond_of_isPullback {Z' T' : AlgebraicSpaces B S hS}
    (Z : Subfunctor Z'.1) (T : Subfunctor T'.1) (a : T.toFunctor ⟶ Z.toFunctor)
    {A A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ T'.1} {i : A₀ ⟶ A}
    {p₀ : A₀ ⟶ T.toFunctor} (hpb : IsPullback p₀ i T.ι m) (c : A ⟶ Z'.1)
    (H : i ≫ c = p₀ ≫ a ≫ Z.ι) :
    (T.preimage m).ι ≫ c = T.fromPreimage m ≫ a ≫ Z.ι := by
  obtain ⟨χ, h1, h2⟩ : ∃ χ : (T.preimage m).toFunctor ⟶ A₀,
      χ ≫ p₀ = T.fromPreimage m ∧ χ ≫ i = (T.preimage m).ι :=
    ⟨hpb.lift _ _ (Subfunctor.fromPreimage_ι T m),
      hpb.lift_fst _ _ (Subfunctor.fromPreimage_ι T m),
      hpb.lift_snd _ _ (Subfunctor.fromPreimage_ι T m)⟩
  calc (T.preimage m).ι ≫ c = (χ ≫ i) ≫ c := by rw [h2]
    _ = χ ≫ (i ≫ c) := by rw [Category.assoc]
    _ = χ ≫ (p₀ ≫ a ≫ Z.ι) := by rw [H]
    _ = (χ ≫ p₀) ≫ a ≫ Z.ι := by rw [Category.assoc]
    _ = T.fromPreimage m ≫ a ≫ Z.ι := by rw [h1]


/-- **Uniqueness of the dotted arrow over an étale chart, from the affine case.** Granted the
lifting property for thickenings of affine algebraic spaces, two dotted arrows over an étale
chart of the ambient space of a first-order thickening agree: they agree over each affine open
of the chart, where the inverse image of the thickening is a first-order thickening of an
affine algebraic space, and the target is an fppf sheaf. -/
private theorem lift_unique_of_affine_lifting_chart
    {X Z' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1) (p : Z' ⟶ X)
    (h : ∀ {T' : AlgebraicSpaces B S hS} (_hT' : IsAffineSpace B S hS T'.1)
      (T : Subfunctor T'.1), IsFirstOrderThickening B S hS T' T →
      ∀ (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1),
        T.ι ≫ b = a ≫ Z.ι ≫ p.hom →
        ∃! c : T'.1 ⟶ Z'.1, (T.ι ≫ c = a ≫ Z.ι) ∧ (c ≫ p.hom = b))
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.1)
    (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    {W : BigFppfOver B S hS} (m : yoneda.obj W ⟶ T'.1)
    (hm : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) m)
    (c d : yoneda.obj W ⟶ Z'.1)
    (hc1 : (T.preimage m).ι ≫ c = T.fromPreimage m ≫ a ≫ Z.ι)
    (hc2 : c ≫ p.hom = m ≫ b)
    (hd1 : (T.preimage m).ι ≫ d = T.fromPreimage m ≫ a ≫ Z.ι)
    (hd2 : d ≫ p.hom = m ≫ b) :
    c = d := by
  classical
  obtain ⟨V, r, haff, hoi, hcov⟩ := exists_affineOpenFamily B S hS W
  refine hom_ext_of_openCover_of_isSheaf B S hS Z'.property.isSheaf r hoi hcov fun k ↦ ?_
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B S hS).map (r k)) := hoi k
  have hmk := presheaf_etale_yoneda_map_comp B S hS (r k) inferInstance m hm
  obtain ⟨hc1', hc2'⟩ := lift_cond_restrict B S hS Z p T a b m (yoneda.map (r k)) c hc1 hc2
  obtain ⟨hd1', hd2'⟩ := lift_cond_restrict B S hS Z p T a b m (yoneda.map (r k)) d hd1 hd2
  have hTk : IsFirstOrderThickening B S hS
      (⟨yoneda.obj (V k), isAlgebraicSpace_yoneda B S hS (V k)⟩ : AlgebraicSpaces B S hS)
      (T.preimage (yoneda.map (r k) ≫ m)) :=
    isFirstOrderThickening_preimage_of_etale B S hS (X := T')
      (Y := ⟨yoneda.obj (V k), isAlgebraicSpace_yoneda B S hS (V k)⟩)
      (yoneda.map (r k) ≫ m) hmk T hT
  have hcommk : (T.preimage (yoneda.map (r k) ≫ m)).ι ≫ ((yoneda.map (r k) ≫ m) ≫ b) =
      (T.fromPreimage (yoneda.map (r k) ≫ m) ≫ a) ≫ Z.ι ≫ p.hom := by
    calc (T.preimage (yoneda.map (r k) ≫ m)).ι ≫ ((yoneda.map (r k) ≫ m) ≫ b)
        = (T.preimage (yoneda.map (r k) ≫ m)).ι ≫ ((yoneda.map (r k) ≫ c) ≫ p.hom) := by
          rw [hc2']
      _ = ((T.preimage (yoneda.map (r k) ≫ m)).ι ≫ (yoneda.map (r k) ≫ c)) ≫ p.hom :=
          (Category.assoc _ _ _).symm
      _ = (T.fromPreimage (yoneda.map (r k) ≫ m) ≫ a ≫ Z.ι) ≫ p.hom := by rw [hc1']
      _ = (T.fromPreimage (yoneda.map (r k) ≫ m) ≫ a) ≫ Z.ι ≫ p.hom := by
          simp only [Category.assoc]
  obtain ⟨_, -, hu⟩ := h
    (T' := ⟨yoneda.obj (V k), isAlgebraicSpace_yoneda B S hS (V k)⟩)
    (isAffineSpace_yoneda B S hS (V k) (haff k))
    (T.preimage (yoneda.map (r k) ≫ m)) hTk
    (T.fromPreimage (yoneda.map (r k) ≫ m) ≫ a) ((yoneda.map (r k) ≫ m) ≫ b) hcommk
  exact (hu _ ⟨hc1'.trans (Category.assoc _ _ _).symm, hc2'⟩).trans
    (hu _ ⟨hd1'.trans (Category.assoc _ _ _).symm, hd2'⟩).symm

/-- **Existence of the dotted arrow over an étale chart, from the affine case.** Granted the
lifting property for thickenings of affine algebraic spaces, every solid diagram over an étale
chart of the ambient space of a first-order thickening admits a dotted arrow: it is solved over
each affine open of the chart, the local solutions agree over the pairwise intersections
because they solve one and the same lifting problem there, and the fppf sheaf condition of the
target glues them. -/
private theorem lift_exists_of_affine_lifting_chart
    {X Z' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1) (p : Z' ⟶ X)
    (h : ∀ {T' : AlgebraicSpaces B S hS} (_hT' : IsAffineSpace B S hS T'.1)
      (T : Subfunctor T'.1), IsFirstOrderThickening B S hS T' T →
      ∀ (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1),
        T.ι ≫ b = a ≫ Z.ι ≫ p.hom →
        ∃! c : T'.1 ⟶ Z'.1, (T.ι ≫ c = a ≫ Z.ι) ∧ (c ≫ p.hom = b))
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.1)
    (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    (comm : T.ι ≫ b = a ≫ Z.ι ≫ p.hom)
    {W : BigFppfOver B S hS} (m : yoneda.obj W ⟶ T'.1)
    (hm : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) m) :
    ∃ c : yoneda.obj W ⟶ Z'.1,
      (T.preimage m).ι ≫ c = T.fromPreimage m ≫ a ≫ Z.ι ∧ c ≫ p.hom = m ≫ b := by
  classical
  obtain ⟨V, r, haff, hoi, hcov⟩ := exists_affineOpenFamily B S hS W
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hoiI : ∀ k, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (r k)) := hoi
  have hmk : ∀ k, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map (r k) ≫ m) := fun k ↦ by
    have _ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (r k)) := hoi k
    exact presheaf_etale_yoneda_map_comp B S hS (r k) inferInstance m hm
  have hTk : ∀ k, IsFirstOrderThickening B S hS
      (⟨yoneda.obj (V k), isAlgebraicSpace_yoneda B S hS (V k)⟩ : AlgebraicSpaces B S hS)
      (T.preimage (yoneda.map (r k) ≫ m)) := fun k ↦
    isFirstOrderThickening_preimage_of_etale B S hS (X := T')
      (Y := ⟨yoneda.obj (V k), isAlgebraicSpace_yoneda B S hS (V k)⟩)
      (yoneda.map (r k) ≫ m) (hmk k) T hT
  choose cl hcl1 hcl2 using fun k ↦ (h
    (T' := ⟨yoneda.obj (V k), isAlgebraicSpace_yoneda B S hS (V k)⟩)
    (isAffineSpace_yoneda B S hS (V k) (haff k))
    (T.preimage (yoneda.map (r k) ≫ m)) (hTk k)
    (T.fromPreimage (yoneda.map (r k) ≫ m) ≫ a) ((yoneda.map (r k) ≫ m) ≫ b)
    (lift_comm_restrict B S hS Z p T a b comm _)).exists
  have hcl1' : ∀ k, (T.preimage (yoneda.map (r k) ≫ m)).ι ≫ cl k =
      T.fromPreimage (yoneda.map (r k) ≫ m) ≫ a ≫ Z.ι :=
    fun k ↦ (hcl1 k).trans (Category.assoc _ _ _)
  -- The local solutions agree on every common refinement, via the pairwise intersections.
  have hcompat : ∀ (k l) (Y : BigFppfOver B S hS) (s : Y ⟶ V k) (t : Y ⟶ V l),
      s ≫ r k = t ≫ r l → yoneda.map s ≫ cl k = yoneda.map t ≫ cl l := by
    intro k l Y s t hst
    have hsq := IsPullback.of_hasPullback (r k) (r l)
    have hsqS := hsq.map (BigFppfOver.toScheme B S hS)
    have hoifst : _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst (r k) (r l))) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @_root_.AlgebraicGeometry.IsOpenImmersion) hsqS.flip (hoi l)
    have hetfst : _root_.AlgebraicGeometry.Etale
        ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst (r k) (r l))) :=
      have := hoifst; inferInstance
    have hchart := presheaf_etale_yoneda_map_comp B S hS
      (Limits.pullback.fst (r k) (r l)) hetfst _ (hmk k)
    obtain ⟨hk1, hk2⟩ := lift_cond_restrict B S hS Z p T a b (yoneda.map (r k) ≫ m)
      (yoneda.map (Limits.pullback.fst (r k) (r l))) (cl k) (hcl1' k) (hcl2 k)
    obtain ⟨hl1, hl2⟩ := lift_cond_restrict B S hS Z p T a b (yoneda.map (r l) ≫ m)
      (yoneda.map (Limits.pullback.snd (r k) (r l))) (cl l) (hcl1' l) (hcl2 l)
    have halign : yoneda.map (Limits.pullback.snd (r k) (r l)) ≫ (yoneda.map (r l) ≫ m) =
        yoneda.map (Limits.pullback.fst (r k) (r l)) ≫ (yoneda.map (r k) ≫ m) := by
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        Limits.pullback.condition]
    rw [halign] at hl1 hl2
    have key : yoneda.map (Limits.pullback.fst (r k) (r l)) ≫ cl k =
        yoneda.map (Limits.pullback.snd (r k) (r l)) ≫ cl l :=
      lift_unique_of_affine_lifting_chart B S hS Z p h T hT a b _ hchart _ _ hk1 hk2 hl1 hl2
    calc yoneda.map s ≫ cl k
        = yoneda.map (Limits.pullback.lift s t hst ≫ Limits.pullback.fst (r k) (r l)) ≫ cl k := by
          rw [Limits.pullback.lift_fst]
      _ = yoneda.map (Limits.pullback.lift s t hst) ≫
            (yoneda.map (Limits.pullback.fst (r k) (r l)) ≫ cl k) := by
          rw [Functor.map_comp, Category.assoc]
      _ = yoneda.map (Limits.pullback.lift s t hst) ≫
            (yoneda.map (Limits.pullback.snd (r k) (r l)) ≫ cl l) := by rw [key]
      _ = yoneda.map (Limits.pullback.lift s t hst ≫ Limits.pullback.snd (r k) (r l)) ≫ cl l := by
          rw [Functor.map_comp, Category.assoc]
      _ = yoneda.map t ≫ cl l := by rw [Limits.pullback.lift_snd]
  have hcovsieve : Sieve.ofArrows V r ∈ BigFppfOver.topology B S hS W :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS r hoiI hcov
  obtain ⟨c, hc⟩ := exists_glue_of_mem_topology (BigFppfOver.topology B S hS)
    Z'.property.isSheaf V r hcovsieve cl hcompat
  refine ⟨c, ?_, ?_⟩
  · -- the glued arrow restricts to the given one, tested on the pullback of the cover
    obtain ⟨W₀, i, p₀, hpb, -⟩ :=
      exists_nthOrderThickening_chart_pullback B S hS hT W m hm
    refine preimage_cond_of_isPullback B S hS Z T a hpb c ?_
    refine hom_ext_of_mem_topology (BigFppfOver.topology B S hS) Z'.property.isSheaf
      ((Sieve.ofArrows V r).pullback i)
      ((BigFppfOver.topology B S hS).pullback_stable i hcovsieve) ?_
    intro Y e he
    obtain ⟨k, g, hg⟩ := (Sieve.mem_ofArrows_iff V r (e ≫ i)).1 he
    obtain ⟨hg1, -⟩ := lift_cond_restrict B S hS Z p T a b (yoneda.map (r k) ≫ m)
      (yoneda.map g) (cl k) (hcl1' k) (hcl2 k)
    have hchart : yoneda.map g ≫ (yoneda.map (r k) ≫ m) = (yoneda.map e ≫ p₀) ≫ T.ι := by
      rw [Category.assoc, hpb.w, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp, hg]
    rw [hchart] at hg1
    have hval := lift_cond_of_factors B S hS T (yoneda.map e ≫ p₀) (yoneda.map g ≫ cl k)
      (a ≫ Z.ι) hg1
    calc yoneda.map e ≫ (yoneda.map i ≫ c)
        = yoneda.map (e ≫ i) ≫ c := by rw [Functor.map_comp, Category.assoc]
      _ = yoneda.map (g ≫ r k) ≫ c := by rw [hg]
      _ = yoneda.map g ≫ (yoneda.map (r k) ≫ c) := by rw [Functor.map_comp, Category.assoc]
      _ = yoneda.map g ≫ cl k := by rw [hc k]
      _ = (yoneda.map e ≫ p₀) ≫ a ≫ Z.ι := hval
      _ = yoneda.map e ≫ (p₀ ≫ a ≫ Z.ι) := by rw [Category.assoc]
  · refine hom_ext_of_openCover_of_isSheaf B S hS X.property.isSheaf r hoiI hcov fun k ↦ ?_
    calc yoneda.map (r k) ≫ (c ≫ p.hom) = (yoneda.map (r k) ≫ c) ≫ p.hom := by
          rw [Category.assoc]
      _ = cl k ≫ p.hom := by rw [hc k]
      _ = (yoneda.map (r k) ≫ m) ≫ b := hcl2 k
      _ = yoneda.map (r k) ≫ (m ≫ b) := by rw [Category.assoc]


/-- **Stacks 0603, the equivalence of (1) and (3).** The universal property of a first-order
thickening of algebraic spaces can already be checked on the diagrams of Stacks 0602 whose
ambient test space is an affine scheme. -/
@[stacks 0603 "equivalence of (1) and (3)"]
theorem isUniversalFirstOrderThickening_iff_affine_lifting
    {X Z' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1) (p : Z' ⟶ X)
    (hZ : IsFirstOrderThickening B S hS Z' Z) :
    IsUniversalFirstOrderThickening B S hS Z p ↔
      ∀ {T' : AlgebraicSpaces B S hS} (_hT' : IsAffineSpace B S hS T'.1)
        (T : Subfunctor T'.1),
        IsFirstOrderThickening B S hS T' T →
        ∀ (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1),
          T.ι ≫ b = a ≫ Z.ι ≫ p.hom →
          ∃! c : T'.1 ⟶ Z'.1, (T.ι ≫ c = a ≫ Z.ι) ∧ (c ≫ p.hom = b) := by
  constructor
  · intro hU _T' _hT' T hT a b comm
    exact hU.existsUnique_lift T hT a b comm
  · refine fun h ↦ ⟨hZ, fun T hT a b comm ↦ ?_⟩
    refine lift_existsUnique_of_chart_lifting B S hS Z p T hT a b fun m hm ↦ ?_
    obtain ⟨c, hc1, hc2⟩ := lift_exists_of_affine_lifting_chart B S hS Z p h T hT a b comm m hm
    exact ⟨c, ⟨hc1, hc2⟩, fun d hd ↦
      lift_unique_of_affine_lifting_chart B S hS Z p h T hT a b m hm d c hd.1 hd.2 hc1 hc2⟩

end AlgebraicGeometry.Space

end
