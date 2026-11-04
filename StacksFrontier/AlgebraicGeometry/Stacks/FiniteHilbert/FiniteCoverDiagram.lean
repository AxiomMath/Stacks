module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityLargeIndex
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram

/-!
# Descending a diagram of finite locally free covers

Let `S` be a scheme contained in a big fppf site `B` and let `d` be a natural number. This file
descends a diagram in the category `ℋ_d` of degree-`d` finite locally free covers of
`AlgebraicGeometry.Stack.finiteCoverCategory`: given an object `U` of the big fppf site, a
family of covers `P i` whose bases cover `U` for the fpqc topology, covers `R i j` presenting
the pairwise fibre products of that family, and covers `T i j k` presenting the triple ones,
there is a degree-`d` finite locally free cover of `U` itself restricting to every `P i`.

## Main results

* `AlgebraicGeometry.Stack.FiniteCover.exists_descended_of_diagram`: the descended cover,
  together with the cartesian squares identifying every member of the family with its base
  change and the compatibility of those identifications over the pairwise fibre products.

## References

* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v u₁ v₁

namespace AlgebraicGeometry.Stack

/-! ### Products in a slice category -/

section Slice

variable {C : Type u₁} [Category.{v₁} C]

/-- A cartesian square over two objects of a slice category presents its apex as their
product there. -/
private lemma over_exists_product_iso [HasPullbacks C]
    {T : C} {W X Y : Over T} [HasBinaryProduct X Y] (a : W ⟶ X) (b : W ⟶ Y)
    (sq : IsPullback a.left b.left X.hom Y.hom) :
    ∃ e : W ≅ X ⨯ Y, e.hom ≫ prod.fst = a ∧ e.hom ≫ prod.snd = b := by
  let e := sq.isoPullback ≪≫ (Over.prodLeftIsoPullback X Y).symm
  have h₁ : e.hom ≫ (prod.fst : X ⨯ Y ⟶ X).left = a.left := by simp [e]
  have h₂ : e.hom ≫ (prod.snd : X ⨯ Y ⟶ Y).left = b.left := by simp [e]
  exact ⟨Over.isoMk e (by rw [← Over.w (prod.fst : X ⨯ Y ⟶ X), ← Category.assoc, h₁, Over.w]),
    Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩

/-- The cocycle condition for a family of transition maps of products, from the triple product
mapping to the three pairwise ones. -/
private lemma productTransition_cocycle [HasBinaryProducts C]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ T : C} (q₁ : Y₁ ⟶ X₁) (q₂ : Y₂ ⟶ X₂)
    (a : Y₁ ⨯ X₂ ⟶ X₁ ⨯ Y₂) (b : Y₂ ⨯ X₃ ⟶ X₂ ⨯ Y₃) (c : Y₁ ⨯ X₃ ⟶ X₁ ⨯ Y₃)
    (ha : a ≫ prod.fst = prod.fst ≫ q₁)
    (ha' : a ≫ prod.snd ≫ q₂ = prod.snd)
    (hb : b ≫ prod.fst = prod.fst ≫ q₂)
    (hc : c ≫ prod.fst = prod.fst ≫ q₁)
    (t : T ≅ (Y₁ ⨯ X₂) ⨯ X₃) (m : T ⟶ Y₂ ⨯ X₃) (n : T ⟶ Y₁ ⨯ X₃)
    (hm₁ : m ≫ prod.fst = t.hom ≫ prod.fst ≫ a ≫ prod.snd)
    (hm₂ : m ≫ prod.snd = t.hom ≫ prod.snd)
    (hn₁ : n ≫ prod.fst = t.hom ≫ prod.fst ≫ prod.fst)
    (hn₂ : n ≫ prod.snd = t.hom ≫ prod.snd)
    (hmn : m ≫ b ≫ prod.snd = n ≫ c ≫ prod.snd) :
    prod.map a (𝟙 X₃) ≫ prodMapLastTwo b = prodMapFirstThird c := by
  apply (cancel_epi t.hom).mp
  apply prod.hom_ext
  · apply prod.hom_ext
    · simp [prodMapLastTwo, prodMapFirstThird, Category.assoc, ha, hc]
    · simp [prodMapLastTwo, prodMapFirstThird, Category.assoc, hb, ha']
  · have hm : t.hom ≫ prod.map a (𝟙 X₃) ≫
        prod.lift (prod.fst ≫ prod.snd) prod.snd = m := by
      apply prod.hom_ext <;> simp [hm₁, hm₂]
    have hn : t.hom ≫ prod.lift (prod.fst ≫ prod.fst) prod.snd = n := by
      apply prod.hom_ext <;> simp [hn₁, hn₂]
    simp only [prodMapLastTwo, prodMapFirstThird, Limits.prod.associator, Limits.prod.braiding,
      prod.map_fst_assoc, prod.map_snd_assoc, prod.map_fst, prod.map_snd, prod.lift_fst,
      prod.lift_snd, prod.lift_fst_assoc, prod.lift_snd_assoc, prod.comp_lift, Category.comp_id]
    simpa only [Category.assoc] using
      (congrArg (fun z => z ≫ b ≫ prod.snd) hm).trans
        (hmn.trans (congrArg (fun z => z ≫ c ≫ prod.snd) hn).symm)

end Slice

/-! ### Descending a finite locally free morphism along an fpqc covering family -/

section Descent

variable {T : Scheme.{u}} {I : Type v} {V : I → Scheme.{u}}

/-- Being finite locally free of a fixed rank descends along an fpqc covering family. -/
private theorem finiteLocallyFreeOfRank_of_fpqc (f : ∀ i, V i ⟶ T)
    (hf : Presieve.ofArrows V f ∈ Scheme.fpqcPrecoverage T)
    {Z : Scheme.{u}} (q : Z ⟶ T) (r : ℕ)
    (h : ∀ i, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd q (f i)) r) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank q r := by
  let : MorphismProperty.IsLocalAtTarget
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r) Scheme.fpqcPrecoverage :=
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc r
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r) hf ?_
  rintro W g _ ⟨i⟩
  exact h i

/-- The compatibility condition of a chart, read on the products in the slice category over the
base rather than on the literal fibre products. -/
private lemma chart_compat_prod {f : ∀ i, V i ⟶ T} {D : DescentData f} (C : D.Chart) (i j : I) :
    (D.gluing i j).hom.left.left ≫
        (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶
          (Over.map (f j)).obj (D.obj j)).left ≫ C.proj j =
      (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶
        (Over.map (f i)).obj (D.obj i)).left ≫ C.proj i := by
  have hsnd : (Over.prodLeftIsoPullback (Over.mk (f i))
        ((Over.map (f j)).obj (D.obj j))).hom ≫
      pullback.snd (f i) ((D.obj j).hom ≫ f j) =
      (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶
        (Over.map (f j)).obj (D.obj j)).left :=
    Over.prodLeftIsoPullback_hom_snd _ _
  have hfst : (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i))
        (Over.mk (f j))).hom ≫
      pullback.fst ((D.obj i).hom ≫ f i) (f j) =
      (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶
        (Over.map (f i)).obj (D.obj i)).left :=
    Over.prodLeftIsoPullback_hom_fst _ _
  have h := congrArg
    (fun z => (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i))
      (Over.mk (f j))).hom ≫ z) (C.compat i j)
  simp only [DescentData.gluingPullbackIso, DescentData.gluingIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Over.forget_map, Category.assoc, Iso.hom_inv_id_assoc] at h
  rwa [← Category.assoc _ (pullback.snd (f i) ((D.obj j).hom ≫ f j)), hsnd,
    ← Category.assoc _ (pullback.fst ((D.obj i).hom ≫ f i) (f j)), hfst] at h

/-- An affine descent datum relative to an fpqc covering family all of whose components are
finite locally free of rank `r` has a chart whose base is finite locally free of rank `r`. -/
private lemma exists_chart_of_rank (f : ∀ i, V i ⟶ T)
    (hf : Presieve.ofArrows V f ∈ Scheme.fpqcPrecoverage T) (D : DescentData f) (r : ℕ)
    (hD : ∀ i, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.obj i).hom r) :
    ∃ C : D.Chart, Stacks.Morphisms.IsFiniteLocallyFreeOfRank C.base.hom r := by
  obtain ⟨C⟩ := DescentData.nonempty_chart_of_isFamilyEffective D
    (DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex f hf D
      fun i => (hD i).toIsAffineHom)
  refine ⟨C, finiteLocallyFreeOfRank_of_fpqc f hf C.base.hom r fun i => ?_⟩
  have h := Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp
    (C.isPullback i).isoPullback.symm (D.obj i).hom (hD i)
  rwa [Iso.symm_hom, (C.isPullback i).isoPullback_inv_snd] at h

end Descent

/-! ### The diagram of covers as a descent datum -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}

/-- The source of a cover, viewed as a scheme over the base of a morphism out of that cover. -/
private abbrev sourceOver {U : BigFppfOver B S hS} (P : FiniteCover B S hS d) (f : P.U ⟶ U) :=
  (Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
    (Over.mk ((BigFppfOver.toScheme B S hS).map P.q))

/-- A morphism of covers over the base, viewed as a morphism of the schemes over it. -/
private def sourceOverMap {U : BigFppfOver B S hS} {P Q : FiniteCover B S hS d} (φ : P ⟶ Q)
    {f : P.U ⟶ U} {g : Q.U ⟶ U} (h : φ.f ≫ g = f) : sourceOver P f ⟶ sourceOver Q g :=
  Over.homMk ((BigFppfOver.toScheme B S hS).map φ.g) (by
    change (BigFppfOver.toScheme B S hS).map φ.g ≫
      ((BigFppfOver.toScheme B S hS).map Q.q ≫ (BigFppfOver.toScheme B S hS).map g) =
      (BigFppfOver.toScheme B S hS).map P.q ≫ (BigFppfOver.toScheme B S hS).map f
    have heq : φ.g ≫ (Q.q ≫ g) = P.q ≫ f := by
      rw [← Category.assoc, φ.square.w, Category.assoc, h]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (BigFppfOver.toScheme B S hS).map heq)

/-- Composites of `sourceOverMap`s agree when the composites of the underlying maps of covers
agree. -/
private lemma sourceOverMap_comp_ext {U : BigFppfOver B S hS} {A B₁ B₂ C : FiniteCover B S hS d}
    {u₁ : A ⟶ B₁} {v₁ : B₁ ⟶ C} {u₂ : A ⟶ B₂} {v₂ : B₂ ⟶ C} (h : u₁ ≫ v₁ = u₂ ≫ v₂)
    {f₀ : A.U ⟶ U} {f₁ : B₁.U ⟶ U} {f₂ : B₂.U ⟶ U} {g : C.U ⟶ U}
    (h₁ : u₁.f ≫ f₁ = f₀) (h₂ : v₁.f ≫ g = f₁) (h₃ : u₂.f ≫ f₂ = f₀) (h₄ : v₂.f ≫ g = f₂) :
    sourceOverMap u₁ h₁ ≫ sourceOverMap v₁ h₂ = sourceOverMap u₂ h₃ ≫ sourceOverMap v₂ h₄ :=
  Over.OverMorphism.ext ((Functor.map_comp _ _ _).symm.trans
    ((congrArg (fun z => (BigFppfOver.toScheme B S hS).map z.g) h).trans (Functor.map_comp _ _ _)))

/-- A cartesian square of bases, pasted with the square of a cover, is cartesian after applying
the functor to schemes, with the base change of the cover as one of its sides. -/
private lemma isPullback_sourceOver {U : BigFppfOver B S hS} {P Q R : FiniteCover B S hS d}
    {f : P.U ⟶ U} {g : Q.U ⟶ U} {u : R.U ⟶ U} (a : R ⟶ P) (b : R ⟶ Q)
    (sq : IsPullback a.f b.f f g) (h₁ : a.f ≫ f = u)
    (z : sourceOver R u ⟶ sourceOver Q g) (hz : z.left = (BigFppfOver.toScheme B S hS).map b.g) :
    IsPullback (sourceOverMap a h₁).left
      (z ≫ structureMap ((BigFppfOver.toScheme B S hS).map g)
        (Over.mk ((BigFppfOver.toScheme B S hS).map Q.q))).left
      (sourceOver P f).hom ((BigFppfOver.toScheme B S hS).map g) := by
  let H := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan H := preservesPullbacks_bigFppfOverToScheme B S hS
  have hs := (a.square.paste_vert sq).map H
  have hb : (z ≫ structureMap (H.map g) (Over.mk (H.map Q.q))).left = H.map (R.q ≫ b.f) := by
    change z.left ≫ H.map Q.q = _
    rw [hz, ← H.map_comp, b.square.w]
  rw [hb]
  change IsPullback (H.map a.g) (H.map (R.q ≫ b.f)) (H.map P.q ≫ H.map f) (H.map g)
  simpa only [Functor.map_comp] using hs

/-- A cover presenting a fibre product of two bases presents the scheme over it as the product
of the two slices, in both of the two ways. -/
private lemma sourceOver_pair {U : BigFppfOver B S hS} {P Q R : FiniteCover B S hS d}
    (f : P.U ⟶ U) (g : Q.U ⟶ U) (a : R ⟶ P) (b : R ⟶ Q) (sq : IsPullback a.f b.f f g) :
    ∃ (l : sourceOver R (a.f ≫ f) ≅
        sourceOver P f ⨯ Over.mk ((BigFppfOver.toScheme B S hS).map g))
      (r : sourceOver R (a.f ≫ f) ≅
        Over.mk ((BigFppfOver.toScheme B S hS).map f) ⨯ sourceOver Q g),
      l.hom ≫ prod.fst = sourceOverMap a rfl ∧
      r.hom ≫ prod.snd = sourceOverMap b sq.w.symm ∧
      l.hom ≫ prod.snd = r.hom ≫ prod.snd ≫
        structureMap ((BigFppfOver.toScheme B S hS).map g)
          (Over.mk ((BigFppfOver.toScheme B S hS).map Q.q)) ∧
      r.hom ≫ prod.fst = l.hom ≫ prod.fst ≫
        structureMap ((BigFppfOver.toScheme B S hS).map f)
          (Over.mk ((BigFppfOver.toScheme B S hS).map P.q)) := by
  let H := BigFppfOver.toScheme B S hS
  let ca := sourceOverMap a (g := f) rfl
  let cb := sourceOverMap b (g := g) sq.w.symm
  let p₁ : sourceOver R (a.f ≫ f) ⟶ Over.mk (H.map f) :=
    ca ≫ structureMap (H.map f) (Over.mk (H.map P.q))
  let p₂ : sourceOver R (a.f ≫ f) ⟶ Over.mk (H.map g) :=
    cb ≫ structureMap (H.map g) (Over.mk (H.map Q.q))
  have hs₁ : IsPullback ca.left p₂.left (sourceOver P f).hom (H.map g) :=
    isPullback_sourceOver a b sq rfl cb rfl
  have hs₂ : IsPullback p₁.left cb.left (H.map f) (sourceOver Q g).hom :=
    (isPullback_sourceOver b a sq.flip sq.w.symm ca rfl).flip
  obtain ⟨l, hl₁, hl₂⟩ := over_exists_product_iso ca p₂ hs₁
  obtain ⟨r, hr₁, hr₂⟩ := over_exists_product_iso p₁ cb hs₂
  refine ⟨l, r, hl₁, hr₂, ?_, ?_⟩
  · rw [hl₂, ← Category.assoc, hr₂]
  · rw [hr₁, ← Category.assoc, hl₁]

/-- **A diagram of degree-`d` finite locally free covers over a covering family descends.**
Let `U` be an object of the big fppf site over `S`, let `P i` be a family of degree-`d` finite
locally free covers whose bases cover `U` for the fpqc topology, let `R i j` be covers
presenting the pairwise fibre products of those bases and `T i j k` covers presenting the triple
ones. Then there is a degree-`d` finite locally free morphism `q` of schemes over `U` whose base
change along every member of the family is the corresponding cover `P i`, compatibly with the
two projections of every `R i j`. -/
theorem FiniteCover.exists_descended_of_diagram
    {U : BigFppfOver B S hS} {I : Type v}
    (P : I → FiniteCover B S hS d) (f : ∀ i, (P i).U ⟶ U)
    (hf : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (P i).U)
      (fun i => (BigFppfOver.toScheme B S hS).map (f i)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj U))
    (R : I → I → FiniteCover B S hS d)
    (a : ∀ i j, R i j ⟶ P i) (b : ∀ i j, R i j ⟶ P j)
    (sq : ∀ i j, IsPullback (a i j).f (b i j).f (f i) (f j))
    (T : I → I → I → FiniteCover B S hS d)
    (c₁₂ : ∀ i j k, T i j k ⟶ R i j)
    (c₂₃ : ∀ i j k, T i j k ⟶ R j k)
    (c₁₃ : ∀ i j k, T i j k ⟶ R i k)
    (h₁ : ∀ i j k, c₁₂ i j k ≫ a i j = c₁₃ i j k ≫ a i k)
    (h₂ : ∀ i j k, c₁₂ i j k ≫ b i j = c₂₃ i j k ≫ a j k)
    (h₃ : ∀ i j k, c₂₃ i j k ≫ b j k = c₁₃ i j k ≫ b i k)
    (sq₃ : ∀ i j k, IsPullback (c₁₂ i j k).f ((c₂₃ i j k ≫ b j k).f)
      ((a i j).f ≫ f i) (f k)) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ (BigFppfOver.toScheme B S hS).obj U),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank q d ∧
      ∃ g : ∀ i, (BigFppfOver.toScheme B S hS).obj (P i).Z ⟶ Z,
        (∀ i, IsPullback (g i) ((BigFppfOver.toScheme B S hS).map (P i).q) q
          ((BigFppfOver.toScheme B S hS).map (f i))) ∧
        ∀ i j, (BigFppfOver.toScheme B S hS).map (a i j).g ≫ g i =
          (BigFppfOver.toScheme B S hS).map (b i j).g ≫ g j := by
  classical
  let H := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan H := preservesPullbacks_bigFppfOverToScheme B S hS
  let X (i : I) : Over (H.obj U) := Over.mk (H.map (f i))
  let Y (i : I) := sourceOver (P i) (f i)
  let qY (i : I) : Y i ⟶ X i := structureMap (H.map (f i)) (Over.mk (H.map (P i).q))
  choose l r hl hr hp₂ hp₁ using fun i j =>
    sourceOver_pair (f i) (f j) (a i j) (b i j) (sq i j)
  let φ (i j : I) : Y i ⨯ X j ≅ X i ⨯ Y j := (l i j).symm ≪≫ r i j
  have hφ₁ (i j : I) : (φ i j).hom ≫ prod.fst = prod.fst ≫ qY i := by
    apply (cancel_epi (l i j).hom).mp
    simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    exact hp₁ i j
  have hφ₂ (i j : I) : (φ i j).hom ≫ prod.snd ≫ qY j = prod.snd := by
    apply (cancel_epi (l i j).hom).mp
    simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    exact (hp₂ i j).symm
  have hcocycle (i j k : I) : prod.map (φ i j).hom (𝟙 (X k)) ≫
      prodMapLastTwo (φ j k).hom = prodMapFirstThird (φ i k).hom := by
    let uT := (c₁₂ i j k).f ≫ (a i j).f ≫ f i
    have h23 : (c₂₃ i j k).f ≫ ((a j k).f ≫ f j) = uT := by
      show (c₂₃ i j k).f ≫ ((a j k).f ≫ f j) = (c₁₂ i j k).f ≫ (a i j).f ≫ f i
      rw [← Category.assoc, ← show (c₁₂ i j k).f ≫ (b i j).f =
        (c₂₃ i j k).f ≫ (a j k).f from congrArg FiniteCover.Hom.f (h₂ i j k),
        Category.assoc, (sq i j).w]
    have h13 : (c₁₃ i j k).f ≫ ((a i k).f ≫ f i) = uT := by
      have hh := congrArg (fun z => z.f ≫ f i) (h₁ i j k).symm
      change ((c₁₃ i j k).f ≫ (a i k).f) ≫ f i = ((c₁₂ i j k).f ≫ (a i j).f) ≫ f i at hh
      simpa only [Category.assoc] using hh
    let m₁₂ := sourceOverMap (c₁₂ i j k) (f := uT) rfl
    let m₂₃ := sourceOverMap (c₂₃ i j k) h23
    let m₁₃ := sourceOverMap (c₁₃ i j k) h13
    let z₃ := m₂₃ ≫ sourceOverMap (b j k) (sq j k).w.symm
    let p₃ := z₃ ≫ qY k
    have hsqT : IsPullback m₁₂.left p₃.left
        (sourceOver (R i j) ((a i j).f ≫ f i)).hom (H.map (f k)) :=
      isPullback_sourceOver (c₁₂ i j k) (c₂₃ i j k ≫ b j k) (sq₃ i j k) rfl z₃
        (H.map_comp _ _).symm
    obtain ⟨t₀, ht₁, ht₂⟩ := over_exists_product_iso m₁₂ p₃ hsqT
    let t := t₀ ≪≫ prod.mapIso (l i j) (Iso.refl (X k))
    let m := m₂₃ ≫ (l j k).hom
    let n := m₁₃ ≫ (l i k).hom
    have hm12 : m₁₂ ≫ sourceOverMap (a i j) rfl = m₁₃ ≫ sourceOverMap (a i k) rfl :=
      sourceOverMap_comp_ext (h₁ i j k) _ _ _ _
    have hm23 : m₁₂ ≫ sourceOverMap (b i j) (sq i j).w.symm =
        m₂₃ ≫ sourceOverMap (a j k) rfl :=
      sourceOverMap_comp_ext (h₂ i j k) _ _ _ _
    have hn3 : m₁₃ ≫ sourceOverMap (b i k) (sq i k).w.symm = z₃ :=
      sourceOverMap_comp_ext (h₃ i j k).symm _ _ _ _
    have ht1 : t.hom ≫ prod.fst = m₁₂ ≫ (l i j).hom := by
      show (t₀.hom ≫ prod.map (l i j).hom (𝟙 (X k))) ≫ prod.fst = _
      rw [Category.assoc, prod.map_fst, ← Category.assoc, ht₁]
    have ht2 : t.hom ≫ prod.snd = p₃ := by
      show (t₀.hom ≫ prod.map (l i j).hom (𝟙 (X k))) ≫ prod.snd = _
      rw [Category.assoc, prod.map_snd, Category.comp_id, ht₂]
    have htphi : t.hom ≫ prod.fst ≫ (φ i j).hom = m₁₂ ≫ (r i j).hom := by
      rw [← Category.assoc, ht1]
      simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    apply productTransition_cocycle (qY i) (qY j) (φ i j).hom (φ j k).hom (φ i k).hom
      (hφ₁ i j) (hφ₂ i j) (hφ₁ j k) (hφ₁ i k) t m n
    · show (m₂₃ ≫ (l j k).hom) ≫ prod.fst = _
      rw [Category.assoc, hl, ← Category.assoc _ _ prod.snd, ← Category.assoc t.hom, htphi,
        Category.assoc, hr]
      exact hm23.symm
    · show (m₂₃ ≫ (l j k).hom) ≫ prod.snd = _
      rw [Category.assoc, hp₂, ← Category.assoc (r j k).hom, hr, ← Category.assoc, ht2]
    · show (m₁₃ ≫ (l i k).hom) ≫ prod.fst = _
      rw [Category.assoc, hl, ← Category.assoc _ _ prod.fst, ht1, Category.assoc, hl]
      exact hm12.symm
    · show (m₁₃ ≫ (l i k).hom) ≫ prod.snd = _
      rw [Category.assoc, hp₂, ← Category.assoc (r i k).hom, hr, ← Category.assoc, hn3, ht2]
    · show (m₂₃ ≫ (l j k).hom) ≫ (φ j k).hom ≫ prod.snd =
        (m₁₃ ≫ (l i k).hom) ≫ (φ i k).hom ≫ prod.snd
      simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
      rw [hr, hr]
      exact hn3.symm
  let E : DescentData (fun i => H.map (f i)) := {
    obj i := Over.mk (H.map (P i).q)
    gluing i j := Over.isoMk (φ i j) (by
      show (φ i j).hom ≫ prod.map (𝟙 (X i)) (qY j) = prod.map (qY i) (𝟙 (X j))
      apply prod.hom_ext
      · simpa only [Category.assoc, prod.map_fst, prod.map_fst_assoc, Category.comp_id]
          using hφ₁ i j
      · simpa only [Category.assoc, prod.map_snd, prod.map_snd_assoc, Category.comp_id]
          using hφ₂ i j)
    cocycle := hcocycle }
  obtain ⟨C, hq⟩ := exists_chart_of_rank (fun i => H.map (f i)) hf E d
    fun i => (P i).finiteLocallyFree
  refine ⟨C.base.left, C.base.hom, hq, fun i => C.proj i, C.isPullback, ?_⟩
  intro i j
  have hcp : (φ i j).hom.left ≫ (prod.snd : X i ⨯ Y j ⟶ Y j).left ≫ C.proj j =
      (prod.fst : Y i ⨯ X j ⟶ Y i).left ≫ C.proj i := chart_compat_prod C i j
  have hl' : (l i j).hom.left ≫ (prod.fst : Y i ⨯ X j ⟶ Y i).left = H.map (a i j).g :=
    congrArg Over.Hom.left (hl i j)
  have hr' : (r i j).hom.left ≫ (prod.snd : X i ⨯ Y j ⟶ Y j).left = H.map (b i j).g :=
    congrArg Over.Hom.left (hr i j)
  have he : (l i j).hom.left ≫ (φ i j).hom.left = (r i j).hom.left :=
    congrArg Over.Hom.left (by simp [φ] : (l i j).hom ≫ (φ i j).hom = (r i j).hom)
  rw [← hl', ← hr', ← he]
  simp only [Category.assoc, hcp]

end AlgebraicGeometry.Stack

end
