module

public import StacksFrontier.AlgebraicGeometry.Descent.FiniteEtaleCoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteEtaleCoversStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.StackDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.EffectiveDescentRefinement

/-!
# Stacks 0BLZ: finite étale covers form a stack over the big fppf site

Let `S` be a scheme contained in a big fppf site, let `FÉt` be the category of finite étale
covers of Stacks 0BLY and let `p : FÉt ⟶ (Sch/S)_fppf` be its projection to the base. This file
proves condition (3) of Stacks 026F for `p` — effectivity of descent along a covering sieve — and
assembles it with conditions (1) and (2) into the statement that `p` defines a stack,
**Stacks 0BLZ**.

The source's proof is fppf descent for finite étale morphisms, which it reads off Stacks 0245,
Stacks 02LA and Stacks 02VN: a finite étale morphism is affine, so a descent datum of such covers
is effective as a descent datum of schemes, and being finite étale is fpqc local on the base, so
the descended morphism is again finite étale. That argument is carried out here for a diagram over
a covering family; the passage from a covering *sieve* to a covering family is legitimate because
the morphism presheaves of `p` are sheaves, which is condition (2).

## Main definitions

* `AlgebraicGeometry.finiteEtaleSourceDiagram`: the total spaces of a descent datum of `FÉt`
  relative to a sieve, as a diagram with cartesian, strictly composable transition squares.

## Main results

* `AlgebraicGeometry.isFinite_inf_etale_of_fpqcCover`: being finite étale is fpqc local on the
  base, Stacks 02LA together with Stacks 02VN.
* `AlgebraicGeometry.finiteEtaleProjection_isStronglyCartesian_of_isPullback`,
  `AlgebraicGeometry.finiteEtaleProjection_isCartesian_of_isPullback` and
  `AlgebraicGeometry.finiteEtaleProjection_isPullback_of_isCartesian`: a morphism of `FÉt` is
  cartesian exactly when its underlying square of the site is cartesian.
* `AlgebraicGeometry.cartesianSieveDiagram_exists_scheme_cocone` and
  `AlgebraicGeometry.cartesianSieveDiagram_exists_site_cocone`: the objects of a diagram with
  cartesian, strictly composable transition squares descend along a covering family of the sieve
  whose underlying family of schemes is an fpqc covering family, the first producing a scheme and
  the second an object of the site carrying the finite étale property.
* `AlgebraicGeometry.finiteEtaleProjection_hasEffectiveDescent`: condition (3) of Stacks 026F
  for `FÉt`.
* `AlgebraicGeometry.finiteEtaleProjection_isStack`: **Stacks 0BLZ**.

## Implementation notes

`AlgebraicGeometry.cartesianSieveDiagram_exists_scheme_cocone` is stated for an arbitrary
`AlgebraicGeometry.Stack.FiniteHilbert.CartesianSieveDiagram` and asks only that the structure
morphisms be affine. It is the generalisation along those two axes of
`AlgebraicGeometry.Stack.FiniteHilbert.sieve_exists_fpqc_cocone`, which is stated for the
particular diagram of covers of a descent datum of the relative finite Hilbert category and
concludes at the degree-`d` finite locally free morphisms; the product identifications and the
cocycle comparison it needs — `AlgebraicGeometry.Stack.FiniteHilbert.over_exists_product_iso` and
`AlgebraicGeometry.Stack.FiniteHilbert.productTransition_cocycle`, both statements about binary
products in an arbitrary category — are reused unchanged, as is the extension of a cocone from a
covering family to the whole sieve,
`AlgebraicGeometry.Stack.FiniteHilbert.CartesianSieveDiagram.exists_cocone`.

## References

* [Stacks Project, Tag 0BLZ](https://stacks.math.columbia.edu/tag/0BLZ)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02LA](https://stacks.math.columbia.edu/tag/02LA)
* [Stacks Project, Tag 02VN](https://stacks.math.columbia.edu/tag/02VN)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w v

namespace AlgebraicGeometry

-- A fibre of a functor is a subtype of its source, a point of the fibre is read through that
-- subtype, and the base of a finite étale cover is the value of the projection on it along a chain
-- of unfoldings and projections of constructors.  The tactics below compare the two spellings of
-- each constantly, so the chains are made visible to the unifier rather than argued about at every
-- step.
attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion Functor.Fiber.mk
  finiteEtaleProjection Arrow.rightFunc

/-! ### Finite étale morphisms of schemes -/

section Property

/-- **Being finite and étale is fpqc local on the base.** Finiteness is Stacks 02LA and
étaleness is Stacks 02VN. -/
theorem isFinite_inf_etale_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      ((@IsFinite.{u} ⊓ @Etale.{u} : MorphismProperty Scheme.{u})) Scheme.fpqcPrecoverage :=
  have _h1 := Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc.{u}
  MorphismProperty.IsLocalAtTarget.inf _ _

/-- **Being finite and étale is fpqc local on the base**, in the form consumed below: a morphism
whose base change along every member of an fpqc covering family is finite and étale is itself
finite and étale. -/
theorem isFinite_inf_etale_of_fpqcCover {T : Scheme.{u}} {I : Type w}
    (V : I → Scheme.{u}) (f : ∀ i, V i ⟶ T)
    (hf : Presieve.ofArrows V f ∈ Scheme.fpqcPrecoverage T)
    {Z : Scheme.{u}} (q : Z ⟶ T)
    (h : ∀ i, (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) (pullback.snd q (f i))) :
    (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) q := by
  have : MorphismProperty.IsLocalAtTarget
      ((@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})) Scheme.fpqcPrecoverage :=
    isFinite_inf_etale_isLocalAtTarget_fpqc.{u}
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})) hf ?_
  intro W g _ hg
  cases hg with
  | mk i => exact h i

/-- **The source of a finite étale morphism into a scheme contained in a big fppf site is
contained in that site.** Such a morphism is finite, hence quasi-compact, and étale, hence
locally of finite type, so it does not raise the size of its target past the cutoff. -/
theorem contains_of_isFinite_inf_etale (B : BigFppfSite.{u}) {T Z : Scheme.{u}} (q : Z ⟶ T)
    (hT : B.Contains T) (hq : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) q) :
    B.Contains Z := by
  have : IsFinite q := hq.1
  have : Etale q := hq.2
  have : QuasiCompact q := inferInstance
  have : LocallyOfFiniteType q := inferInstance
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact q hT

end Property

/-! ### Cartesian morphisms of `FÉt` -/

section Cartesian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of `FÉt` lies over the morphism of bases it carries. -/
lemma finiteEtaleProjection_isHomLift {x y : FiniteEtaleCovers B S hS} (Φ : x ⟶ y) :
    (finiteEtaleProjection B S hS).IsHomLift Φ.right Φ :=
  IsHomLift.map (finiteEtaleProjection B S hS) Φ

/-- **A morphism of `FÉt` whose underlying square is cartesian is a strongly cartesian
morphism.** The lift of a morphism into the target is the one the cartesian square provides, and
it is unique because a morphism of `FÉt` is determined by its two components. -/
lemma finiteEtaleProjection_isStronglyCartesian_of_isPullback {x y : FiniteEtaleCovers B S hS}
    (Φ : x ⟶ y) {r : x.right ⟶ y.right} (hr : Φ.right = r)
    (sq : IsPullback Φ.left x.hom y.hom r) :
    (finiteEtaleProjection B S hS).IsStronglyCartesian r Φ := by
  cases hr
  refine { toIsHomLift := finiteEtaleProjection_isHomLift B S hS Φ
           universal_property' := ?_ }
  intro c g ψ hψ
  have hgr : g ≫ Φ.right = ψ.right :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ (finiteEtaleProjection B S hS) _ _ (g ≫ Φ.right) ψ hψ
  have hw : ψ.left ≫ y.hom = (c.hom ≫ g) ≫ Φ.right := by
    rw [MorphismProperty.Arrow.w ψ, ← hgr]
    exact (Category.assoc _ _ _).symm
  refine ⟨MorphismProperty.Arrow.homMk (sq.lift ψ.left (c.hom ≫ g) hw) g
      (sq.lift_snd _ _ hw),
    ⟨finiteEtaleProjection_isHomLift_homMk B S hS _ _ _,
      MorphismProperty.Arrow.Hom.ext (sq.lift_fst _ _ hw) hgr⟩, ?_⟩
  rintro χ ⟨hχ, hχ'⟩
  have hχr : g = χ.right :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ (finiteEtaleProjection B S hS) _ _ g χ hχ
  refine MorphismProperty.Arrow.Hom.ext ?_ hχr.symm
  refine sq.hom_ext ?_ ?_
  · exact (congrArg (fun m => m.left) hχ').trans (sq.lift_fst _ _ hw).symm
  · refine (MorphismProperty.Arrow.w χ).trans ?_
    rw [← hχr]
    exact (sq.lift_snd _ _ hw).symm

/-- **A morphism of `FÉt` whose underlying square is cartesian is a cartesian morphism.** -/
lemma finiteEtaleProjection_isCartesian_of_isPullback {x y : FiniteEtaleCovers B S hS}
    (Φ : x ⟶ y) {r : x.right ⟶ y.right} (hr : Φ.right = r)
    (sq : IsPullback Φ.left x.hom y.hom r) :
    (finiteEtaleProjection B S hS).IsCartesian r Φ :=
  have := finiteEtaleProjection_isStronglyCartesian_of_isPullback B S hS Φ hr sq
  inferInstance

/-- The cartesian square exhibiting a base change of a finite étale cover presents it as a
strongly cartesian morphism of `FÉt`. -/
instance finiteEtaleProjection_isStronglyCartesian_baseChangeHom
    (a : FiniteEtaleCovers B S hS) {V : BigFppfOver B S hS} (h : V ⟶ a.right) :
    (finiteEtaleProjection B S hS).IsStronglyCartesian h
      (FiniteEtaleCovers.baseChangeHom B S hS a h) :=
  have := hasPullbacks_bigFppfOver B S hS
  finiteEtaleProjection_isStronglyCartesian_of_isPullback B S hS _ rfl
    (IsPullback.of_hasPullback a.hom h)

/-- **A morphism of `FÉt` whose underlying square is cartesian is a cartesian morphism**, with
the two bases presented through identifications `x.right = W` and `y.right = V`. -/
lemma finiteEtaleProjection_isCartesian_of_isPullback_eqToHom
    {x y : FiniteEtaleCovers B S hS} {W V : BigFppfOver B S hS} (a : W ⟶ V) (Φ : x ⟶ y)
    (hx : x.right = W) (hy : y.right = V)
    (hΦr : Φ.right = eqToHom hx ≫ a ≫ eqToHom hy.symm)
    (sq : IsPullback Φ.left (x.hom ≫ eqToHom hx) (y.hom ≫ eqToHom hy) a) :
    (finiteEtaleProjection B S hS).IsCartesian a Φ := by
  revert a hΦr sq
  cases hx
  cases hy
  intro a hΦr sq
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hΦr sq
  exact finiteEtaleProjection_isCartesian_of_isPullback B S hS Φ hΦr sq

/-- **A cartesian morphism of `FÉt` has cartesian underlying square.** The base change of its
target along the morphism of bases it lies over is cartesian over that same morphism, so the
canonical comparison of the two is an isomorphism and identifies the source of the morphism with
the fibre product.

The two bases are presented through identifications `x.right = W` and `y.right = V`, which is the
shape in which the objects of a descent datum relative to a sieve carry their bases. -/
lemma finiteEtaleProjection_isPullback_of_isCartesian {x y : FiniteEtaleCovers B S hS}
    {W V : BigFppfOver B S hS} (a : W ⟶ V) (Φ : x ⟶ y)
    (hx : x.right = W) (hy : y.right = V)
    (hΦ : (finiteEtaleProjection B S hS).IsCartesian a Φ) :
    IsPullback Φ.left (x.hom ≫ eqToHom hx) (y.hom ≫ eqToHom hy) a := by
  revert a hΦ
  cases hx
  cases hy
  intro a hΦ
  simp only [eqToHom_refl, Category.comp_id]
  obtain rfl : a = (finiteEtaleProjection B S hS).map Φ :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ (finiteEtaleProjection B S hS) _ _ a Φ
      hΦ.toIsHomLift
  have := hasPullbacks_bigFppfOver B S hS
  have hc : (finiteEtaleProjection B S hS).IsCartesian Φ.right Φ := hΦ
  have hhl : (finiteEtaleProjection B S hS).IsHomLift Φ.right Φ :=
    finiteEtaleProjection_isHomLift B S hS Φ
  have hfac := Functor.IsCartesian.fac (finiteEtaleProjection B S hS) Φ.right
    (FiniteEtaleCovers.baseChangeHom B S hS y Φ.right) Φ
  have hr : (𝟙 x.right) =
      (Functor.IsCartesian.map (finiteEtaleProjection B S hS) Φ.right
        (FiniteEtaleCovers.baseChangeHom B S hS y Φ.right) Φ).right :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ (finiteEtaleProjection B S hS) x
      (FiniteEtaleCovers.baseChange B S hS y Φ.right) (𝟙 x.right)
      (Functor.IsCartesian.map (finiteEtaleProjection B S hS) Φ.right
        (FiniteEtaleCovers.baseChangeHom B S hS y Φ.right) Φ)
      (Functor.IsCartesian.map_isHomLift (finiteEtaleProjection B S hS) Φ.right
        (FiniteEtaleCovers.baseChangeHom B S hS y Φ.right) Φ)
  refine IsPullback.of_iso_pullback ⟨MorphismProperty.Arrow.w Φ⟩
    (CategoryTheory.Arrow.leftFunc.mapIso ((MorphismProperty.Arrow.forget _ _ _).mapIso
      (Functor.IsCartesian.domainUniqueUpToIso (finiteEtaleProjection B S hS) Φ.right
        (FiniteEtaleCovers.baseChangeHom B S hS y Φ.right) Φ))) ?_ ?_
  · exact congrArg (fun m => m.left) hfac
  · refine (MorphismProperty.Arrow.w
      (Functor.IsCartesian.map (finiteEtaleProjection B S hS) Φ.right
        (FiniteEtaleCovers.baseChangeHom B S hS y Φ.right) Φ)).trans ?_
    rw [← hr]
    exact Category.comp_id _

end Cartesian


/-! ### Descending the objects of a cartesian diagram over a covering family of a sieve -/

section SieveDiagram

open Stack.FiniteHilbert

/-- A transition morphism of a cartesian sieve diagram commutes with the composite structure
morphisms to the base of the sieve. -/
theorem Stack.FiniteHilbert.CartesianSieveDiagram.map_comp_q_comp {C : Type*} [Category C]
    {U : C} {R : Sieve U} (D : CartesianSieveDiagram R) {V W : C} {f : V ⟶ U} (hf : R f)
    {g : W ⟶ U} (hg : R g) (a : W ⟶ V) (ha : a ≫ f = g) :
    D.map hf hg a ha ≫ D.q f hf ≫ f = D.q g hg ≫ g := by
  rw [← Category.assoc, (D.square hf hg a ha).w, Category.assoc, ha]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The objects of a diagram with cartesian, strictly composable transition squares descend
along a covering family of the sieve whose underlying family of schemes is an fpqc covering
family, as soon as their structure morphisms are affine.**

This is Stacks 0245 for the descent datum of schemes that the diagram carries: the objects at the
members of the family, the gluing isomorphisms read off the objects at the overlap arrows — which
the cartesian squares of the diagram present as fibre products in two ways — and the cocycle
condition read off the objects at the triple overlap arrows, where strict composability of the
transition morphisms makes the two ways round the triangle agree. -/
theorem cartesianSieveDiagram_exists_scheme_cocone {U : BigFppfOver B S hS} {R : Sieve U}
    (D : CartesianSieveDiagram R) {ι : Type v} {V : ι → BigFppfOver B S hS}
    (f : ∀ i, V i ⟶ U) (hR : ∀ i, R (f i))
    (hf : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (V i))
      (fun i => (BigFppfOver.toScheme B S hS).map (f i)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj U))
    (haff : ∀ i, IsAffineHom ((BigFppfOver.toScheme B S hS).map (D.q (f i) (hR i)))) :
    ∃ (Z : Scheme.{u}) (pz : Z ⟶ (BigFppfOver.toScheme B S hS).obj U)
      (g : ∀ i, (BigFppfOver.toScheme B S hS).obj (D.obj (f i) (hR i)) ⟶ Z),
      (∀ i, IsPullback (g i) ((BigFppfOver.toScheme B S hS).map (D.q (f i) (hR i))) pz
        ((BigFppfOver.toScheme B S hS).map (f i))) ∧
      ∀ i j : ι,
        (BigFppfOver.toScheme B S hS).map (D.map (hR i)
            (R.downward_closed (hR i) (pullback.fst (f i) (f j)))
            (pullback.fst (f i) (f j)) rfl) ≫ g i =
          (BigFppfOver.toScheme B S hS).map (D.map (hR j)
            (R.downward_closed (hR i) (pullback.fst (f i) (f j)))
            (pullback.snd (f i) (f j)) pullback.condition.symm) ≫ g j := by
  classical
  have := hasPullbacks_bigFppfOver B S hS
  have := preservesPullbacks_bigFppfOverToScheme B S hS
  let H := BigFppfOver.toScheme B S hS
  -- the family, the overlaps and the triple overlaps, as arrows of the sieve
  let pr (i j : ι) := pullback.fst (f i) (f j)
  let rr (i j : ι) := pullback.snd (f i) (f j)
  let f₂ (i j : ι) := pr i j ≫ f i
  let m₂ (i j : ι) := R.downward_closed (hR i) (pr i j)
  let cc (i j : ι) := D.map (hR i) (m₂ i j) (pr i j) rfl
  let ee (i j : ι) := D.map (hR j) (m₂ i j) (rr i j) pullback.condition.symm
  let tt (i j k : ι) := pullback.fst (f₂ i j) (f k)
  let ss (i j k : ι) := pullback.snd (f₂ i j) (f k)
  let f₃ (i j k : ι) := tt i j k ≫ f₂ i j
  let m₃ (i j k : ι) := R.downward_closed (m₂ i j) (tt i j k)
  let u₂₃ (i j k : ι) : pullback (f₂ i j) (f k) ⟶ pullback (f j) (f k) :=
    pullback.lift (tt i j k ≫ rr i j) (ss i j k) (by
      rw [Category.assoc, ← pullback.condition]
      exact pullback.condition)
  let u₁₃ (i j k : ι) : pullback (f₂ i j) (f k) ⟶ pullback (f i) (f k) :=
    pullback.lift (tt i j k ≫ pr i j) (ss i j k) (by
      rw [Category.assoc]
      exact pullback.condition)
  have hu₂₃ (i j k : ι) : u₂₃ i j k ≫ f₂ j k = f₃ i j k := by
    dsimp only [u₂₃, f₂, f₃, pr, rr]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, ← pullback.condition]
  have hu₁₃ (i j k : ι) : u₁₃ i j k ≫ f₂ i k = f₃ i j k := by
    dsimp only [u₁₃, f₂, f₃, pr]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc]
  let d₁₂ (i j k : ι) := D.map (m₂ i j) (m₃ i j k) (tt i j k) rfl
  let d₂₃ (i j k : ι) := D.map (m₂ j k) (m₃ i j k) (u₂₃ i j k) (hu₂₃ i j k)
  let d₁₃ (i j k : ι) := D.map (m₂ i k) (m₃ i j k) (u₁₃ i j k) (hu₁₃ i j k)
  have hd₁ (i j k : ι) : d₁₂ i j k ≫ cc i j = d₁₃ i j k ≫ cc i k := by
    dsimp only [d₁₂, d₁₃, cc]
    rw [D.map_comp, D.map_comp]
    simp only [u₁₃, pr, pullback.lift_fst]
  have hd₂ (i j k : ι) : d₁₂ i j k ≫ ee i j = d₂₃ i j k ≫ cc j k := by
    dsimp only [d₁₂, d₂₃, cc, ee]
    rw [D.map_comp, D.map_comp]
    simp only [u₂₃, pr, pullback.lift_fst]
  have hd₃ (i j k : ι) : d₂₃ i j k ≫ ee j k = d₁₃ i j k ≫ ee i k := by
    dsimp only [d₂₃, d₁₃, ee]
    rw [D.map_comp, D.map_comp]
    simp only [u₂₃, u₁₃, rr, pullback.lift_snd]
  -- the diagram, read in the slice of schemes over the base
  let XO (i : ι) : Over (H.obj U) := Over.mk (H.map (f i))
  let YO (i : ι) : Over (H.obj U) :=
    (Over.map (H.map (f i))).obj (Over.mk (H.map (D.q (f i) (hR i))))
  let qY (i : ι) : YO i ⟶ XO i :=
    structureMap (H.map (f i)) (Over.mk (H.map (D.q (f i) (hR i))))
  let WO (i j : ι) : Over (H.obj U) :=
    (Over.map (H.map (f₂ i j))).obj (Over.mk (H.map (D.q (f₂ i j) (m₂ i j))))
  let WT (i j k : ι) : Over (H.obj U) :=
    (Over.map (H.map (f₃ i j k))).obj (Over.mk (H.map (D.q (f₃ i j k) (m₃ i j k))))
  -- a transition morphism of the diagram, read in the slice
  have hmapw : ∀ {V' W' : BigFppfOver B S hS} {f' : V' ⟶ U} (hf' : R f') {g' : W' ⟶ U}
      (hg' : R g') (α : W' ⟶ V') (hα : α ≫ f' = g'),
      H.map (D.map hf' hg' α hα) ≫ H.map (D.q f' hf') ≫ H.map f' =
        H.map (D.q g' hg') ≫ H.map g' := by
    intro V' W' f' hf' g' hg' α hα
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg H.map (D.map_comp_q_comp hf' hg' α hα)
  -- an equation between composites, transported along `H`
  have hH : ∀ {A X Y Z : BigFppfOver B S hS} {a : A ⟶ X} {b : X ⟶ Z} {a' : A ⟶ Y} {b' : Y ⟶ Z},
      a ≫ b = a' ≫ b' → H.map a ≫ H.map b = H.map a' ≫ H.map b' :=
    fun h => by rw [← H.map_comp, ← H.map_comp, h]
  -- the base change of a cartesian square of the diagram along any morphism to the base
  have hpb : ∀ {V' Y : BigFppfOver B S hS} {f' : V' ⟶ U} (hf' : R f') (k : Y ⟶ U)
      (hg' : R (pullback.fst f' k ≫ f')),
      IsPullback (H.map (D.map hf' hg' (pullback.fst f' k) rfl))
        (H.map (D.q _ hg') ≫ H.map (pullback.snd f' k))
        (H.map (D.q f' hf') ≫ H.map f') (H.map k) := by
    intro V' Y f' hf' k hg'
    have h0 := (D.square hf' hg' _ rfl).paste_vert (IsPullback.of_hasPullback f' k)
    simpa only [Functor.map_comp] using h0.map H
  -- the transition morphisms of the diagram, read in the slice
  let ca (i j : ι) : WO i j ⟶ YO i :=
    Over.homMk (H.map (cc i j)) (hmapw (hR i) (m₂ i j) (pr i j) rfl)
  let cb (i j : ι) : WO i j ⟶ YO j :=
    Over.homMk (H.map (ee i j)) (hmapw (hR j) (m₂ i j) (rr i j) pullback.condition.symm)
  -- an overlap is the product of a cover with a base in two ways
  have hpair : ∀ i j : ι, ∃ (lI : WO i j ≅ YO i ⨯ XO j) (rI : WO i j ≅ XO i ⨯ YO j),
      lI.hom ≫ prod.fst = ca i j ∧ rI.hom ≫ prod.snd = cb i j ∧
      lI.hom ≫ prod.snd = rI.hom ≫ prod.snd ≫ qY j ∧
      rI.hom ≫ prod.fst = lI.hom ≫ prod.fst ≫ qY i := by
    intro i j
    have hbl : (cb i j ≫ qY j).left =
        H.map (D.q (f₂ i j) (m₂ i j)) ≫ H.map (rr i j) := by
      exact hH (D.square (hR j) (m₂ i j) (rr i j) pullback.condition.symm).w
    have hal : (ca i j ≫ qY i).left =
        H.map (D.q (f₂ i j) (m₂ i j)) ≫ H.map (pr i j) := by
      exact hH (D.square (hR i) (m₂ i j) (pr i j) rfl).w
    have h₁ := hpb (hR i) (f j) (m₂ i j)
    have h₂ : IsPullback (H.map (D.q (f₂ i j) (m₂ i j)) ≫ H.map (pr i j)) (H.map (ee i j))
        (H.map (f i)) (H.map (D.q (f j) (hR j)) ≫ H.map (f j)) := by
      have h0 := ((D.square (hR j) (m₂ i j) (rr i j) pullback.condition.symm).paste_vert
        (IsPullback.of_hasPullback (f i) (f j)).flip).flip
      simpa only [Functor.map_comp] using h0.map H
    have hs₁ : IsPullback (ca i j).left (cb i j ≫ qY j).left (YO i).hom (XO j).hom := by
      rwa [hbl]
    have hs₂ : IsPullback (ca i j ≫ qY i).left (cb i j).left (XO i).hom (YO j).hom := by
      rwa [hal]
    obtain ⟨lI, hl₁, hl₂⟩ :=
      Stack.FiniteHilbert.over_exists_product_iso (ca i j) (cb i j ≫ qY j) hs₁
    obtain ⟨rI, hr₁, hr₂⟩ :=
      Stack.FiniteHilbert.over_exists_product_iso (ca i j ≫ qY i) (cb i j) hs₂
    exact ⟨lI, rI, hl₁, hr₂, by rw [hl₂, ← Category.assoc, hr₂],
      by rw [hr₁, ← Category.assoc, hl₁]⟩
  choose lI rI hl hr hp₂ hp₁ using hpair
  let φ (i j : ι) : YO i ⨯ XO j ≅ XO i ⨯ YO j := (lI i j).symm ≪≫ rI i j
  have hφ₁ (i j : ι) : (φ i j).hom ≫ prod.fst = prod.fst ≫ qY i := by
    refine (cancel_epi (lI i j).hom).mp ?_
    simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    exact hp₁ i j
  have hφ₂ (i j : ι) : (φ i j).hom ≫ prod.snd ≫ qY j = prod.snd := by
    refine (cancel_epi (lI i j).hom).mp ?_
    simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    exact (hp₂ i j).symm
  -- the cocycle condition, read on the triple overlaps
  have hcocycle (i j k : ι) : prod.map (φ i j).hom (𝟙 (XO k)) ≫
      prodMapLastTwo (φ j k).hom = prodMapFirstThird (φ i k).hom := by
    let m₁₂ : WT i j k ⟶ WO i j :=
      Over.homMk (H.map (d₁₂ i j k)) (hmapw (m₂ i j) (m₃ i j k) (tt i j k) rfl)
    let m₂₃ : WT i j k ⟶ WO j k :=
      Over.homMk (H.map (d₂₃ i j k)) (hmapw (m₂ j k) (m₃ i j k) (u₂₃ i j k) (hu₂₃ i j k))
    let m₁₃ : WT i j k ⟶ WO i k :=
      Over.homMk (H.map (d₁₃ i j k)) (hmapw (m₂ i k) (m₃ i j k) (u₁₃ i j k) (hu₁₃ i j k))
    let z₃ : WT i j k ⟶ YO k := m₂₃ ≫ cb j k
    let p₃ : WT i j k ⟶ XO k := z₃ ≫ qY k
    have hz : d₂₃ i j k ≫ ee j k ≫ D.q (f k) (hR k) =
        D.q (f₃ i j k) (m₃ i j k) ≫ ss i j k :=
      calc d₂₃ i j k ≫ ee j k ≫ D.q (f k) (hR k)
          = d₂₃ i j k ≫ D.q (f₂ j k) (m₂ j k) ≫ rr j k := by
            rw [(D.square (hR k) (m₂ j k) (rr j k) pullback.condition.symm).w]
        _ = (d₂₃ i j k ≫ D.q (f₂ j k) (m₂ j k)) ≫ rr j k :=
            (Category.assoc _ _ _).symm
        _ = (D.q (f₃ i j k) (m₃ i j k) ≫ u₂₃ i j k) ≫ rr j k := by
            rw [(D.square (m₂ j k) (m₃ i j k) (u₂₃ i j k) (hu₂₃ i j k)).w]
        _ = D.q (f₃ i j k) (m₃ i j k) ≫ u₂₃ i j k ≫ rr j k := Category.assoc _ _ _
        _ = D.q (f₃ i j k) (m₃ i j k) ≫ ss i j k := by
            simp only [u₂₃, rr, pullback.lift_snd]
    have hp₃l : p₃.left = H.map (D.q (f₃ i j k) (m₃ i j k)) ≫ H.map (ss i j k) := by
      show H.map (d₂₃ i j k) ≫ H.map (ee j k) ≫ H.map (D.q (f k) (hR k)) = _
      rw [← H.map_comp, ← H.map_comp, hz, H.map_comp]
    have hT := hpb (m₂ i j) (f k) (m₃ i j k)
    have hsqT : IsPullback m₁₂.left p₃.left (WO i j).hom (XO k).hom := by
      rwa [hp₃l]
    obtain ⟨t₀, ht₁, ht₂⟩ := Stack.FiniteHilbert.over_exists_product_iso m₁₂ p₃ hsqT
    let tI := t₀ ≪≫ prod.mapIso (lI i j) (Iso.refl (XO k))
    let m := m₂₃ ≫ (lI j k).hom
    let n := m₁₃ ≫ (lI i k).hom
    have hm12 : m₁₂ ≫ ca i j = m₁₃ ≫ ca i k := by
      exact Over.OverMorphism.ext (hH (hd₁ i j k))
    have hm23 : m₁₂ ≫ cb i j = m₂₃ ≫ ca j k := by
      exact Over.OverMorphism.ext (hH (hd₂ i j k))
    have hm3 : m₂₃ ≫ cb j k = z₃ := rfl
    have hn3 : m₁₃ ≫ cb i k = z₃ := by
      exact Over.OverMorphism.ext (hH (hd₃ i j k).symm)
    have ht1 : tI.hom ≫ prod.fst = m₁₂ ≫ (lI i j).hom := by
      show (t₀.hom ≫ prod.map (lI i j).hom (𝟙 (XO k))) ≫ prod.fst = _
      rw [Category.assoc, prod.map_fst, ← Category.assoc, ht₁]
    have ht2 : tI.hom ≫ prod.snd = p₃ := by
      show (t₀.hom ≫ prod.map (lI i j).hom (𝟙 (XO k))) ≫ prod.snd = _
      rw [Category.assoc, prod.map_snd, Category.comp_id, ht₂]
    have htphi : tI.hom ≫ prod.fst ≫ (φ i j).hom = m₁₂ ≫ (rI i j).hom := by
      rw [← Category.assoc, ht1]
      simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    refine Stack.FiniteHilbert.productTransition_cocycle (qY i) (qY j) (φ i j).hom (φ j k).hom
      (φ i k).hom (hφ₁ i j) (hφ₂ i j) (hφ₁ j k) (hφ₁ i k) tI m n ?_ ?_ ?_ ?_ ?_
    · show (m₂₃ ≫ (lI j k).hom) ≫ prod.fst = _
      rw [Category.assoc, hl, ← Category.assoc _ _ prod.snd, ← Category.assoc tI.hom, htphi,
        Category.assoc, hr]
      exact hm23.symm
    · show (m₂₃ ≫ (lI j k).hom) ≫ prod.snd = _
      rw [Category.assoc, hp₂, ← Category.assoc (rI j k).hom, hr, ← Category.assoc, hm3, ht2]
    · show (m₁₃ ≫ (lI i k).hom) ≫ prod.fst = _
      rw [Category.assoc, hl, ← Category.assoc _ _ prod.fst, ht1, Category.assoc, hl]
      exact hm12.symm
    · show (m₁₃ ≫ (lI i k).hom) ≫ prod.snd = _
      rw [Category.assoc, hp₂, ← Category.assoc (rI i k).hom, hr, ← Category.assoc, hn3, ht2]
    · show (m₂₃ ≫ (lI j k).hom) ≫ (φ j k).hom ≫ prod.snd =
        (m₁₃ ≫ (lI i k).hom) ≫ (φ i k).hom ≫ prod.snd
      simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
      rw [hr, hr]
      exact hm3.trans hn3.symm
  -- the descent datum of schemes and Stacks 0245
  let E : DescentData (fun i => H.map (f i)) :=
    { obj i := Over.mk (H.map (D.q (f i) (hR i)))
      gluing i j := Over.isoMk (φ i j) (by
        show (φ i j).hom ≫ prod.map (𝟙 (XO i)) (qY j) = prod.map (qY i) (𝟙 (XO j))
        refine prod.hom_ext ?_ ?_
        · simpa only [Category.assoc, prod.map_fst, prod.map_fst_assoc, Category.comp_id]
            using hφ₁ i j
        · simpa only [Category.assoc, prod.map_snd, prod.map_snd_assoc, Category.comp_id]
            using hφ₂ i j)
      cocycle := hcocycle }
  obtain ⟨C⟩ := DescentData.nonempty_chart_of_isFamilyEffective E
    (DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex (fun i => H.map (f i)) hf E haff)
  refine ⟨C.base.left, C.base.hom, C.proj, C.isPullback, fun i j => ?_⟩
  have hgi := (DescentData.isGluingInvariant_iff E C.proj).2 C.compat
  have h' : (φ i j).hom.left ≫ (prod.snd : XO i ⨯ YO j ⟶ YO j).left ≫ C.proj j =
      (prod.fst : YO i ⨯ XO j ⟶ YO i).left ≫ C.proj i := by
    have h := hgi i j
    simp only [Over.comp_left, Category.assoc] at h
    exact h.symm
  have hh := congrArg (fun z => (lI i j).hom.left ≫ z) h'
  have hl' := congrArg Over.Hom.left (hl i j)
  have hr' := congrArg Over.Hom.left (hr i j)
  have he := congrArg Over.Hom.left
    (show (lI i j).hom ≫ (φ i j).hom = (rI i j).hom by simp [φ])
  dsimp only [Over.comp_left] at hl' hr' he
  rw [← Category.assoc (lI i j).hom.left (φ i j).hom.left, he,
    ← Category.assoc (rI i j).hom.left, hr', ← Category.assoc (lI i j).hom.left, hl'] at hh
  exact hh.symm

/-- **The objects of a diagram with cartesian, strictly composable transition squares, whose
structure morphisms are finite étale, descend to a finite étale object over the base of the
sieve.** The descended scheme is produced by
`AlgebraicGeometry.cartesianSieveDiagram_exists_scheme_cocone`; it is again finite étale over the
base because being finite étale is fpqc local there, and it satisfies the size cutoff of the site
because a finite étale morphism is quasi-compact and locally of finite type, so the whole cocone
lifts back into the big fppf category over `S`. -/
theorem cartesianSieveDiagram_exists_site_cocone {U : BigFppfOver B S hS} {R : Sieve U}
    (D : CartesianSieveDiagram R) {ι : Type v} {V : ι → BigFppfOver B S hS}
    (f : ∀ i, V i ⟶ U) (hR : ∀ i, R (f i))
    (hf : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (V i))
      (fun i => (BigFppfOver.toScheme B S hS).map (f i)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj U))
    (hfe : ∀ i, (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})
      ((BigFppfOver.toScheme B S hS).map (D.q (f i) (hR i)))) :
    ∃ (Z : BigFppfOver B S hS) (pz : Z ⟶ U) (g : ∀ i, D.obj (f i) (hR i) ⟶ Z),
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})
          ((BigFppfOver.toScheme B S hS).map pz) ∧
        (∀ i, IsPullback (g i) (D.q (f i) (hR i)) pz (f i)) ∧
        ∀ {W : BigFppfOver B S hS} (i j : ι) (α : W ⟶ V i) (β : W ⟶ V j)
          (hαβ : α ≫ f i = β ≫ f j),
          D.map (hR i) (R.downward_closed (hR i) α) α rfl ≫ g i =
            D.map (hR j) (R.downward_closed (hR i) α) β hαβ.symm ≫ g j := by
  classical
  have := hasPullbacks_bigFppfOver B S hS
  let H := BigFppfOver.toScheme B S hS
  have hbc : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf
  obtain ⟨Z, pz, g, hsq, hglue⟩ := cartesianSieveDiagram_exists_scheme_cocone B S hS D f hR hf
    fun i => isFinite_inf_etale_le_isAffineHom _ (hfe i)
  -- the descended morphism is finite étale, so `Z` is an object of the site
  have hpz : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) pz := by
    refine isFinite_inf_etale_of_fpqcCover _ _ hf pz fun i => ?_
    have hs : IsPullback (hsq i).isoPullback.inv (pullback.snd pz (H.map (f i)))
        (H.map (D.q (f i) (hR i))) (𝟙 (H.obj (V i))) := by
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      rw [Category.comp_id, Iso.inv_comp_eq]
      exact (hsq i).isoPullback_hom_snd.symm
    exact MorphismProperty.of_isPullback hs (hfe i)
  have hz : B.Contains Z := contains_of_isFinite_inf_etale B pz U.left.property hpz
  let q₀ : B.obj hz ⟶ U.left := B.inclusion.preimage pz
  let Z' : BigFppfOver B S hS := Over.mk (q₀ ≫ U.hom)
  let pz' : Z' ⟶ U := Over.homMk q₀
  have hq₀ : B.inclusion.map q₀ = pz :=
    B.inclusion.map_preimage (X := B.obj hz) (Y := U.left) pz
  let g₀ (i : ι) : (D.obj (f i) (hR i)).left ⟶ B.obj hz := B.inclusion.preimage (g i)
  have hg₀map (i : ι) : B.inclusion.map (g₀ i) = g i :=
    B.inclusion.map_preimage (X := (D.obj (f i) (hR i)).left) (Y := B.obj hz) (g i)
  have hg₀ (i : ι) : g₀ i ≫ q₀ = (D.q (f i) (hR i)).left ≫ (f i).left := by
    refine B.inclusion.map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hq₀, hg₀map]
    exact (hsq i).w
  let g' (i : ι) : D.obj (f i) (hR i) ⟶ Z' := Over.homMk (g₀ i) (by
    show g₀ i ≫ (q₀ ≫ U.hom) = (D.obj (f i) (hR i)).hom
    rw [← Category.assoc, hg₀ i, Category.assoc, Over.w, Over.w])
  have hpz'map : H.map pz' = pz := hq₀
  have hg'map (i : ι) : H.map (g' i) = g i := hg₀map i
  refine ⟨Z', pz', g', ?_, ?_, ?_⟩
  · rwa [hpz'map]
  · exact fun i => IsPullback.of_map_of_faithful H (by simpa only [hpz'map, hg'map] using hsq i)
  · intro W i j α β hαβ
    refine H.map_injective ?_
    have hl : pullback.lift α β hαβ ≫ (pullback.fst (f i) (f j) ≫ f i) = α ≫ f i := by
      rw [← Category.assoc, pullback.lift_fst]
    have hm₁ : D.map (R.downward_closed (hR i) (pullback.fst (f i) (f j)))
          (R.downward_closed (hR i) α) (pullback.lift α β hαβ) hl ≫
        D.map (hR i) (R.downward_closed (hR i) (pullback.fst (f i) (f j)))
          (pullback.fst (f i) (f j)) rfl =
        D.map (hR i) (R.downward_closed (hR i) α) α rfl := by
      rw [D.map_comp]
      simp only [pullback.lift_fst]
    have hm₂ : D.map (R.downward_closed (hR i) (pullback.fst (f i) (f j)))
          (R.downward_closed (hR i) α) (pullback.lift α β hαβ) hl ≫
        D.map (hR j) (R.downward_closed (hR i) (pullback.fst (f i) (f j)))
          (pullback.snd (f i) (f j)) pullback.condition.symm =
        D.map (hR j) (R.downward_closed (hR i) α) β hαβ.symm := by
      rw [D.map_comp]
      simp only [pullback.lift_snd]
    have hh := congrArg (fun z => H.map (D.map
      (R.downward_closed (hR i) (pullback.fst (f i) (f j))) (R.downward_closed (hR i) α)
      (pullback.lift α β hαβ) hl) ≫ z) (hglue i j)
    rw [← H.map_comp_assoc, ← H.map_comp_assoc, hm₁, hm₂] at hh
    simpa only [Functor.map_comp, hg'map] using hh

end SieveDiagram

/-! ### Condition (3) of Stacks 026F for `FÉt` -/

section Effectivity

open Stack.FiniteHilbert

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : BigFppfOver B S hS} {R : Sieve U}
  (Dd : Functor.SieveDescentDatum (finiteEtaleProjection B S hS) R)

/-- The base component of a transition morphism of a descent datum of `FÉt` relative to a sieve
is the factorisation it is taken along. -/
lemma finiteEtaleDatumMap_right {V W : BigFppfOver B S hS} {f : V ⟶ U} (hf : R f)
    {g : W ⟶ U} (hg : R g) (α : W ⟶ V) (hα : α ≫ f = g) :
    (sieveDatumMap Dd hf hg α hα).right =
      eqToHom (Dd.obj g hg).2 ≫ α ≫ eqToHom (Dd.obj f hf).2.symm := by
  have := (sieveDatumMap_cartesian Dd hf hg α hα).toIsHomLift
  exact CategoryTheory.IsHomLift.fac' (finiteEtaleProjection B S hS) α
    (sieveDatumMap Dd hf hg α hα)

/-- **The total spaces of a descent datum of `FÉt` relative to a sieve form a diagram with
cartesian, strictly composable transition squares.** Cartesianness is
`AlgebraicGeometry.finiteEtaleProjection_isPullback_of_isCartesian` applied to the transition
morphisms of the datum, and strict composability is their strict composability in `FÉt`. -/
def finiteEtaleSourceDiagram : CartesianSieveDiagram R where
  obj f hf := (Dd.obj f hf).1.left
  q f hf := (Dd.obj f hf).1.hom ≫ eqToHom (Dd.obj f hf).2
  map {_V _W _f} hf {_g} hg α hα := (sieveDatumMap Dd hf hg α hα).left
  square {_V _W f} hf {g} hg α hα :=
    finiteEtaleProjection_isPullback_of_isCartesian B S hS α (sieveDatumMap Dd hf hg α hα)
      (Dd.obj g hg).2 (Dd.obj f hf).2 (sieveDatumMap_cartesian Dd hf hg α hα)
  map_comp {_V _W _Z _f} hf {_g} hg {_b} hb α α' hα hα' :=
    congrArg (fun z => z.left) (sieveDatumMap_comp Dd hf hg hb α α' hα hα')

/-- **Effectivity of a descent datum of `FÉt` from a cocone on it.** An object of the fibre over
the base of the sieve together with a cartesian morphism from every object of the datum,
compatible with the transition morphisms, is effectivity: the compatibility with the gluing
isomorphisms that effectivity asks for is the compatibility of the transition morphisms with
those isomorphisms, `AlgebraicGeometry.Stack.FiniteHilbert.sieveDatumMap_glue`. -/
theorem finiteEtaleProjection_isEffective_of_cocone
    (x : (finiteEtaleProjection B S hS).Fiber U)
    (ζ : ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ U) (hf : R f), (Dd.obj f hf).1 ⟶ x.1)
    (hcart : ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ U) (hf : R f),
      (finiteEtaleProjection B S hS).IsCartesian f (ζ f hf))
    (hnat : ∀ ⦃V W : BigFppfOver B S hS⦄ {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
      (α : W ⟶ V) (hα : α ≫ f = g), sieveDatumMap Dd hf hg α hα ≫ ζ f hf = ζ g hg) :
    Dd.IsEffective := by
  refine ⟨x, ζ, hcart, ?_⟩
  intro _V _W _Z f hf g hg ε ε' heq
  have hi := sieveDatumMap_glue Dd hf hg (R.downward_closed hf ε) ε ε' rfl heq.symm
  have hj := sieveDatumMap_glue Dd hf hf (R.downward_closed hf ε) ε ε rfl rfl
  rw [Dd.iso_self, CategoryTheory.Functor.map_id, Category.id_comp] at hj
  have hi' := congrArg (fun z => z ≫ ζ g hg) hi
  have hj' := congrArg (fun z => z ≫ ζ f hf) hj
  simp only [Category.assoc] at hi' hj'
  rw [hnat] at hi' hj'
  exact hi'.symm.trans hj'

end Effectivity

/-! ### Stacks 0BLZ -/

section Stack

open Stack.FiniteHilbert

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (3) of Stacks 026F for `FÉt`.** Every descent datum of `FÉt` relative to a
covering sieve of the big fppf category over `S` is effective.

The covering sieve is first refined by a covering family whose underlying family of schemes is an
fpqc covering family, which is legitimate because the morphism presheaves of `p` are sheaves. The
total spaces of the datum restricted to that family then descend by Stacks 0245 together with
Stacks 02LA and Stacks 02VN — a finite étale morphism is affine and being finite étale is fpqc
local on the base — and the resulting cocone is extended to the whole sieve by subcanonicality of
the site. -/
theorem finiteEtaleProjection_hasEffectiveDescent :
    (finiteEtaleProjection B S hS).HasEffectiveDescent (BigFppfOver.topology B S hS) := by
  classical
  refine Functor.hasEffectiveDescent_of_familyRefinements
    (fun W x y => finiteEtaleProjection_isMorSheaf B S hS W x y) ?_
  intro U R hRmem
  obtain ⟨I, X, fX, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨E, hEmem, hEle, hEfpqc⟩ := exists_fpqc_cover_refining B S hS X fX hRmem
  refine ⟨E.I₀, E.X, E.f, hEle, hEmem, ?_⟩
  intro Dd
  have hRE : ∀ i, (Sieve.ofArrows E.X E.f) (E.f i) := fun i => Sieve.ofArrows_mk E.X E.f i
  -- the structure morphisms of the diagram are finite étale
  have htransport : ∀ {A T T' : BigFppfOver B S hS} (α : A ⟶ T) (h : T = T'),
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})
          ((BigFppfOver.toScheme B S hS).map α) →
        (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})
          ((BigFppfOver.toScheme B S hS).map (α ≫ eqToHom h)) := by
    intro A T T' α h hα
    cases h
    simpa using hα
  have hfe : ∀ i, (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})
      ((BigFppfOver.toScheme B S hS).map
        ((finiteEtaleSourceDiagram B S hS Dd).q (E.f i) (hRE i))) := fun i =>
    htransport _ _ (Dd.obj (E.f i) (hRE i)).1.prop
  -- the total spaces descend over the family, and the cocone extends to the sieve
  obtain ⟨Z, pz, g, hpz, hsq, hglue⟩ := cartesianSieveDiagram_exists_site_cocone B S hS
    (finiteEtaleSourceDiagram B S hS Dd) E.f hRE hEfpqc hfe
  obtain ⟨ζ, hζsq, hζnat⟩ := (finiteEtaleSourceDiagram B S hS Dd).exists_cocone
    E.f hEmem hRE pz g hsq hglue
  have hw : ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ U) (hf : (Sieve.ofArrows E.X E.f) f),
      ζ f hf ≫ pz =
        (Dd.obj f hf).1.hom ≫ eqToHom (Dd.obj f hf).2 ≫ f := fun {V} f hf =>
    (hζsq f hf).w.trans (Category.assoc _ _ _)
  refine finiteEtaleProjection_isEffective_of_cocone B S hS Dd
    ⟨MorphismProperty.Arrow.mk pz hpz, rfl⟩
    (fun {V} f hf => MorphismProperty.Arrow.homMk (ζ f hf)
      (eqToHom (Dd.obj f hf).2 ≫ f) (hw f hf)) ?_ ?_
  · intro V f hf
    -- The base component of the cocone morphism already is the composite the lemma asks for, up to
    -- the identity it carries as an `eqToHom` along `rfl`.  The identification is a term: the two
    -- sides are typed through the base of the cover and through the projection applied to it.
    refine finiteEtaleProjection_isCartesian_of_isPullback_eqToHom B S hS f _
      (Dd.obj f hf).2 rfl
      ((Category.comp_id (eqToHom (Dd.obj f hf).2 ≫ f)).symm.trans (Category.assoc _ _ _)) ?_
    show IsPullback (ζ f hf) ((finiteEtaleSourceDiagram B S hS Dd).q f hf)
      (pz ≫ eqToHom rfl) f
    simpa only [eqToHom_refl, Category.comp_id] using hζsq f hf
  · intro V W f hf g hg α hα
    refine MorphismProperty.Arrow.Hom.ext (hζnat hf hg α hα) ?_
    show (sieveDatumMap Dd hf hg α hα).right ≫ eqToHom (Dd.obj f hf).2 ≫ f =
      eqToHom (Dd.obj g hg).2 ≫ g
    -- The chain is written out rather than rewritten: the base component of a transition morphism
    -- is typed through the projection applied to the component of the datum, the identification of
    -- the bases is typed through the base itself, and the two meet in every intermediate goal
    -- here, so only term elaboration can read them as the same object.
    have hcancel {A A' : BigFppfOver B S hS} (h : A = A') (k : A' ⟶ U) :
        eqToHom h.symm ≫ eqToHom h ≫ k = k := by
      cases h
      simp
    refine Eq.trans (congrArg (· ≫ eqToHom (Dd.obj f hf).2 ≫ f)
      (finiteEtaleDatumMap_right B S hS Dd hf hg α hα)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (eqToHom (Dd.obj g hg).2 ≫ ·) (Category.assoc _ _ _)) ?_
    refine Eq.trans (congrArg (fun z => eqToHom (Dd.obj g hg).2 ≫ α ≫ z)
      (hcancel (Dd.obj f hf).2 f)) ?_
    exact congrArg (eqToHom (Dd.obj g hg).2 ≫ ·) hα

/-- **Stacks 0BLZ.** The functor `p : FÉt ⟶ (Sch/S)_fppf` of Stacks 0BLY defines a stack over
the big fppf site of `S`: it satisfies the three conditions of Stacks 026F.

Condition (1) is `AlgebraicGeometry.finiteEtaleProjection_isFibered`, condition (2) is
`AlgebraicGeometry.finiteEtaleProjection_isMorSheaf` and condition (3) is
`AlgebraicGeometry.finiteEtaleProjection_hasEffectiveDescent`. -/
@[stacks 0BLZ]
theorem finiteEtaleProjection_isStack :
    Functor.IsStack (finiteEtaleProjection B S hS) (BigFppfOver.topology B S hS) where
  isFibered := inferInstance
  isMorSheaf U x y := finiteEtaleProjection_isMorSheaf B S hS U x y
  hasEffectiveDescent := finiteEtaleProjection_hasEffectiveDescent B S hS

end Stack

end AlgebraicGeometry

end

end
