module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Limits
public import StacksFrontier.CategoryTheory.Sites.CoveringPermanence

/-!
# Fibre products of hypercoverings

Let `C` be a site given by a pretopology `J`, let `C` have fibre products and let `X : C`. If `K`
is a hypercovering of `X` and `b : M ⟶ L` is a morphism of simplicial semi-representable objects
over `X` which is covering in degree zero and covering relative to every successive matching
object, then the degreewise fibre product `K ×_L M` is again a hypercovering of `X`.

The relative matching condition is the statement that the canonical morphism from `M_{n + 1}` to
the fibre product of the matching object of `L` in degree `n + 1` with the matching object of
`M` is covering; it is the `pullback.lift` appearing in the hypothesis `hmatching` of
`isHypercovering_fibreProduct`. The degreewise fibre product `SimplicialObject.fibreProduct` is
the pointwise fibre product `Limits.pointwisePullback` of a cospan of functors.

The indexed-family composition axiom of a site (Tag 00VH (2)) is the instance assumption
`Precoverage.IsStableUnderComposition J.toPrecoverage`; Mathlib's presieve-level `Pretopology`
does not provide it.

## Main definitions

* `CategoryTheory.Limits.pointwisePullback.fst` and `.snd`: the two projections of a pointwise
  fibre product of functors, as natural transformations.
* `relativePullbackIso`: for `p : P ⟶ S`, `q : Q ⟶ T`, `r : R ⟶ U` over `s : S ⟶ T`,
  `t : U ⟶ T` and `f : P ⟶ Q`, `g : R ⟶ Q` with `p ≫ s = f ≫ q` and `g ≫ q = r ≫ t`, the
  isomorphism of `P ×_Q R` with the fibre product of `P ×_S (S ×_T U) ⟶ Q ×_T U` and
  `R ⟶ Q ×_T U`.
* `matchingObjectFunctor` and `matchingObjectFibreProductIso`: the functor taking a simplicial
  semi-representable object to its matching object in degree `n + 1`, and the identification of
  the matching object of a degreewise fibre product with the fibre product of the matching
  objects.

## Main results

* `CategoryTheory.Limits.isPullback_pointwisePullback`: a pointwise fibre product of functors is
  a fibre product in the functor category.
* `IsCoveringOver.of_isIso_comp`, `IsCoveringOver.isIso_comp`, `IsCoveringOver.pullback_fst` and
  `IsCoveringOver.pullback_snd`: consequences of Tag 01G4 — a covering morphism may be
  recognised after composing with an isomorphism on either side, and the projections of a fibre
  product are covering as soon as the opposite morphism of the cospan is.
* `isCoveringOver_relativePullbackLift`: the morphism `P ×_Q R ⟶ S ×_T U` induced by `p` and `r`
  is covering as soon as `p` is and the comparison `R ⟶ Q ×_T U` of the other leg is.
* `isHypercovering_fibreProduct`: a degreewise fibre product with a hypercovering, along a
  morphism covering in degree zero and on every relative matching object, is a hypercovering.

## References

* [Stacks Project, Tag 01GH](https://stacks.math.columbia.edu/tag/01GH)
-/

@[expose] public section

universe w v₁ u₁ v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject.Truncated

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u} [Category.{v} D] {F G H : D ⥤ C}
  (f : F ⟶ H) (g : G ⟶ H) [∀ d, HasPullback (f.app d) (g.app d)]

/-- The first projection of a pointwise fibre product of functors. -/
@[simps] noncomputable def pointwisePullback.fst : pointwisePullback f g ⟶ F where
  app d := pullback.fst (f.app d) (g.app d)
  naturality _ _ _ := pullback.lift_fst _ _ _

/-- The second projection of a pointwise fibre product of functors. -/
@[simps] noncomputable def pointwisePullback.snd : pointwisePullback f g ⟶ G where
  app d := pullback.snd (f.app d) (g.app d)
  naturality _ _ _ := pullback.lift_snd _ _ _

/-- A pointwise fibre product of functors is a fibre product in the functor category. -/
theorem isPullback_pointwisePullback :
    IsPullback (pointwisePullback.fst f g) (pointwisePullback.snd f g) f g :=
  IsPullback.of_forall_isPullback_app fun d ↦ IsPullback.of_hasPullback (f.app d) (g.app d)

end CategoryTheory.Limits

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-! ### Small consequences of Tag 01G4 -/

section Covering

variable (J : Pretopology C) {X : C}

/-- A morphism is covering as soon as it is covering after precomposing with an
isomorphism. -/
theorem IsCoveringOver.of_isIso_comp [Precoverage.IsStableUnderComposition J.toPrecoverage]
    {U U' V : FormalCoproduct.{w} (Over X)} (e : U ⟶ U') [IsIso e] {f : U' ⟶ V}
    (h : IsCoveringOver J (e ≫ f)) : IsCoveringOver J f := by
  simpa [Category.assoc] using (IsCoveringOver.of_isIso J (inv e)).comp J h

/-- Precomposing a covering morphism with an isomorphism gives a covering morphism. -/
theorem IsCoveringOver.isIso_comp [Precoverage.IsStableUnderComposition J.toPrecoverage]
    {U U' V : FormalCoproduct.{w} (Over X)} (e : U ⟶ U') [IsIso e] {f : U' ⟶ V}
    (h : IsCoveringOver J f) : IsCoveringOver J (e ≫ f) :=
  (IsCoveringOver.of_isIso J e).comp J h

/-- **Stacks Project, Tag 01G4, part (2)**, for the chosen fibre product: the second projection
of a fibre product of semi-representable objects over `X` is covering as soon as the first
morphism of the cospan is. -/
theorem IsCoveringOver.pullback_snd [Precoverage.IsStableUnderComposition J.toPrecoverage]
    {U V W : FormalCoproduct.{w} (Over X)} (f : U ⟶ V) (g : W ⟶ V)
    (hf : IsCoveringOver J f) : IsCoveringOver J (Limits.pullback.snd f g) :=
  IsCoveringOver.of_isPullback J (IsPullback.of_hasPullback f g) hf

/-- **Stacks Project, Tag 01G4, part (2)**, for the chosen fibre product: the first projection
of a fibre product of semi-representable objects over `X` is covering as soon as the second
morphism of the cospan is. -/
theorem IsCoveringOver.pullback_fst [Precoverage.IsStableUnderComposition J.toPrecoverage]
    {U V W : FormalCoproduct.{w} (Over X)} (f : U ⟶ V) (g : W ⟶ V)
    (hg : IsCoveringOver J g) : IsCoveringOver J (Limits.pullback.fst f g) :=
  IsCoveringOver.of_isPullback J (IsPullback.of_hasPullback f g).flip hg

end Covering

/-! ### The relative fibre product -/

section Relative

variable {D : Type u₁} [Category.{v₁} D] [HasPullbacks D]

/-- The comparison isomorphism identifying `P ×_Q R` with the fibre product of the morphism
`P ×_S (S ×_T U) ⟶ Q ×_T U` induced by `f` and the morphism `R ⟶ Q ×_T U` induced by `g`
and `r`. -/
noncomputable def relativePullbackIso {P Q R S T U : D} (f : P ⟶ Q) (g : R ⟶ Q)
    (p : P ⟶ S) (q : Q ⟶ T) (r : R ⟶ U) (s : S ⟶ T) (t : U ⟶ T)
    (hp : p ≫ s = f ≫ q) (hr : g ≫ q = r ≫ t) :
    Limits.pullback f g ≅
      Limits.pullback
        (Limits.pullback.lift (Limits.pullback.fst p (Limits.pullback.fst s t) ≫ f)
          (Limits.pullback.snd p (Limits.pullback.fst s t) ≫ Limits.pullback.snd s t)
          (by simp [Limits.pullback.condition_assoc, Limits.pullback.condition,
            Category.assoc, ← hp]))
        (Limits.pullback.lift g r hr) := by
  let h : Limits.pullback p (Limits.pullback.fst s t) ⟶ Limits.pullback q t :=
    Limits.pullback.lift (Limits.pullback.fst p (Limits.pullback.fst s t) ≫ f)
      (Limits.pullback.snd p (Limits.pullback.fst s t) ≫ Limits.pullback.snd s t)
      (by simp [Limits.pullback.condition_assoc, Limits.pullback.condition,
        Category.assoc, ← hp])
  let γ : R ⟶ Limits.pullback q t := Limits.pullback.lift g r hr
  let c : Limits.pullback f g ⟶ Limits.pullback s t :=
    Limits.pullback.lift (Limits.pullback.fst f g ≫ p) (Limits.pullback.snd f g ≫ r)
      (by simp [Limits.pullback.condition_assoc, Category.assoc, hp, hr])
  let d : Limits.pullback f g ⟶ Limits.pullback p (Limits.pullback.fst s t) :=
    Limits.pullback.lift (Limits.pullback.fst f g) c (by simp [c])
  have hd : d ≫ h = Limits.pullback.snd f g ≫ γ := by
    apply Limits.pullback.hom_ext
    · simp [Limits.pullback.condition, d, h, γ, c, Category.assoc]
    · simp [d, h, γ, c, Category.assoc]
  let hom : Limits.pullback f g ⟶ Limits.pullback h γ :=
    Limits.pullback.lift d (Limits.pullback.snd f g) hd
  let inv : Limits.pullback h γ ⟶ Limits.pullback f g :=
    Limits.pullback.lift
      (Limits.pullback.fst h γ ≫ Limits.pullback.fst p (Limits.pullback.fst s t))
      (Limits.pullback.snd h γ) (by
        have he := congrArg (fun z : Limits.pullback h γ ⟶ Limits.pullback q t ↦
          z ≫ Limits.pullback.fst q t) (Limits.pullback.condition (f := h) (g := γ))
        simpa only [h, γ, Category.assoc, Limits.pullback.lift_fst_assoc,
          Limits.pullback.lift_fst] using he)
  refine { hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply Limits.pullback.hom_ext
    · simp [hom, inv, d, c, h, γ, Category.assoc]
    · simp [hom, inv, d, c, h, γ, Category.assoc]
  · apply Limits.pullback.hom_ext
    · apply Limits.pullback.hom_ext
      · simp [hom, inv, d, c, h, γ, Category.assoc]
      · apply Limits.pullback.hom_ext
        · simp [Limits.pullback.condition, hom, inv, d, c, h, γ, Category.assoc]
        · have he := congrArg (fun z : Limits.pullback h γ ⟶ Limits.pullback q t ↦
              z ≫ Limits.pullback.snd q t) (Limits.pullback.condition (f := h) (g := γ))
          simp [hom, inv, d, c, h, γ, Category.assoc]
          simpa [h, γ, Category.assoc, Limits.pullback.lift_snd_assoc,
            Limits.pullback.lift_snd] using he.symm
    · simp [hom, inv, d, c, h, γ, Category.assoc]

end Relative

/-- The morphism `P ×_Q R ⟶ S ×_T U` induced by `p` and `r` is covering as soon as `p` is
covering and the comparison `R ⟶ Q ×_T U` of the other leg is. -/
theorem isCoveringOver_relativePullbackLift (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {P Q R S T U : FormalCoproduct.{w} (Over X)} (f : P ⟶ Q) (g : R ⟶ Q) (p : P ⟶ S)
    (q : Q ⟶ T) (r : R ⟶ U) (s : S ⟶ T) (t : U ⟶ T) (hp : p ≫ s = f ≫ q)
    (hr : g ≫ q = r ≫ t) (hpcover : IsCoveringOver J p)
    (hrcover : IsCoveringOver J (Limits.pullback.lift g r hr)) :
    IsCoveringOver J
      (Limits.pullback.lift (f := s) (g := t) (Limits.pullback.fst f g ≫ p)
        (Limits.pullback.snd f g ≫ r)
        (by simp [Category.assoc, hp, hr, Limits.pullback.condition_assoc])) := by
  let h : Limits.pullback p (Limits.pullback.fst s t) ⟶ Limits.pullback q t :=
    Limits.pullback.lift (Limits.pullback.fst p (Limits.pullback.fst s t) ≫ f)
      (Limits.pullback.snd p (Limits.pullback.fst s t) ≫ Limits.pullback.snd s t)
      (by simp [Category.assoc, ← hp, Limits.pullback.condition_assoc,
        Limits.pullback.condition])
  let γ : R ⟶ Limits.pullback q t := Limits.pullback.lift g r hr
  let e := relativePullbackIso f g p q r s t hp hr
  have hbase : IsCoveringOver J (Limits.pullback.snd γ h) :=
    IsCoveringOver.pullback_snd J γ h hrcover
  have hfirst : IsCoveringOver J (e.hom ≫ Limits.pullback.fst h γ) :=
    IsCoveringOver.isIso_comp J e.hom
      (IsCoveringOver.of_isIso_comp J (pullbackSymmetry γ h).hom (by simpa using hbase))
  have hcomp := hfirst.comp J
    (IsCoveringOver.pullback_snd J p (Limits.pullback.fst s t) hpcover)
  have heq : (e.hom ≫ Limits.pullback.fst h γ) ≫
      Limits.pullback.snd p (Limits.pullback.fst s t) =
      Limits.pullback.lift (f := s) (g := t) (Limits.pullback.fst f g ≫ p)
        (Limits.pullback.snd f g ≫ r)
        (by simp [Category.assoc, hp, hr, Limits.pullback.condition_assoc]) := by
    apply Limits.pullback.hom_ext <;>
      simp [e, relativePullbackIso, h, γ]
  exact heq ▸ hcomp

/-! ### Tag 01GH -/

section Hypercovering

variable {X : C}

/-- Truncating simplicial semi-representable objects preserves fibre products. -/
instance preservesPullbacks_truncation (n : ℕ) :
    PreservesLimitsOfShape WalkingCospan
      (SimplicialObject.truncation n :
        SimplicialObject (FormalCoproduct.{w} (Over X)) ⥤ _) := by
  change PreservesLimitsOfShape WalkingCospan
    ((Functor.whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n).op)
  infer_instance

/-- The matching-object functor in degree `n + 1`: truncate, take the coskeleton and
evaluate. -/
noncomputable abbrev matchingObjectFunctor (n : ℕ) :
    SimplicialObject (FormalCoproduct.{w} (Over X)) ⥤ FormalCoproduct.{w} (Over X) :=
  (SimplicialObject.truncation n : SimplicialObject (FormalCoproduct.{w} (Over X)) ⥤ _) ⋙
    SimplicialObject.Truncated.cosk n ⋙ (evaluation _ _).obj (op ⦋n + 1⦌)

/-- The matching-object functor in degree `n + 1` preserves fibre products. -/
instance preservesPullbacks_matchingObjectFunctor (n : ℕ) :
    PreservesLimitsOfShape WalkingCospan (matchingObjectFunctor.{w} (X := X) n) :=
  inferInstance

variable {K L M : SimplicialObject (FormalCoproduct.{w} (Over X))}

/-- The matching object of a degreewise fibre product is the fibre product of the matching
objects. -/
noncomputable def matchingObjectFibreProductIso (a : K ⟶ L) (b : M ⟶ L) (n : ℕ) :
    (matchingObjectFunctor n).obj (SimplicialObject.fibreProduct a b) ≅
      Limits.pullback ((matchingObjectFunctor n).map a) ((matchingObjectFunctor n).map b) :=
  ((isPullback_pointwisePullback a b).map (matchingObjectFunctor n)).isoIsPullback _ _
    (IsPullback.of_hasPullback _ _)

/-- A fibre product with a hypercovering is a hypercovering when the other morphism is covering
in degree zero and on every relative matching object. -/
@[stacks 01GH]
theorem isHypercovering_fibreProduct (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {K L M : SimplicialObject (FormalCoproduct.{w} (Over X))} (a : K ⟶ L) (b : M ⟶ L)
    (hK : IsHypercovering J K)
    (h₀ : IsCoveringOver J (b.app (op ⦋0⦌)))
    (hmatching : ∀ n : ℕ, IsCoveringOver J
      (Limits.pullback.lift
        (f := (((SimplicialObject.coskAdj n).unit.app L).app (op ⦋n + 1⦌)))
        (g := (((SimplicialObject.Truncated.cosk n).map
          ((SimplicialObject.truncation n).map b)).app (op ⦋n + 1⦌)))
        (b.app (op ⦋n + 1⦌))
        (((SimplicialObject.coskAdj n).unit.app M).app (op ⦋n + 1⦌))
        (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality b)
          (op ⦋n + 1⦌)))) :
    IsHypercovering J (SimplicialObject.fibreProduct a b) := by
  refine ⟨?_, ?_⟩
  · have hcomp := (IsCoveringOver.pullback_fst J (a.app (op ⦋0⦌)) _ h₀).comp J hK.1
    have hEq : Limits.pullback.fst (a.app (op ⦋0⦌)) (b.app (op ⦋0⦌)) ≫
        terminal.from (K.obj (op ⦋0⦌)) =
        terminal.from ((SimplicialObject.fibreProduct a b).obj (op ⦋0⦌)) :=
      terminal.hom_ext _ _
    exact hEq ▸ hcomp
  · intro n
    let i := op (⦋n + 1⦌ : SimplexCategory)
    let F := matchingObjectFunctor.{w} (X := X) n
    let p := (((SimplicialObject.coskAdj n).unit.app K).app i)
    let q := (((SimplicialObject.coskAdj n).unit.app L).app i)
    let r := (((SimplicialObject.coskAdj n).unit.app M).app i)
    have nat : ∀ {A B : SimplicialObject (FormalCoproduct.{w} (Over X))} (φ : A ⟶ B),
        ((SimplicialObject.coskAdj n).unit.app A).app i ≫ F.map φ =
          φ.app i ≫ ((SimplicialObject.coskAdj n).unit.app B).app i := fun φ ↦
      (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality φ) i).symm
    have hp : p ≫ F.map a = a.app i ≫ q := nat a
    have hr : b.app i ≫ q = r ≫ F.map b := (nat b).symm
    let c : Limits.pullback (a.app i) (b.app i) ⟶ Limits.pullback (F.map a) (F.map b) :=
      Limits.pullback.lift (Limits.pullback.fst (a.app i) (b.app i) ≫ p)
        (Limits.pullback.snd (a.app i) (b.app i) ≫ r)
        (by simp [Category.assoc, hp, hr, Limits.pullback.condition_assoc])
    have hrel : IsCoveringOver J c :=
      isCoveringOver_relativePullbackLift J (a.app i) (b.app i) p q r (F.map a) (F.map b)
        hp hr (hK.2 n) (hmatching n)
    let e := matchingObjectFibreProductIso a b n
    have hproj₁ : e.hom ≫ Limits.pullback.fst (F.map a) (F.map b) =
        F.map (pointwisePullback.fst a b) :=
      ((isPullback_pointwisePullback a b).map F).isoIsPullback_hom_fst _ _
        (IsPullback.of_hasPullback (F.map a) (F.map b))
    have hproj₂ : e.hom ≫ Limits.pullback.snd (F.map a) (F.map b) =
        F.map (pointwisePullback.snd a b) :=
      ((isPullback_pointwisePullback a b).map F).isoIsPullback_hom_snd _ _
        (IsPullback.of_hasPullback (F.map a) (F.map b))
    let u := ((SimplicialObject.coskAdj n).unit.app (SimplicialObject.fibreProduct a b)).app i
    have heq : u ≫ e.hom = c := by
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, hproj₁]
        exact (nat (pointwisePullback.fst a b)).trans (Limits.pullback.lift_fst _ _ _).symm
      · rw [Category.assoc, hproj₂]
        exact (nat (pointwisePullback.snd a b)).trans (Limits.pullback.lift_snd _ _ _).symm
    change IsCoveringOver J u
    exact IsCoveringOver.of_comp_isIso J e.hom (heq ▸ hrel)

end Hypercovering

end Stacks.CategoryTheory.Hypercovering

end
