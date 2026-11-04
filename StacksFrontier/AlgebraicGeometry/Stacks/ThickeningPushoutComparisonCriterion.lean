module

public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso

/-!
# A gluing criterion for the comparison functor of a square

Let `p : 𝒳 ⥤ 𝒮` be fibred in groupoids and let `f ≫ b = i ≫ a` be a commutative square
`X ⟶ Y ⟶ Y'`, `X ⟶ X' ⟶ Y'` of `𝒮`. The comparison functor
`𝒳_{Y'} ⥤ 𝒳_Y ×_{𝒳_X} 𝒳_{X'}` of `Deformation.Artin.fiberSquareComparison` is an equivalence as
soon as

* **objects glue**: for every span `y ← x → z` of `𝒳` over `Y ← X → X'` there are an object `t`
  over `Y'` and morphisms `y ⟶ t`, `z ⟶ t` over `b` and `a` completing it to a commutative
  square; and
* **morphisms glue**: for `t`, `t'` over `Y'` and morphisms `r : y ⟶ t`, `s : z ⟶ t` over `b`
  and `a`, a pair of morphisms `y ⟶ t'`, `z ⟶ t'` over `b` and `a` agreeing on every common
  lift of `X` is the composite of `r` and `s` with exactly one morphism `t ⟶ t'` of the fibre
  over `Y'`.

These are the two halves of the conditions of Stacks 07WP and 07Y8 written on spans rather than
on the two-fibre product of the fibres, and they are what is checked for a concrete fibred
category such as the stack of coherent sheaves of Stacks 08KB (Stacks 08LQ). The converse
direction, from an equivalence to gluing, is
`AlgebraicGeometry.Stack.ThickeningPushout.isGluingSquare_of_full_of_faithful`.

## Main definitions

* `AlgebraicGeometry.Stack.ThickeningPushout.ObjectsGlue`, the gluing of objects;
* `AlgebraicGeometry.Stack.ThickeningPushout.MorphismsGlue`, the gluing of morphisms.

## Main results

* `AlgebraicGeometry.Stack.ThickeningPushout.fiberSquareComparison_isEquivalence_of_glue`: the
  comparison functor is an equivalence when objects and morphisms glue.

## References

* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 08LQ](https://stacks.math.columbia.edu/tag/08LQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.ThickeningPushout

section Criterion

variable {𝒮 : Type*} [Category 𝒮] {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ 𝒮)
variable {X X' Y Y' : 𝒮} (f : X ⟶ Y) (i : X ⟶ X') (b : Y ⟶ Y') (a : X' ⟶ Y')

/-- **Objects glue along the square**: every span `y ← x → z` of `𝒳` lying over `Y ← X → X'`
is completed, by morphisms over `b` and `a` into an object over `Y'`, to a commutative square. -/
def ObjectsGlue : Prop :=
  ∀ (x : p.Fiber X) (y : p.Fiber Y) (z : p.Fiber X') (α : x.1 ⟶ y.1) (β : x.1 ⟶ z.1),
    p.IsHomLift f α → p.IsHomLift i β →
    ∃ (t : p.Fiber Y') (γ : y.1 ⟶ t.1) (δ : z.1 ⟶ t.1),
      p.IsHomLift b γ ∧ p.IsHomLift a δ ∧ α ≫ γ = β ≫ δ

/-- **Morphisms glue along the square**: for `r : y ⟶ t` and `s : z ⟶ t` over `b` and `a`, a
pair of morphisms `y ⟶ t'` and `z ⟶ t'` over `b` and `a` which agree on every common lift of
`X` factors through `r` and `s` by exactly one morphism `t ⟶ t'` of the fibre over `Y'`. -/
def MorphismsGlue : Prop :=
  ∀ {y : p.Fiber Y} {z : p.Fiber X'} {t t' : p.Fiber Y'} (r : y.1 ⟶ t.1) (s : z.1 ⟶ t.1)
    (mY : y.1 ⟶ t'.1) (mZ : z.1 ⟶ t'.1),
    p.IsHomLift b r → p.IsHomLift a s → p.IsHomLift b mY → p.IsHomLift a mZ →
    (∀ (x : p.Fiber X) (uY : x.1 ⟶ y.1) (uZ : x.1 ⟶ z.1), p.IsHomLift f uY →
      p.IsHomLift i uZ → uY ≫ r = uZ ≫ s → uY ≫ mY = uZ ≫ mZ) →
    ∃! m : t ⟶ t', r ≫ m.1 = mY ∧ s ≫ m.1 = mZ

variable [p.IsFibered]

variable {p f i b a}

/-- **The gluing criterion.** If `p` is fibred in groupoids and objects and morphisms glue along
the square `f ≫ b = i ≫ a`, then the comparison functor `𝒳_{Y'} ⥤ 𝒳_Y ×_{𝒳_X} 𝒳_{X'}` is an
equivalence. -/
theorem fiberSquareComparison_isEquivalence_of_glue (hp : p.IsFiberedInGroupoids)
    (w : f ≫ b = i ≫ a) (hobj : ObjectsGlue p f i b a) (hmor : MorphismsGlue p f i b a) :
    (Deformation.Artin.fiberSquareComparison p p.chosenPullbacks f i b a w).IsEquivalence := by
  let c := p.chosenPullbacks
  let F := Deformation.Artin.fiberSquareComparison p c f i b a w
  -- the structure isomorphism of the comparison at `t`, typed through the chosen pullbacks
  have hι : ∀ t : p.Fiber Y', ∃ ι : (c.obj f (c.obj b t)).1 ⟶ (c.obj i (c.obj a t)).1,
      ι = (F.obj t).iso.hom.1 ∧ p.IsHomLift (𝟙 X) ι ∧
        ι ≫ c.map i (c.obj a t) ≫ c.map a t = c.map f (c.obj b t) ≫ c.map b t :=
    fun t => ⟨(F.obj t).iso.hom.1, rfl, (F.obj t).iso.hom.2,
      fiberSquareComparison_iso_fac p f i b a w t⟩
  have hfac : ∀ {V U : 𝒮} (k : V ⟶ U) {x x' : p.Fiber U} (α : x ⟶ x'),
      (c.homMap k α).1 ≫ c.map k x' = c.map k x ≫ α.1 :=
    fun k _ _ α => c.homMap_fac k α
  have hfaith : F.Faithful := by
    refine ⟨fun {t t'} α β hαβ => ?_⟩
    obtain ⟨h1, h2⟩ : c.homMap b α = c.homMap b β ∧ c.homMap a α = c.homMap a β :=
      CategoricalPullback.hom_ext_iff.1 hαβ
    have e1 : c.map b t ≫ α.1 = c.map b t ≫ β.1 := by rw [← hfac, ← hfac, h1]
    have e2 : c.map a t ≫ α.1 = c.map a t ≫ β.1 := by rw [← hfac, ← hfac, h2]
    have hα : p.IsHomLift (𝟙 Y') α.1 := α.2
    obtain ⟨m, -, hm⟩ := hmor (c.map b t) (c.map a t) (c.map b t ≫ α.1) (c.map a t ≫ α.1)
      inferInstance inferInstance inferInstance inferInstance
      (fun x uY uZ _ _ h => by rw [← Category.assoc, h, Category.assoc])
    exact (hm α ⟨rfl, rfl⟩).trans (hm β ⟨e1.symm, e2.symm⟩).symm
  have hfull : F.Full := by
    refine ⟨fun {t t'} m => ?_⟩
    obtain ⟨ψY, hψY⟩ : ∃ ψY : (c.obj b t).1 ⟶ (c.obj b t').1, ψY = m.fst.1 := ⟨_, rfl⟩
    obtain ⟨ψZ, hψZ⟩ : ∃ ψZ : (c.obj a t).1 ⟶ (c.obj a t').1, ψZ = m.snd.1 := ⟨_, rfl⟩
    obtain ⟨πf, hπf⟩ : ∃ πf : (c.obj f (c.obj b t)).1 ⟶ (c.obj f (c.obj b t')).1,
        πf = ((c.pullbackFunctor f).map m.fst).1 := ⟨_, rfl⟩
    obtain ⟨πi, hπi⟩ : ∃ πi : (c.obj i (c.obj a t)).1 ⟶ (c.obj i (c.obj a t')).1,
        πi = ((c.pullbackFunctor i).map m.snd).1 := ⟨_, rfl⟩
    obtain ⟨ι, hιe, hιl, hιf⟩ := hι t
    obtain ⟨ι', hιe', -, hιf'⟩ := hι t'
    have hψYl : p.IsHomLift (𝟙 Y) ψY := by subst hψY; exact m.fst.2
    have hψZl : p.IsHomLift (𝟙 X') ψZ := by subst hψZ; exact m.snd.2
    have hw : πf ≫ ι' = ι ≫ πi := by
      subst hπf hπi hιe hιe'; exact congrArg (fun q => q.1) m.w
    have hf₁ : πf ≫ c.map f (c.obj b t') = c.map f (c.obj b t) ≫ ψY := by
      subst hπf hψY; exact hfac f m.fst
    have hf₂ : πi ≫ c.map i (c.obj a t') = c.map i (c.obj a t) ≫ ψZ := by
      subst hπi hψZ; exact hfac i m.snd
    have hcomp : ∀ (x : p.Fiber X) (uY : x.1 ⟶ (c.obj b t).1) (uZ : x.1 ⟶ (c.obj a t).1),
        p.IsHomLift f uY → p.IsHomLift i uZ → uY ≫ c.map b t = uZ ≫ c.map a t →
        uY ≫ ψY ≫ c.map b t' = uZ ≫ ψZ ≫ c.map a t' := by
      intro x uY uZ hY hZ h
      let θ : x.1 ⟶ (c.obj f (c.obj b t)).1 :=
        IsStronglyCartesian.map p f (c.map f (c.obj b t)) (Category.id_comp f).symm uY
      have hθ : θ ≫ c.map f (c.obj b t) = uY :=
        IsStronglyCartesian.fac p f (c.map f (c.obj b t)) (Category.id_comp f).symm uY
      have hθl : p.IsHomLift (𝟙 X) θ := inferInstance
      have hZ' : uZ = θ ≫ ι ≫ c.map i (c.obj a t) := by
        refine IsStronglyCartesian.ext p a (c.map a t) i ?_
        rw [← h, ← hθ, Category.assoc, Category.assoc, Category.assoc, hιf]
      calc uY ≫ ψY ≫ c.map b t'
          = θ ≫ (c.map f (c.obj b t) ≫ ψY) ≫ c.map b t' := by
            rw [← hθ, Category.assoc, Category.assoc]
        _ = θ ≫ πf ≫ c.map f (c.obj b t') ≫ c.map b t' := by
            rw [← hf₁, Category.assoc]
        _ = θ ≫ πf ≫ ι' ≫ c.map i (c.obj a t') ≫ c.map a t' := by rw [hιf']
        _ = θ ≫ ι ≫ πi ≫ c.map i (c.obj a t') ≫ c.map a t' := by
            rw [← Category.assoc πf, hw, Category.assoc]
        _ = θ ≫ ι ≫ c.map i (c.obj a t) ≫ ψZ ≫ c.map a t' := by
            rw [← Category.assoc πi, hf₂, Category.assoc]
        _ = uZ ≫ ψZ ≫ c.map a t' := by
            rw [hZ']; simp only [Category.assoc]
    obtain ⟨γ, ⟨hγ₁, hγ₂⟩, -⟩ := hmor (c.map b t) (c.map a t) (ψY ≫ c.map b t')
      (ψZ ≫ c.map a t') inferInstance inferInstance inferInstance inferInstance hcomp
    refine ⟨γ, CategoricalPullback.hom_ext ?_ ?_⟩
    · refine (c.homMap_uniq b γ m.fst ?_).symm
      subst hψY; exact hγ₁.symm
    · refine (c.homMap_uniq a γ m.snd ?_).symm
      subst hψZ; exact hγ₂.symm
  have hess : F.EssSurj := by
    refine ⟨fun e => ?_⟩
    obtain ⟨κ, hκ⟩ : ∃ κ : (c.obj f e.fst).1 ⟶ (c.obj i e.snd).1, κ = e.iso.hom.1 :=
      ⟨_, rfl⟩
    have hκl : p.IsHomLift (𝟙 X) κ := by subst hκ; exact e.iso.hom.2
    obtain ⟨t, γ, δ, hγ, hδ, hαβ⟩ := hobj (c.obj f e.fst) e.fst e.snd (c.map f e.fst)
      (κ ≫ c.map i e.snd) inferInstance inferInstance
    have hcγ : p.IsCartesian b γ :=
      (hp.isStronglyCartesian_homLift b γ).isCartesian_of_isStronglyCartesian
    have hcδ : p.IsCartesian a δ :=
      (hp.isStronglyCartesian_homLift a δ).isCartesian_of_isStronglyCartesian
    let E₁ : c.obj b t ≅ e.fst := fiberIsoOfCartesian b (c.map b t) γ inferInstance hcγ
    let E₂ : c.obj a t ≅ e.snd := fiberIsoOfCartesian a (c.map a t) δ inferInstance hcδ
    obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : (c.obj b t).1 ⟶ e.fst.1, ε₁ = E₁.hom.1 := ⟨_, rfl⟩
    obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : (c.obj a t).1 ⟶ e.snd.1, ε₂ = E₂.hom.1 := ⟨_, rfl⟩
    have hE₁ : ε₁ ≫ γ = c.map b t := by
      subst hε₁; exact fiberIsoOfCartesian_hom_fac b (c.map b t) γ inferInstance hcγ
    have hE₂ : ε₂ ≫ δ = c.map a t := by
      subst hε₂; exact fiberIsoOfCartesian_hom_fac a (c.map a t) δ inferInstance hcδ
    obtain ⟨πf, hπf⟩ : ∃ πf : (c.obj f (c.obj b t)).1 ⟶ (c.obj f e.fst).1,
        πf = ((c.pullbackFunctor f).map E₁.hom).1 := ⟨_, rfl⟩
    obtain ⟨πi, hπi⟩ : ∃ πi : (c.obj i (c.obj a t)).1 ⟶ (c.obj i e.snd).1,
        πi = ((c.pullbackFunctor i).map E₂.hom).1 := ⟨_, rfl⟩
    have hf₁ : πf ≫ c.map f e.fst = c.map f (c.obj b t) ≫ ε₁ := by
      subst hπf hε₁; exact hfac f E₁.hom
    have hf₂ : πi ≫ c.map i e.snd = c.map i (c.obj a t) ≫ ε₂ := by
      subst hπi hε₂; exact hfac i E₂.hom
    obtain ⟨ι, hιe, hιl, hιf⟩ := hι t
    refine ⟨t, ⟨CategoricalPullback.mkIso E₁ E₂ ?_⟩⟩
    have hδl : p.IsHomLift a δ := hδ
    have hcomp : p.IsStronglyCartesian (i ≫ a) (c.map i e.snd ≫ δ) :=
      hp.isStronglyCartesian_homLift _ _
    have hl₁ : p.IsHomLift (𝟙 X) (πf ≫ κ) := by
      have : p.IsHomLift (𝟙 X) πf := by subst hπf; exact ((c.pullbackFunctor f).map E₁.hom).2
      infer_instance
    have hl₂ : p.IsHomLift (𝟙 X) (ι ≫ πi) := by
      have : p.IsHomLift (𝟙 X) πi := by subst hπi; exact ((c.pullbackFunctor i).map E₂.hom).2
      infer_instance
    have key : πf ≫ κ = ι ≫ πi := by
      refine IsStronglyCartesian.ext p (i ≫ a) (c.map i e.snd ≫ δ) (𝟙 X) ?_
      calc (πf ≫ κ) ≫ c.map i e.snd ≫ δ
          = πf ≫ c.map f e.fst ≫ γ := by
            rw [Category.assoc, ← Category.assoc κ, ← hαβ]
        _ = c.map f (c.obj b t) ≫ c.map b t := by
            rw [← Category.assoc, hf₁, Category.assoc, hE₁]
        _ = ι ≫ c.map i (c.obj a t) ≫ c.map a t := hιf.symm
        _ = (ι ≫ πi) ≫ c.map i e.snd ≫ δ := by
            rw [Category.assoc, ← Category.assoc πi, hf₂, Category.assoc, hE₂]
    subst hπf hπi hιe hκ
    exact Fiber.hom_ext key
  exact { faithful := hfaith, full := hfull, essSurj := hess }

end Criterion

end AlgebraicGeometry.Stack.ThickeningPushout

end
