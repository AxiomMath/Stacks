module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismHom

/-!
# Fppf descent of the pairs of Stacks 05Y1

Let `S` be a scheme contained in a big fppf site `B` and let `z : Z ⟶ Q` and `x : X ⟶ Q` be
morphisms of algebraic spaces over `S`. Given an fppf covering `{U i ⟶ T}` of algebraic spaces
over `S` and a family of pairs `(a_i, b_i)` of Stacks 05Y1 over the `U i` which agree on the
fibre products `U i ×_T U j`, there is exactly one pair `(a, b)` over `T` restricting to the
given ones. This is the first paragraph of the proof of **Stacks 05Y3** and the engine of both
of its parts.

## Main results

* `AlgebraicGeometry.Space.existsUnique_restrict_of_isFppfCovering`: effective descent and
  uniqueness for the pairs of Stacks 05Y1 along an fppf covering.
* `AlgebraicGeometry.Space.RelativeMorphism.eval_eq_of_restrict_eq`: two pairs whose
  restrictions to the fibre product of their test objects agree have the same evaluation at any
  compatible pair of points.

## Implementation notes

Both halves reduce to fpqc descent for morphisms of algebraic spaces (**Stacks 04P2**,
`AlgebraicGeometry.Space.existsUnique_desc_of_fpqcCovering`), an fppf covering being an fpqc
covering by **Stacks 0DFQ**. The first components descend by one application of it. For the
second components, the base change `T ×_{a, Q} Z` of the descended first component is covered by
the fibre products `(T ×_{a, Q} Z) ×_T U i` (**Stacks 03Y9**), each of which carries the morphism
to `T ×_{a, Q} X` read off from `(a_i, b_i)`; a second application of 04P2 descends those, and a
third, with target `T`, identifies the resulting morphism's first component, which is what makes
it a morphism over `T` and hence the second component of a pair.

The pairs are compared through `AlgebraicGeometry.Space.RelativeMorphism.eval` and
`AlgebraicGeometry.Space.RelativeMorphism.ext_of_eval` throughout, so that no morphism out of a
base change has to be transported along an equality of first components.

## References

* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}

/-- A pair evaluated at the two projections of its own base change is its second component. -/
theorem RelativeMorphism.eval_self {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RelativeMorphism B S hS Z X Q z x T) :
    p.eval (pullback.fst p.base z) (pullback.snd p.base z) pullback.condition = p.morphism := by
  have hid : pullback.lift (pullback.fst p.base z) (pullback.snd p.base z)
      (pullback.condition : pullback.fst p.base z ≫ p.base = pullback.snd p.base z ≫ z) =
      𝟙 (pullback p.base z) :=
    pullback.hom_ext (by simp) (by simp)
  rw [RelativeMorphism.eval, hid, Category.id_comp]

/-- Two pairs over `U i` and `U j` whose restrictions to `U i ×_T U j` agree have the same
evaluation at any pair of points of `U i` and of `U j` lying over a common point of `T` and a
common point of `Z`. -/
theorem RelativeMorphism.eval_eq_of_restrict_eq {Ui Uj Tt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (fi : Ui ⟶ Tt) (fj : Uj ⟶ Tt) (pi : RelativeMorphism B S hS Z X Q z x Ui)
    (pj : RelativeMorphism B S hS Z X Q z x Uj)
    (hpij : RelativeMorphism.restrict (pullback.fst fi fj) pi =
      RelativeMorphism.restrict (pullback.snd fi fj) pj)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (γi : P ⟶ Ui) (γj : P ⟶ Uj)
    (hγ : γi ≫ fi = γj ≫ fj) (s : P ⟶ Z) (hi : γi ≫ pi.base = s ≫ z)
    (hj : γj ≫ pj.base = s ≫ z) :
    pi.eval γi s hi = pj.eval γj s hj := by
  have hρ₁ : pullback.lift γi γj hγ ≫ pullback.fst fi fj = γi := pullback.lift_fst _ _ _
  have hρ₂ : pullback.lift γi γj hγ ≫ pullback.snd fi fj = γj := pullback.lift_snd _ _ _
  have hRi : (pullback.lift γi γj hγ ≫ pullback.fst fi fj) ≫ pi.base = s ≫ z := by
    rwa [hρ₁]
  have hRj : (pullback.lift γi γj hγ ≫ pullback.snd fi fj) ≫ pj.base = s ≫ z := by
    rwa [hρ₂]
  have hLi : pullback.lift γi γj hγ ≫
      (RelativeMorphism.restrict (pullback.fst fi fj) pi).base = s ≫ z := by
    rwa [RelativeMorphism.restrict_base, ← Category.assoc]
  have hLj : pullback.lift γi γj hγ ≫
      (RelativeMorphism.restrict (pullback.snd fi fj) pj).base = s ≫ z := by
    rwa [RelativeMorphism.restrict_base, ← Category.assoc]
  calc pi.eval γi s hi
      = pi.eval (pullback.lift γi γj hγ ≫ pullback.fst fi fj) s hRi :=
        RelativeMorphism.eval_congr _ hρ₁.symm rfl hi hRi
    _ = (RelativeMorphism.restrict (pullback.fst fi fj) pi).eval
          (pullback.lift γi γj hγ) s hLi :=
        (RelativeMorphism.eval_restrict _ _ _ _ hLi hRi).symm
    _ = (RelativeMorphism.restrict (pullback.snd fi fj) pj).eval
          (pullback.lift γi γj hγ) s hLj :=
        RelativeMorphism.eval_eq_of_eq hpij _ _ hLi hLj
    _ = pj.eval (pullback.lift γi γj hγ ≫ pullback.snd fi fj) s hRj :=
        RelativeMorphism.eval_restrict _ _ _ _ hLj hRj
    _ = pj.eval γj s hj := RelativeMorphism.eval_congr _ hρ₂ rfl hRj hj

/-- **Fppf descent for the pairs of Stacks 05Y1**, the first paragraph of the proof of
Stacks 05Y3. A family of pairs over the members of an fppf covering `{U i ⟶ T}` of algebraic
spaces over `S` which agree on the fibre products `U i ×_T U j` comes from exactly one pair
over `T`. -/
theorem existsUnique_restrict_of_isFppfCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)
    {I : Type v} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, U i ⟶ T)
    (hf : IsFppfCovering B S hS U f)
    (p : ∀ i, RelativeMorphism B S hS Z X Q z x (U i))
    (hp : ∀ i j, RelativeMorphism.restrict (pullback.fst (f i) (f j)) (p i) =
      RelativeMorphism.restrict (pullback.snd (f i) (f j)) (p j)) :
    ∃! q : RelativeMorphism B S hS Z X Q z x T,
      ∀ i, RelativeMorphism.restrict (f i) q = p i := by
  classical
  let Ta : AlgebraicSpaces B S hS := ⟨T, hf.target_isAlgebraicSpace⟩
  let Ua : I → AlgebraicSpaces B S hS := fun i => ⟨U i, hf.source_isAlgebraicSpace i⟩
  let Qa : AlgebraicSpaces B S hS := ⟨Q, hQ⟩
  let fa : ∀ i, Ua i ⟶ Ta := fun i => ObjectProperty.homMk (f i)
  have hfpqc : IsFpqcCovering B S hS (fun i => (fa i).hom) :=
    isFpqcCovering_of_isFppfCovering B S hS U f hf
  -- Step 1: the first components descend.
  obtain ⟨qA, hqA, hqAuniq⟩ :=
    existsUnique_desc_of_fpqcCovering B S hS fa hfpqc Qa
      (fun i => ObjectProperty.homMk (p i).base)
      (fun i j => ObjectProperty.hom_ext _ (congrArg RelativeMorphism.base (hp i j)))
  let a : T ⟶ Q := qA.hom
  have hbase : ∀ i, f i ≫ a = (p i).base := fun i =>
    congrArg (fun m : Ua i ⟶ Qa => m.hom) (hqA i)
  -- The two base changes along the descended first component.
  let Pb : AlgebraicSpaces B S hS :=
    ⟨pullback a z, isAlgebraicSpace_pullback B S hS a z hf.target_isAlgebraicSpace hZ hQ⟩
  let Wb : AlgebraicSpaces B S hS :=
    ⟨pullback a x, isAlgebraicSpace_pullback B S hS a x hf.target_isAlgebraicSpace hX hQ⟩
  let gA : Pb ⟶ Ta := ObjectProperty.homMk (pullback.fst a z)
  let Vi : I → AlgebraicSpaces B S hS := fun i => AlgebraicSpaces.fiberProduct B S hS gA (fa i)
  let cA : ∀ i, Vi i ⟶ Pb := fun i => ObjectProperty.homMk (pullback.fst gA.hom (fa i).hom)
  let eA : ∀ i, Vi i ⟶ Ua i := fun i => ObjectProperty.homMk (pullback.snd gA.hom (fa i).hom)
  have hcov : IsFppfCovering B S hS (fun i => (Vi i).1) (fun i => (cA i).hom) :=
    isFppfCovering_fibreProduct B S hS Ua fa gA hf
  have hfpqcV : IsFpqcCovering B S hS (fun i => (cA i).hom) :=
    isFpqcCovering_of_isFppfCovering B S hS _ _ hcov
  have hVcond : ∀ i, (cA i).hom ≫ pullback.fst a z = (eA i).hom ≫ f i := fun i =>
    pullback.condition
  have hazx : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : Y ⟶ pullback a z),
      (m ≫ pullback.fst a z) ≫ a = (m ≫ pullback.snd a z) ≫ z := fun m => by
    rw [Category.assoc, Category.assoc, pullback.condition]
  -- The morphism from each member of the covering of the base change to `T ×_{a, Q} X`.
  have hw : ∀ i, (eA i).hom ≫ (p i).base = ((cA i).hom ≫ pullback.snd a z) ≫ z := by
    intro i
    rw [← hbase i, ← Category.assoc, ← hVcond i]
    exact hazx (cA i).hom
  have hwc : ∀ i {Y} (m : Y ⟶ (Vi i).1), (m ≫ (eA i).hom) ≫ (p i).base =
      (m ≫ ((cA i).hom ≫ pullback.snd a z)) ≫ z := fun i _ m => by
    rw [Category.assoc, hw i, Category.assoc, Category.assoc, Category.assoc]
  let kHom : ∀ i, (Vi i).1 ⟶ pullback a x := fun i =>
    pullback.lift ((cA i).hom ≫ pullback.fst a z)
      ((p i).eval (eA i).hom ((cA i).hom ≫ pullback.snd a z) (hw i))
      (by rw [RelativeMorphism.eval_comp]; exact hazx (cA i).hom)
  have hkfst : ∀ i, kHom i ≫ pullback.fst a x = (cA i).hom ≫ pullback.fst a z :=
    fun i => pullback.lift_fst _ _ _
  have hksnd : ∀ i, kHom i ≫ pullback.snd a x =
      (p i).eval (eA i).hom ((cA i).hom ≫ pullback.snd a z) (hw i) :=
    fun i => pullback.lift_snd _ _ _
  let kA : ∀ i, Vi i ⟶ Wb := fun i => ObjectProperty.homMk (kHom i)
  -- Step 2: those morphisms agree on the overlaps.
  have hkCompat : ∀ i j,
      (ObjectProperty.homMk (pullback.fst (cA i).hom (cA j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (cA i) (cA j) ⟶ Vi i) ≫ kA i =
      (ObjectProperty.homMk (pullback.snd (cA i).hom (cA j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (cA i) (cA j) ⟶ Vi j) ≫ kA j := by
    intro i j
    refine ObjectProperty.hom_ext _ ?_
    change pullback.fst (cA i).hom (cA j).hom ≫ kHom i =
      pullback.snd (cA i).hom (cA j).hom ≫ kHom j
    have hπ : pullback.fst (cA i).hom (cA j).hom ≫ (cA i).hom =
        pullback.snd (cA i).hom (cA j).hom ≫ (cA j).hom := pullback.condition
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hkfst, hkfst, ← Category.assoc, ← Category.assoc, hπ]
    · rw [Category.assoc, Category.assoc, hksnd, hksnd]
      set π₁ := pullback.fst (cA i).hom (cA j).hom with hπ₁
      set π₂ := pullback.snd (cA i).hom (cA j).hom with hπ₂
      have hρw : (π₁ ≫ (eA i).hom) ≫ f i = (π₂ ≫ (eA j).hom) ≫ f j := by
        rw [Category.assoc, Category.assoc, ← hVcond i, ← hVcond j, ← Category.assoc,
          ← Category.assoc, hπ]
      have hsP : π₁ ≫ ((cA i).hom ≫ pullback.snd a z) =
          π₂ ≫ ((cA j).hom ≫ pullback.snd a z) := by
        rw [← Category.assoc, hπ, Category.assoc]
      have hPi := hwc i π₁
      have hPj' := hwc j π₂
      have hPj : (π₂ ≫ (eA j).hom) ≫ (p j).base =
          (π₁ ≫ ((cA i).hom ≫ pullback.snd a z)) ≫ z := by rw [hPj', hsP]
      calc π₁ ≫ (p i).eval (eA i).hom ((cA i).hom ≫ pullback.snd a z) (hw i)
          = (p i).eval (π₁ ≫ (eA i).hom) (π₁ ≫ ((cA i).hom ≫ pullback.snd a z)) hPi :=
            RelativeMorphism.comp_eval (p i) π₁ (eA i).hom _ (hw i) hPi
        _ = (p j).eval (π₂ ≫ (eA j).hom) (π₁ ≫ ((cA i).hom ≫ pullback.snd a z)) hPj :=
            RelativeMorphism.eval_eq_of_restrict_eq (f i) (f j) (p i) (p j) (hp i j)
              (π₁ ≫ (eA i).hom) (π₂ ≫ (eA j).hom) hρw _ hPi hPj
        _ = (p j).eval (π₂ ≫ (eA j).hom) (π₂ ≫ ((cA j).hom ≫ pullback.snd a z)) hPj' :=
            RelativeMorphism.eval_congr (p j) rfl hsP hPj hPj'
        _ = π₂ ≫ (p j).eval (eA j).hom ((cA j).hom ≫ pullback.snd a z) (hw j) :=
            (RelativeMorphism.comp_eval (p j) π₂ (eA j).hom _ (hw j) hPj').symm
  -- Step 3: the second components descend.
  obtain ⟨kObj, hk, hkuniq⟩ :=
    existsUnique_desc_of_fpqcCovering B S hS cA hfpqcV Wb kA hkCompat
  let k : pullback a z ⟶ pullback a x := kObj.hom
  have hki : ∀ i, (cA i).hom ≫ k = kHom i := fun i =>
    congrArg (fun m : Vi i ⟶ Wb => m.hom) (hk i)
  -- Step 4: the descended morphism lies over `T`.
  obtain ⟨dObj, hd, hduniq⟩ :=
    existsUnique_desc_of_fpqcCovering B S hS cA hfpqcV Ta (fun i => cA i ≫ gA)
      (fun i j => ObjectProperty.hom_ext _ (by
        change pullback.fst (cA i).hom (cA j).hom ≫ ((cA i).hom ≫ pullback.fst a z) =
          pullback.snd (cA i).hom (cA j).hom ≫ ((cA j).hom ≫ pullback.fst a z)
        rw [← Category.assoc, ← Category.assoc, pullback.condition]))
  have hkfstP : k ≫ pullback.fst a x = pullback.fst a z := by
    have h1 : ∀ i, cA i ≫ (kObj ≫ (ObjectProperty.homMk (pullback.fst a x) : Wb ⟶ Ta)) =
        cA i ≫ gA := by
      intro i
      refine ObjectProperty.hom_ext _ ?_
      change (cA i).hom ≫ (k ≫ pullback.fst a x) = (cA i).hom ≫ pullback.fst a z
      rw [← Category.assoc, hki i, hkfst i]
    exact congrArg (fun m : Pb ⟶ Ta => m.hom)
      ((hduniq _ h1).trans (hduniq _ fun _ => rfl).symm)
  -- Step 5: the descended pair, and its two defining properties.
  have hqcomm : (k ≫ pullback.snd a x) ≫ x = pullback.snd a z ≫ z := by
    rw [Category.assoc, ← pullback.condition (f := a) (g := x), ← Category.assoc, hkfstP,
      pullback.condition]
  let q : RelativeMorphism B S hS Z X Q z x T := ⟨a, k ≫ pullback.snd a x, hqcomm⟩
  refine ⟨q, ?_, ?_⟩
  · intro i
    refine RelativeMorphism.ext_of_eval (hbase i) ?_
    intro V γ s hγ hγ'
    have h₂ : (γ ≫ f i) ≫ q.base = s ≫ z := by
      rwa [RelativeMorphism.restrict_base, ← Category.assoc] at hγ
    have hLfst : pullback.lift (γ ≫ f i) s h₂ ≫ gA.hom = γ ≫ (fa i).hom :=
      pullback.lift_fst _ _ _
    have hLsnd : pullback.lift (γ ≫ f i) s h₂ ≫ pullback.snd a z = s :=
      pullback.lift_snd _ _ _
    let θ : yoneda.obj V ⟶ (Vi i).obj :=
      pullback.lift (pullback.lift (γ ≫ f i) s h₂) γ hLfst
    have hθc : θ ≫ (cA i).hom = pullback.lift (γ ≫ f i) s h₂ := pullback.lift_fst _ _ _
    have hθe : θ ≫ (eA i).hom = γ := pullback.lift_snd _ _ _
    have hθs : θ ≫ ((cA i).hom ≫ pullback.snd a z) = s := by
      rw [← Category.assoc, hθc, hLsnd]
    have hθP := hwc i θ
    calc (RelativeMorphism.restrict (f i) q).eval γ s hγ
        = q.eval (γ ≫ f i) s h₂ := RelativeMorphism.eval_restrict q (f i) γ s hγ h₂
      _ = pullback.lift (γ ≫ f i) s h₂ ≫ (k ≫ pullback.snd a x) := rfl
      _ = (θ ≫ (cA i).hom) ≫ (k ≫ pullback.snd a x) := by rw [hθc]
      _ = θ ≫ (((cA i).hom ≫ k) ≫ pullback.snd a x) := by
          simp only [Category.assoc]
      _ = θ ≫ (kHom i ≫ pullback.snd a x) := by rw [hki i]
      _ = θ ≫ (p i).eval (eA i).hom ((cA i).hom ≫ pullback.snd a z) (hw i) := by rw [hksnd i]
      _ = (p i).eval (θ ≫ (eA i).hom) (θ ≫ ((cA i).hom ≫ pullback.snd a z)) hθP :=
          RelativeMorphism.comp_eval (p i) θ (eA i).hom _ (hw i) hθP
      _ = (p i).eval γ s hγ' := RelativeMorphism.eval_congr (p i) hθe hθs hθP hγ'
  · intro r hr
    obtain ⟨rb, rm, rc⟩ := r
    have hrb : rb = a := by
      have h1 : ∀ i, fa i ≫ (ObjectProperty.homMk rb : Ta ⟶ Qa) =
          ObjectProperty.homMk (p i).base := fun i =>
        ObjectProperty.hom_ext _ (congrArg RelativeMorphism.base (hr i))
      exact congrArg (fun m : Ta ⟶ Qa => m.hom) (hqAuniq _ h1)
    subst hrb
    let r' : RelativeMorphism B S hS Z X Q z x T := ⟨a, rm, rc⟩
    have hlcond : pullback.fst a z ≫ a = rm ≫ x := pullback.condition.trans rc.symm
    have hlfst : pullback.lift (pullback.fst a z) rm hlcond ≫ pullback.fst a x =
        pullback.fst a z := pullback.lift_fst _ _ _
    have hlsnd : pullback.lift (pullback.fst a z) rm hlcond ≫ pullback.snd a x = rm :=
      pullback.lift_snd _ _ _
    have hlA : ∀ i, cA i ≫ (ObjectProperty.homMk
        (pullback.lift (pullback.fst a z) rm hlcond) : Pb ⟶ Wb) = kA i := by
      intro i
      refine ObjectProperty.hom_ext _ ?_
      change (cA i).hom ≫ pullback.lift (pullback.fst a z) rm hlcond = kHom i
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hlfst, hkfst i]
      · rw [Category.assoc, hlsnd, hksnd i]
        have hci : ((cA i).hom ≫ pullback.fst a z) ≫ r'.base =
            ((cA i).hom ≫ pullback.snd a z) ≫ z := hazx (cA i).hom
        have hci' : ((eA i).hom ≫ f i) ≫ r'.base =
            ((cA i).hom ≫ pullback.snd a z) ≫ z := by rwa [← hVcond i]
        have hL : (eA i).hom ≫ (RelativeMorphism.restrict (f i) r').base =
            ((cA i).hom ≫ pullback.snd a z) ≫ z := by
          rwa [RelativeMorphism.restrict_base, ← Category.assoc]
        calc (cA i).hom ≫ rm
            = (cA i).hom ≫ r'.eval (pullback.fst r'.base z) (pullback.snd r'.base z)
                pullback.condition := by rw [RelativeMorphism.eval_self]
          _ = r'.eval ((cA i).hom ≫ pullback.fst a z) ((cA i).hom ≫ pullback.snd a z) hci :=
              RelativeMorphism.comp_eval r' (cA i).hom (pullback.fst a z) (pullback.snd a z)
                pullback.condition hci
          _ = r'.eval ((eA i).hom ≫ f i) ((cA i).hom ≫ pullback.snd a z) hci' :=
              RelativeMorphism.eval_congr r' (hVcond i) rfl hci hci'
          _ = (RelativeMorphism.restrict (f i) r').eval (eA i).hom
                ((cA i).hom ≫ pullback.snd a z) hL :=
              (RelativeMorphism.eval_restrict r' (f i) (eA i).hom _ hL hci').symm
          _ = (p i).eval (eA i).hom ((cA i).hom ≫ pullback.snd a z) (hw i) :=
              RelativeMorphism.eval_eq_of_eq (hr i) _ _ hL (hw i)
    have hlk : pullback.lift (pullback.fst a z) rm hlcond = k :=
      congrArg (fun m : Pb ⟶ Wb => m.hom) (hkuniq _ hlA)
    have hrm : rm = k ≫ pullback.snd a x := by rw [← hlsnd, hlk]
    subst hrm
    rfl

end AlgebraicGeometry.Space

end
