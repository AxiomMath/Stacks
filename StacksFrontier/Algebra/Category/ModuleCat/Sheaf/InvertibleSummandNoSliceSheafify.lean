module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify

/-!
# Tag 0B8N (b) without any sheafification hypothesis on the slice sites

`Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree` proves Tag 0B8N (b) under two
hypotheses, `HasWeakSheafify J AddCommGrpCat.{w}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{w}`, and in particular under none on the slice sites:
the local-bijectivity hypothesis `∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}`
is not needed, and neither is the `J`-level use of the second one in the splitting step.

What the slice hypothesis was for is a single implication. The pairing `ψ : L ⊗ N ⟶ 𝒪` coming
out of invertibility is *universal*: every morphism of presheaves of modules out of `L ⊗ N`
into a sheaf of modules factors uniquely through it. That is literally membership in Mathlib's
Bousfield class `CategoryTheory.GrothendieckTopology.W`, which is defined with no reference to
sheafification as `ObjectProperty.isLocal (Presheaf.IsSheaf J)`. The splitting step needs the
same factorisation property for the *restricted* pairing on a slice site, and what transfers to
a slice site unconditionally is not membership in `W` but local bijectivity
(`Presheaf.isLocallySurjective_whisker` and its injective counterpart, since `Over.forget V` is
cocontinuous). Getting back from local bijectivity to a factorisation is the forward direction
of `GrothendieckTopology.WEqualsLocallyBijective`, which Mathlib proves only from the existence
of sheafification — hence the hypothesis, at every slice.

`Stacks.Sites.W_of_isLocallyBijective` below proves that direction outright, with no
sheafification: a locally bijective morphism of presheaves of abelian groups is `J.W`. The
proof is the amalgamation argument. For injectivity, two morphisms into a sheaf that agree
after `f` agree locally on the image sieve of each section, hence agree. For surjectivity,
`ψ : X ⟶ N` is extended by gluing: over a section `s` of `Y` the family `ψ (local preimage of
s)` on the image sieve of `s` is compatible — two local preimages of the same section agree
locally by local *injectivity*, so `ψ` of them agree — and the amalgamation is additive and
natural because each identity holds locally on a covering sieve and `N` is separated. No object
of a category of sheaves is constructed anywhere, which is why no size hypothesis appears.

## Main results

* `Stacks.Sites.W_of_isLocallyBijective`: a locally bijective morphism of presheaves of abelian
  groups is in `J.W`, with no sheafification instance.
* `Stacks.Sites.homEquivOfIsLocallyBijective`: consequently
  `PresheafOfModules.homEquivOfIsLocallyBijective` holds with no sheafification instance.
* `Stacks.SheafOfModules.isSplitMono_of_dualBasis'`: the algebraic core of Tag 0B8N (b) with
  `[J.WEqualsLocallyBijective AddCommGrpCat.{w}]` removed.
* `Stacks.SheafOfModules.exists_isSplitMono_over'`: the slice step with
  `[(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]` removed.
* `Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree`: **Tag 0B8N (b)**, carrying
  the tag. Its two hypotheses are consumed at exactly one place,
  `Stacks.SheafOfModules.isLocallyInjective_of_universal`, i.e. for the implication
  `W ⟹ locally injective`, the direction this file does *not* prove.

## Implementation notes

The three primed statements are the unprimed ones with a hypothesis deleted; their proofs are
the same, with `PresheafOfModules.homEquivOfIsLocallyBijective` replaced by
`Stacks.Sites.homEquivOfIsLocallyBijective`. They are stated here rather than by editing the
originals so that no consumer of the originals can break.

**Dedup note.** The same implication for presheaves of *types* is already in this tree, as the
`private lemma Stacks.Sites.ConnectedColimitRestriction.W_of_isLocallyBijective` of
`StacksFrontier/CategoryTheory/Sites/Cocontinuous/AlmostCocontinuousFunctors.lean`, with the same
observation about universes in its docstring. It is private, it is stated for
`Cᵒᵖ ⥤ Type w`, and what the presheaf-of-modules hom bijection needs is the
`AddCommGrpCat.{w}`-valued form, which does not follow from the type-valued one by whiskering
(the bijection is between hom sets of additive presheaves). The two should be unified behind
one statement over a concrete category whenever either is touched again.

`Stacks.Sites.homEquivOfIsLocallyBijective` is Mathlib's
`PresheafOfModules.homEquivOfIsLocallyBijective` with one input replaced, but its semilinearity
proof is rewritten as a chain of `Eq.trans`/`congrArg` steps instead of a `rw` chain. Mathlib's
version needs the `backward.isDefEq.respectTransparency` option switched off for that `rw`
chain to match: the `•` in `PresheafOfModules.map_smul` and the `•` produced by the surrounding
rewriting are definitionally equal but not syntactically equal, so `rw` fails on them under
normal transparency. Stating each intermediate equality explicitly and composing the terms
moves the check to elaboration, which does see through it, and needs no option.

## References

* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

universe v u w

namespace Stacks.Sites

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Bijective

variable {X Y N : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : X ⟶ Y)
  (hN : Presheaf.IsSheaf J N)

include hN in
/-- Two morphisms into a separated presheaf which agree after a locally surjective morphism
agree. -/
theorem injective_comp [Presheaf.IsLocallySurjective J f] :
    Function.Injective (fun g : Y ⟶ N => f ≫ g) := by
  intro g₁ g₂ h
  have h' : f ≫ g₁ = f ≫ g₂ := h
  ext Z s
  refine hN.isSeparated _ _ (Presheaf.imageSieve_mem J f s) _ _ ?_
  rintro W p ⟨t, ht⟩
  have e₁ := NatTrans.naturality_apply g₁ p.op s
  have e₂ := NatTrans.naturality_apply g₂ p.op s
  have hcomp : ∀ g : Y ⟶ N, g.app (op W) (f.app (op W) t) = (f ≫ g).app (op W) t :=
    fun _ => rfl
  have key : g₁.app (op W) (Y.map p.op s) = g₂.app (op W) (Y.map p.op s) := by
    rw [← ht, hcomp g₁, hcomp g₂, h']
  rw [e₁, e₂] at key
  exact key

variable [Presheaf.IsLocallyInjective J f] (ψ : X ⟶ N)

include hN in
/-- Sections of `X` with the same image under a locally injective `f` have the same image under
any morphism into a sheaf. -/
theorem app_congr_of_app_eq {Z : Cᵒᵖ} (a b : ToType (X.obj Z))
    (h : f.app Z a = f.app Z b) : ψ.app Z a = ψ.app Z b := by
  refine hN.isSeparated _ _ (Presheaf.equalizerSieve_mem J f a b h) _ _ ?_
  intro W p hp
  rw [← NatTrans.naturality_apply ψ p.op a, ← NatTrans.naturality_apply ψ p.op b]
  exact congrArg (fun z => ψ.app (op W) z) hp

include hN in
/-- The underlying presheaf of sets of a sheaf of abelian groups is a sheaf. -/
theorem isSheaf_comp_forget : Presieve.IsSheaf J (N ⋙ forget AddCommGrpCat.{w}) :=
  (isSheaf_iff_isSheaf_of_type J _).1
    ((sheafCompose J (forget AddCommGrpCat.{w})).obj ⟨N, hN⟩).2

include hN in
/-- The local values `ψ (local preimage of s)` form a compatible family on the image sieve of
`s`: two local preimages have the same image under `f`, hence under `ψ`. -/
theorem localValues_compatible {U : C} (s : ToType (Y.obj (op U))) :
    Presieve.FamilyOfElements.Compatible
      (P := N ⋙ forget AddCommGrpCat.{w})
      (fun W p hp => ψ.app (op W) (Presheaf.localPreimage f s p hp)) := by
  intro W₁ W₂ T g₁ g₂ p₁ p₂ h₁ h₂ hcomm
  change N.map g₁.op (ψ.app (op W₁) (Presheaf.localPreimage f s p₁ h₁))
      = N.map g₂.op (ψ.app (op W₂) (Presheaf.localPreimage f s p₂ h₂))
  rw [← NatTrans.naturality_apply ψ g₁.op, ← NatTrans.naturality_apply ψ g₂.op]
  refine app_congr_of_app_eq f hN ψ _ _ ?_
  rw [NatTrans.naturality_apply f g₁.op, NatTrans.naturality_apply f g₂.op,
    Presheaf.app_localPreimage f s p₁ h₁, Presheaf.app_localPreimage f s p₂ h₂,
    ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]

include hN in
/-- The glued extension of `ψ` along `f`, characterised by its local values: it is the unique
family of sections of `N` whose restriction along any arrow `p` with `f t = s|ₚ` is `ψ t`. -/
theorem exists_glue [Presheaf.IsLocallySurjective J f] :
    ∃ val : ∀ Z : Cᵒᵖ, ToType (Y.obj Z) → ToType (N.obj Z),
      ∀ (Z : Cᵒᵖ) (s : ToType (Y.obj Z)) (W : C) (p : W ⟶ Z.unop)
        (t : ToType (X.obj (op W))), f.app (op W) t = Y.map p.op s →
          N.map p.op (val Z s) = ψ.app (op W) t := by
  classical
  have hNt := isSheaf_comp_forget (J := J) (N := N) hN
  refine ⟨fun Z s => (hNt (Presheaf.imageSieve f s) (Presheaf.imageSieve_mem J f s)).amalgamate
      _ (localValues_compatible f hN ψ s), ?_⟩
  intro Z s W p t ht
  have hp : (Presheaf.imageSieve f s).arrows p := ⟨t, ht⟩
  refine ((hNt (Presheaf.imageSieve f s) (Presheaf.imageSieve_mem J f s)).valid_glue
    (localValues_compatible f hN ψ s) p hp).trans (app_congr_of_app_eq f hN ψ _ _ ?_)
  rw [Presheaf.app_localPreimage f s p hp, ht]

include hN in
/-- Every morphism into a sheaf extends along a locally bijective morphism. -/
theorem exists_comp_eq [Presheaf.IsLocallySurjective J f] : ∃ g : Y ⟶ N, f ≫ g = ψ := by
  classical
  obtain ⟨val, hval⟩ := exists_glue f hN ψ
  have hadd : ∀ (Z : Cᵒᵖ) (s₁ s₂ : ToType (Y.obj Z)),
      val Z (s₁ + s₂) = val Z s₁ + val Z s₂ := by
    intro Z s₁ s₂
    refine hN.isSeparated _ _ (J.intersection_covering
      (Presheaf.imageSieve_mem J f s₁) (Presheaf.imageSieve_mem J f s₂)) _ _ ?_
    rintro W p ⟨⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩
    have hsum : f.app (op W) (t₁ + t₂) = Y.map p.op (s₁ + s₂) := by
      rw [map_add, ht₁, ht₂, map_add]
    rw [hval Z (s₁ + s₂) W p (t₁ + t₂) hsum, map_add, map_add, hval Z s₁ W p t₁ ht₁,
      hval Z s₂ W p t₂ ht₂]
  let happ : ∀ Z : Cᵒᵖ, Y.obj Z ⟶ N.obj Z := fun Z =>
    ConcreteCategory.ofHom (C := AddCommGrpCat.{w}) (AddMonoidHom.mk' (val Z) (hadd Z))
  refine ⟨{ app := happ, naturality := ?_ }, ?_⟩
  · intro Z Z' g
    ext s
    refine hN.isSeparated _ _ (J.pullback_stable g.unop (Presheaf.imageSieve_mem J f s)) _ _ ?_
    rintro W p ⟨t, ht⟩
    have hLHS : N.map p.op (val Z' (Y.map g s)) = ψ.app (op W) t := by
      refine hval Z' (Y.map g s) W p t ?_
      rw [ht, ← Functor.map_comp_apply, show (p ≫ g.unop).op = g ≫ p.op by simp]
    have hRHS : N.map p.op (N.map g (val Z s)) = ψ.app (op W) t := by
      rw [← Functor.map_comp_apply]
      exact hval Z s W (p ≫ g.unop) t ht
    change N.map p.op (val Z' (Y.map g s)) = N.map p.op (N.map g (val Z s))
    rw [hLHS, hRHS]
  · ext Z t
    have h := hval Z (f.app Z (t : ToType (X.obj Z))) Z.unop (𝟙 Z.unop) t (by simp)
    exact (show val Z (f.app Z t) = ψ.app Z t by simpa using h)

include hN in
/-- Composition with a locally bijective morphism is a bijection on morphisms into a sheaf. -/
theorem bijective_comp [Presheaf.IsLocallySurjective J f] :
    Function.Bijective (fun g : Y ⟶ N => f ≫ g) :=
  ⟨injective_comp f hN, fun ψ => exists_comp_eq f hN ψ⟩

end Bijective

/-- **A locally bijective morphism of presheaves of abelian groups is in `J.W`, with no
sheafification hypothesis.** `J.W` is Mathlib's Bousfield class
`ObjectProperty.isLocal (Presheaf.IsSheaf J)`, so this is the forward direction of
`GrothendieckTopology.WEqualsLocallyBijective` proved outright. -/
theorem W_of_isLocallyBijective {X Y : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : X ⟶ Y)
    [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f] : J.W f :=
  fun _ hN => bijective_comp f hN

/-- `PresheafOfModules.homEquivOfIsLocallyBijective` with no sheafification hypothesis: a
locally bijective morphism of presheaves of modules induces a bijection on morphisms into a
sheaf of modules. The proof is Mathlib's, with `GrothendieckTopology.W_of_isLocallyBijective`
replaced by `Stacks.Sites.W_of_isLocallyBijective`. -/
noncomputable def homEquivOfIsLocallyBijective {R : Cᵒᵖ ⥤ RingCat.{w}}
    {M₁ M₂ N : PresheafOfModules.{w} R} (f : M₁ ⟶ M₂)
    (hN : Presheaf.IsSheaf J N.presheaf)
    [PresheafOfModules.IsLocallySurjective J f] [PresheafOfModules.IsLocallyInjective J f] :
    (M₂ ⟶ N) ≃ (M₁ ⟶ N) where
  toFun φ := f ≫ φ
  invFun ψ := PresheafOfModules.homMk (((W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).symm
      ((PresheafOfModules.toPresheaf R).map ψ)) (by
        obtain ⟨φ, hφ⟩ := ((W_of_isLocallyBijective
          ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).surjective
          ((PresheafOfModules.toPresheaf R).map ψ)
        simp only [← hφ, Equiv.symm_apply_apply]
        replace hφ : ∀ (Z : Cᵒᵖ) (x : M₁.obj Z), φ.app Z (f.app Z x) = ψ.app Z x :=
          fun Z x ↦ CategoryTheory.congr_fun (congr_app hφ Z) x
        intro Z r y
        apply hN.isSeparated _ _
          (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf R).map f) y)
        rintro W p ⟨x : M₁.obj _, hx : f.app _ x = M₂.map p.op y⟩
        have hφ' : ∀ z : M₂.obj Z, φ.app _ (M₂.map p.op z) =
            N.map p.op (φ.app _ z) := CategoryTheory.congr_fun (φ.naturality p.op)
        have hfsmul : ∀ (c : R.obj (op W)) (z : M₁.obj (op W)),
            f.app (op W) (c • z) = c • f.app (op W) z :=
          fun c z => (f.app (op W)).hom.map_smul c z
        have hψsmul : ∀ (c : R.obj (op W)) (z : M₁.obj (op W)),
            ψ.app (op W) (c • z) = c • ψ.app (op W) z :=
          fun c z => (ψ.app (op W)).hom.map_smul c z
        change N.map p.op (φ.app Z (r • y)) = N.map p.op (r • φ.app Z y)
        have hL : N.map p.op (φ.app Z (r • y)) = φ.app (op W) (M₂.map p.op (r • y)) :=
          (hφ' (r • y)).symm
        have hR : N.map p.op (r • φ.app Z y)
            = (R.map p.op r) • φ.app (op W) (M₂.map p.op y) :=
          (N.map_smul p.op r (φ.app Z y)).trans
            (congrArg (fun z => (R.map p.op r) • z) (hφ' y).symm)
        have e1 : M₂.map p.op (r • y) = (R.map p.op r) • M₂.map p.op y := M₂.map_smul p.op r y
        have e2 : (R.map p.op r) • M₂.map p.op y = f.app (op W) ((R.map p.op r) • x) :=
          (congrArg (fun z => (R.map p.op r) • z) hx.symm).trans (hfsmul _ _).symm
        refine hL.trans (Eq.trans ?_ hR.symm)
        refine (congrArg (fun z => φ.app (op W) z) (e1.trans e2)).trans ?_
        refine (hφ (op W) ((R.map p.op r) • x)).trans ?_
        refine (hψsmul (R.map p.op r) x).trans ?_
        refine congrArg (fun z => (R.map p.op r) • z) ?_
        exact ((hφ (op W) x).symm).trans (congrArg (fun z => φ.app (op W) z) hx))
  left_inv φ := (PresheafOfModules.toPresheaf _).map_injective
    (((W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).left_inv
      ((PresheafOfModules.toPresheaf R).map φ))
  right_inv ψ := (PresheafOfModules.toPresheaf _).map_injective
    (((W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).right_inv
      ((PresheafOfModules.toPresheaf R).map ψ))

end Stacks.Sites

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)}

/-- **Stacks Project, Tag 0B8N (b), algebraic core, with no sheafification hypothesis.** This
is `Stacks.SheafOfModules.isSplitMono_of_dualBasis` with
`[J.WEqualsLocallyBijective AddCommGrpCat.{w}]` deleted: the retraction comes from
`Stacks.Sites.homEquivOfIsLocallyBijective`. -/
theorem isSplitMono_of_dualBasis'
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (hLp : Presheaf.IsSheaf J Lp.presheaf)
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallySurjective J ψ] [PresheafOfModules.IsLocallyInjective J ψ]
    {n : ℕ} (x : Fin n → Lp.sections) (y : Fin n → Np.sections)
    (c : ∀ W : Cᵒᵖ, Fin n → O.obj W)
    (hc : ∀ (W : Cᵒᵖ) (j : Fin n), ψ.app W ((x j).eval W ⊗ₜ (y j).eval W) = c W j)
    (hsum : ∀ W : Cᵒᵖ, ∑ j, c W j = 1) :
    ∃ s : (⟨Lp, hLp⟩ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      O hO)) ⟶
        ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
      IsSplitMono s := by
  classical
  set L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
    ⟨Lp, hLp⟩ with hL
  set E := Stacks.Sites.homEquivOfIsLocallyBijective ψ hLp with hE
  let α : Fin n → (L ⟶ SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :=
    fun j ↦ ⟨coev Lp Np (y j) ≫ ψ⟩
  let ρ : Fin n → (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
    hO) ⟶ L) :=
    fun j ↦ ⟨E.symm (proj Lp Np ψ (x j))⟩
  have hρ : ∀ j, ψ ≫ (ρ j).val = proj Lp Np ψ (x j) := fun j ↦ E.apply_symm_apply _
  have key : ∑ j, α j ≫ ρ j = 𝟙 L := by
    refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun W ↦
      ModuleCat.hom_ext (LinearMap.ext fun v ↦ ?_))
    have hj : ∀ j : Fin n, (α j ≫ ρ j).val.app W v = c W j • v := fun j ↦ by
      have e1 : (α j ≫ ρ j).val = coev Lp Np (y j) ≫ proj Lp Np ψ (x j) := by
        change (coev Lp Np (y j) ≫ ψ) ≫ (ρ j).val = _
        rw [Category.assoc, hρ]
      rw [e1]
      exact coev_proj_app Lp Np ψ (x j) (y j) W v (c W j) (hc W j)
    rw [app_sum Finset.univ (fun j ↦ α j ≫ ρ j) W v,
      Finset.sum_congr rfl (fun j _ ↦ hj j), ← Finset.sum_smul, hsum W, one_smul]
    rfl
  refine ⟨Pi.lift α, ⟨⟨∑ j, Pi.π _ j ≫ ρ j, ?_⟩⟩⟩
  simpa only [Preadditive.comp_sum, ← Category.assoc, Pi.lift_comp_π] using key

/-- **Stacks Project, Tag 0B8N (b), slice step, with no sheafification hypothesis on the slice
site.** This is `Stacks.SheafOfModules.exists_isSplitMono_over` with
`[(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]` deleted. -/
theorem exists_isSplitMono_over' (V : C)
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (hLp : Presheaf.IsSheaf J Lp.presheaf)
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallySurjective J ψ] [PresheafOfModules.IsLocallyInjective J ψ]
    {n : ℕ} (x : Fin n → Lp.obj (op V)) (y : Fin n → Np.obj (op V))
    (hxy : ∑ j, ψ.app (op V) (x j ⊗ₜ y j) = (1 : O.obj (op V))) :
    ∃ s : (⟨Lp, hLp⟩ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      O hO)).over V ⟶
        ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
          ((Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).over V),
      IsSplitMono s := by
  classical
  refine isSplitMono_of_dualBasis' (J := J.over V)
    (Lp := (sliceFunctor (O := O) V).obj Lp) (Np := (sliceFunctor (O := O) V).obj Np)
    (hO := (Over.forget V).op_comp_isSheaf_of_isSheaf (J.over V) J _ hO)
    (hLp := (Over.forget V).op_comp_isSheaf_of_isSheaf (J.over V) J _ hLp)
    (slicePairing V ψ) (fun j => sliceSection V (x j)) (fun j => sliceSection V (y j))
    (fun W j => (𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))).map
      (W.unop.hom).op (ψ.app (op V) (x j ⊗ₜ y j)))
    (fun W j => ?_) (fun W => ?_)
  · exact PresheafOfModules.naturality_apply ψ (W.unop.hom).op (x j ⊗ₜ y j)
  · have hs : ∑ j, (𝟙_ (PresheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))).map
          (W.unop.hom).op (ψ.app (op V) (x j ⊗ₜ y j))
        = (𝟙_ (PresheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))).map
          (W.unop.hom).op (∑ j, ψ.app (op V) (x j ⊗ₜ y j)) :=
      (map_sum _ _ _).symm
    refine hs.trans ((congrArg (fun z =>
      (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        O))).map
        (W.unop.hom).op z) hxy).trans ?_)
    exact PresheafOfModules.unit_map_one _ _

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks Project, Tag 0B8N (b).** On a cover of any object, an invertible module embeds as a
direct summand of a finite free module. The two sheafification hypotheses are used only by
`Stacks.SheafOfModules.isLocallyInjective_of_universal`; none is needed on the slice sites. -/
@[stacks 0B8N "(b), invertible_local_summand"]
theorem exists_cover_isDirectSummand_finiteFree
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      [IsInvertible O hO L] (U : C) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.generate (Presieve.ofArrows V f) ∈ J U ∧
        ∀ i : I, ∃ n : ℕ,
          ∃ s : L.over (V i) ⟶
              ∏ᶜ (fun _ : Fin n ↦
                SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf O
                  hO).over (V i))),
            IsSplitMono s := by
  classical
  obtain ⟨Lp, hLp, rfl⟩ : ∃ (Lp : PresheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
      (hLp : Presheaf.IsSheaf J Lp.presheaf),
      L = (⟨Lp, hLp⟩ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        O hO)) :=
    ⟨L.val, L.isSheaf, rfl⟩
  obtain ⟨Np, ψ, hsurj, hinj⟩ := exists_locallyBijective_pairing (hO := hO) hLp inferInstance
  obtain ⟨S, hSdef⟩ : ∃ S : Sieve U,
      S = imgSieve (A := SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ψ
        (1 : O.obj (op U)) := ⟨_, rfl⟩
  have hS : S ∈ J U := by
    rw [hSdef]
    exact Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map ψ) _
  refine ⟨Σ W : C, {g : W ⟶ U // S.arrows g}, fun i => i.1, fun i => i.2.1, ?_, ?_⟩
  · refine J.superset_covering ?_ hS
    intro W g hg
    exact ⟨W, 𝟙 W, g,
      Presieve.ofArrows.mk (⟨W, g, hg⟩ : Σ W : C, {g : W ⟶ U // S.arrows g}),
      Category.id_comp g⟩
  · rintro ⟨W, g, hg⟩
    rw [hSdef] at hg
    obtain ⟨t, ht⟩ := hg
    obtain ⟨n, x, y, hxy⟩ := exists_fin_tmul_eq t
    refine ⟨n, exists_isSplitMono_over' W hO hLp ψ x y ?_⟩
    have h1 : ∑ j, ψ.app (op W) (x j ⊗ₜ y j) = ψ.app (op W) (∑ j, x j ⊗ₜ y j) :=
      (map_sum _ _ _).symm
    exact h1.trans ((congrArg (fun z => ψ.app (op W) z) hxy).trans
      (ht.trans (PresheafOfModules.unit_map_one _ _)))

end Stacks.SheafOfModules

end
