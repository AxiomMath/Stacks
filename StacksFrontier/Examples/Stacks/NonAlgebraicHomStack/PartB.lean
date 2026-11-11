module

public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack
public import StacksFrontier.CategoryTheory.Sites.OverPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.SmoothGroupThickeningFirstCohomology

/-!
# Part (b) of Stacks 0AFB: lifting first cohomology along the tower of thickenings

In the situation of the example of a non-algebraic Hom-stack (Stacks, Section 0AF8), with
`S = Spec k⟦t⟧`, `Sₙ = Spec k⟦t⟧/(tⁿ⁺¹)` and `Xₙ = X ×_S Sₙ`, part (b) of the proof of Stacks
0AFB asserts that the restriction maps `H¹_fppf(X_{n+1}, A) ⟶ H¹_fppf(Xₙ, A)` are surjective.
This file records the geometric facts about the tower through which that statement is
reduced to one about a single first-order thickening:

* `Xₙ = X_{n+1} ×_S Sₙ`, as schemes and as objects of the big fppf site over `S`, compatibly
  with the transition `Xₙ ⟶ X_{n+1}` (`isPullback_thickeningSucc`,
  `thickeningObjIsoBaseChange`, `thickeningObjIsoBaseChange_hom_baseChangeFst`);
* the transition `Xₙ ⟶ X_{n+1}` is a first-order thickening, being the base change of
  `Sₙ ⟶ S_{n+1}`, whose ideal `(tⁿ⁺¹)/(tⁿ⁺²)` has square zero
  (`isFirstOrderThickening_adicThickeningSucc`, `isFirstOrderThickening_thickeningSucc`,
  `isFirstOrderThickening_baseChangeFst`);
* the thickenings of a Noetherian `X` are Noetherian, and all have the dimension of the special
  fibre `X₀` (`isNoetherian_thickening`, `topologicalKrullDim_thickening`).

With these, `surjective_restrictSucc_pointsSheaf` is part (b) itself: the surjectivity of
`restrictSucc` for the sheaf of points of a smooth commutative group scheme over `S`, obtained from
`AlgebraicGeometry.surjective_cohomologyPresheaf_map_baseChangeFst_pointsSheaf`.

The index `n` is that of `StacksFrontier.Examples.Stacks.NonAlgebraicHomStack`: `Xₙ` is cut out by
`tⁿ⁺¹`, so `X₀` is the special fibre.

## References

* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
* [Stacks Project, Section 0AF8](https://stacks.math.columbia.edu/tag/0AF8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace Stacks.Examples.NonAlgebraicHomStack

variable {k : Type u} [Field k]

/-- The inclusion `Sₙ ⟶ S_{n+1}` of consecutive thickenings of the closed point of
`Spec k⟦t⟧` is a first-order thickening: it is the spectrum of the surjection
`k⟦t⟧/(tⁿ⁺²) ⟶ k⟦t⟧/(tⁿ⁺¹)`, whose kernel `(tⁿ⁺¹)/(tⁿ⁺²)` has square zero. -/
public theorem isFirstOrderThickening_adicThickeningSucc (n : ℕ) :
    Stacks.Thickenings.IsFirstOrderThickening
      (adicThickeningSucc (PowerSeries k) (uniformizer k) n) := by
  let ψ := Ideal.Quotient.factorPow (uniformizer k) (Nat.le_succ (n + 1))
  have hsurj : Function.Surjective ψ := Ideal.Quotient.factor_surjective _
  have hker : RingHom.ker ψ ^ 2 = ⊥ := by
    rw [Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))]
    have hpow : (uniformizer k ^ (n + 1)) ^ 2 ≤ uniformizer k ^ (n + 1 + 1) := by
      rw [← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    simpa using hpow
  exact Stacks.Smooth.isFirstOrderThickening_specMap (CommRingCat.ofHom ψ) hsurj hker

/-- The square of schemes
```
Xₙ ──→ X_{n+1}
│         │
Sₙ ──→ S_{n+1}
```
is cartesian: both `Xₙ` and `X_{n+1}` are base changes of `X`. -/
public theorem isPullback_thickeningSucc_adicThickeningSucc {X : Scheme.{u}} (fX : X ⟶ base k)
    (n : ℕ) :
    IsPullback (thickeningSucc fX n) (pullback.snd fX (adicThickeningι _ (uniformizer k) n))
      (pullback.snd fX (adicThickeningι _ (uniformizer k) (n + 1)))
      (adicThickeningSucc _ (uniformizer k) n) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback fX (adicThickeningι _ (uniformizer k) (n + 1)))
  rw [thickeningSucc, adicBaseChangeSucc, pullback.lift_fst, adicThickeningSucc_ι]
  exact IsPullback.of_hasPullback fX (adicThickeningι _ (uniformizer k) n)

/-- The transition `Xₙ ⟶ X_{n+1}` is a first-order thickening. -/
public theorem isFirstOrderThickening_thickeningSucc {X : Scheme.{u}} (fX : X ⟶ base k)
    (n : ℕ) : Stacks.Thickenings.IsFirstOrderThickening (thickeningSucc fX n) :=
  Stacks.Thickenings.isFirstOrderThickening_of_isPullback
    (isPullback_thickeningSucc_adicThickeningSucc fX n)
    (isFirstOrderThickening_adicThickeningSucc n)

/-- The square of schemes
```
Xₙ ──→ X_{n+1}
│         │
Sₙ ──→    S
```
is cartesian: `Xₙ = X_{n+1} ×_S Sₙ`, because `Sₙ ⟶ S` factors through the monomorphism
`S_{n+1} ⟶ S`. -/
public theorem isPullback_thickeningSucc {X : Scheme.{u}} (fX : X ⟶ base k) (n : ℕ) :
    IsPullback (thickeningSucc fX n) (pullback.snd fX (adicThickeningι _ (uniformizer k) n))
      (thickeningToTotal fX (n + 1) ≫ fX) (adicThickeningι _ (uniformizer k) n) := by
  have hB : IsPullback (adicThickeningSucc _ (uniformizer k) n) (𝟙 _)
      (adicThickeningι _ (uniformizer k) (n + 1)) (adicThickeningι _ (uniformizer k) n) := by
    have : IsClosedImmersion (adicThickeningι (PowerSeries k) (uniformizer k) (n + 1)) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : Mono (adicThickeningι (PowerSeries k) (uniformizer k) (n + 1)) := inferInstance
    exact IsPullback.of_vert_isIso_mono ⟨by rw [adicThickeningSucc_ι, Category.id_comp]⟩
  have h := (isPullback_thickeningSucc_adicThickeningSucc fX n).paste_vert hB
  rw [Category.comp_id, ← pullback.condition] at h
  exact h

/-- All thickenings `Xₙ` have the dimension of the special fibre `X₀`: each transition
`Xₙ ⟶ X_{n+1}` is a thickening, hence a homeomorphism. -/
public theorem topologicalKrullDim_thickening {X : Scheme.{u}} (fX : X ⟶ base k) (n : ℕ) :
    topologicalKrullDim (thickening fX n) = topologicalKrullDim (thickening fX 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    have ht := (isFirstOrderThickening_thickeningSucc fX n).isThickening
    have : IsClosedImmersion (thickeningSucc fX n) := ht.1
    have hh : IsHomeomorph (thickeningSucc fX n) :=
      isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨(thickeningSucc fX n).isClosedEmbedding.isEmbedding, ht.2⟩
    exact (IsHomeomorph.topologicalKrullDim_eq _ hh).symm

/-- The thickenings of a Noetherian scheme over `Spec k⟦t⟧` are Noetherian: they are closed
subschemes of it. -/
public theorem isNoetherian_thickening {X : Scheme.{u}} (fX : X ⟶ base k) [IsNoetherian X]
    (n : ℕ) : IsNoetherian (thickening fX n) := by
  have : IsClosedImmersion (adicThickeningι (PowerSeries k) (uniformizer k) n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact isNoetherian_of_isClosedImmersion (thickeningToTotal fX n)

section Site

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (base k)) {X : Scheme.{u}}
  (fX : X ⟶ base k) (hXn : ∀ n, B.Contains (thickening fX n))

include hS in
/-- The thickening `Sₙ` of the closed point of `S = Spec k⟦t⟧` belongs to every big fppf site
containing `S`: it is a closed subscheme of `S`. -/
public theorem contains_adicThickening (n : ℕ) :
    B.Contains (adicThickening (PowerSeries k) (uniformizer k) n) := by
  have : IsClosedImmersion (adicThickeningι (PowerSeries k) (uniformizer k) n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact lt_of_le_of_lt
    (Scheme.size_le_of_mono_quasiCompact (adicThickeningι (PowerSeries k) (uniformizer k) n)) hS

/-- The closed immersion `Sₙ ⟶ S`, as a morphism of the big fppf site. -/
public def truncationι (n : ℕ) : B.obj (contains_adicThickening B hS n) ⟶ B.obj hS :=
  ObjectProperty.homMk (adicThickeningι (PowerSeries k) (uniformizer k) n)

public instance mono_truncationι (n : ℕ) : Mono (truncationι B hS n) := by
  have : IsClosedImmersion (adicThickeningι (PowerSeries k) (uniformizer k) n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : Mono (B.inclusion.map (truncationι B hS n)) :=
    (inferInstance : Mono (adicThickeningι (PowerSeries k) (uniformizer k) n))
  exact B.inclusion.mono_of_mono_map this

/-- The square `Xₙ ⟶ X_{n+1}`, `Xₙ ⟶ Sₙ`, `X_{n+1} ⟶ S`, `Sₙ ⟶ S` is cartesian in the big
fppf site. -/
public theorem isPullback_thickeningObjSucc_left (n : ℕ) :
    IsPullback (thickeningObjSucc B hS fX hXn n).left
      (ObjectProperty.homMk (pullback.snd fX (adicThickeningι _ (uniformizer k) n)) :
        B.obj (hXn n) ⟶ B.obj (contains_adicThickening B hS n))
      (thickeningObj B hS fX hXn (n + 1)).hom (truncationι B hS n) :=
  IsPullback.of_map_of_faithful (F := B.inclusion) (isPullback_thickeningSucc fX n)

/-- `Xₙ` is the base change `X_{n+1} ×_S Sₙ`, as objects of the big fppf site over `S`. -/
public def thickeningObjIsoBaseChange (n : ℕ) :
    thickeningObj B hS fX hXn n ≅ (Over.map (truncationι B hS n)).obj
      ((Over.pullback (truncationι B hS n)).obj (thickeningObj B hS fX hXn (n + 1))) :=
  Over.isoMk (isPullback_thickeningObjSucc_left B hS fX hXn n).isoPullback (by
    change _ ≫ pullback.snd _ _ ≫ truncationι B hS n = _
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ truncationι B hS n)
      (isPullback_thickeningObjSucc_left B hS fX hXn n).isoPullback_hom_snd).trans ?_)
    apply ObjectProperty.hom_ext
    exact pullback.condition.symm)

/-- Under `thickeningObjIsoBaseChange`, the first projection `X_{n+1} ×_S Sₙ ⟶ X_{n+1}` is the
transition `Xₙ ⟶ X_{n+1}`. -/
public theorem thickeningObjIsoBaseChange_hom_baseChangeFst (n : ℕ) :
    (thickeningObjIsoBaseChange B hS fX hXn n).hom ≫
        Sheaf.baseChangeFst (truncationι B hS n) (thickeningObj B hS fX hXn (n + 1)) =
      thickeningObjSucc B hS fX hXn n := by
  apply Over.OverMorphism.ext
  exact (isPullback_thickeningObjSucc_left B hS fX hXn n).isoPullback_hom_fst

/-- The first projection `X_{n+1} ×_S Sₙ ⟶ X_{n+1}` is a first-order thickening: it is the base
change of `Sₙ ⟶ S_{n+1}` along `X_{n+1} ⟶ S_{n+1}`. -/
public theorem isFirstOrderThickening_baseChangeFst (n : ℕ) :
    Stacks.Thickenings.IsFirstOrderThickening (B.inclusion.map
      (Sheaf.baseChangeFst (truncationι B hS n) (thickeningObj B hS fX hXn (n + 1))).left) := by
  let h := isPullback_thickeningObjSucc_left B hS fX hXn n
  have hinv := h.isoPullback_inv_fst
  have hsq : IsPullback
      (B.inclusion.map (Sheaf.baseChangeFst (truncationι B hS n)
        (thickeningObj B hS fX hXn (n + 1))).left)
      (B.inclusion.map h.isoPullback.inv) (𝟙 _) (thickeningSucc fX n) :=
    IsPullback.of_vert_isIso ⟨by
      rw [Category.comp_id]
      exact (congrArg B.inclusion.map hinv).symm.trans (B.inclusion.map_comp _ _)⟩
  exact Stacks.Thickenings.isFirstOrderThickening_of_isPullback hsq
    (isFirstOrderThickening_thickeningSucc fX n)

end Site


section Main

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (base k)) {X : Scheme.{u}}
  (fX : X ⟶ base k) (hXn : ∀ n, B.Contains (thickening fX n))
  [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u})]

/-- The ring `Γ(Spec k⟦t⟧, ⊤) ≅ k⟦t⟧` of the base is local. -/
public instance isLocalRing_base_top : IsLocalRing Γ(base k, ⊤) :=
  (Scheme.ΓSpecIso (.of (PowerSeries k))).symm.commRingCatIsoToRingEquiv.isLocalRing

/-- **Part (b) of the proof of Stacks 0AFB.** In the situation of the example of a
non-algebraic Hom-stack, the restriction maps `H¹_fppf(X_{n+1}, A) ⟶ H¹_fppf(Xₙ, A)` are
surjective, for every `n`. This is the hypothesis `hsurjective` of
`exists_compatible_ne_restrictTotal` and `not_surjective_toCompatibleSystems`.

Of the situation, the statement uses only what the source's argument uses: `A` is a smooth
commutative group scheme over `S = Spec k⟦t⟧` (an abelian scheme `A₀ ×_k S` is one), `X` is
Noetherian (it is projective over `S`) and the special fibre `X₀` has dimension at most one (it is a
curve). The source's argument — the obstruction to deforming an `A`-torsor from `Xₙ` to `X_{n+1}`
lies in an `H²` of a vector bundle on the curve `X₀` — is carried out cohomologically by
`AlgebraicGeometry.surjective_cohomologyPresheaf_map_baseChangeFst_pointsSheaf`, applied to the
first-order thickening `Xₙ = X_{n+1} ×_S Sₙ ⟶ X_{n+1}`. -/
public theorem surjective_restrictSucc_pointsSheaf (A : Over (base k)) [GrpObj A]
    [IsCommMonObj A] [Smooth A.hom] (hA : B.Contains A.left) [IsNoetherian X]
    (hdim : topologicalKrullDim (thickening fX 0) ≤ 1) (n : ℕ) :
    Function.Surjective (restrictSucc B hS fX hXn (pointsSheaf B (base k) hS A hA) n) := by
  have : IsNoetherian (B.inclusion.obj (thickeningObj B hS fX hXn (n + 1)).left) :=
    isNoetherian_thickening fX (n + 1)
  have hsurj := surjective_cohomologyPresheaf_map_baseChangeFst_pointsSheaf B hS
    (contains_adicThickening B hS n) (truncationι B hS n) A hA (thickeningObj B hS fX hXn (n + 1))
    (isFirstOrderThickening_baseChangeFst B hS fX hXn n)
    ((topologicalKrullDim_thickening fX (n + 1)).le.trans hdim)
  let e := thickeningObjIsoBaseChange B hS fX hXn n
  intro x
  obtain ⟨y, hy⟩ := hsurj (((pointsSheaf B (base k) hS A hA).cohomologyPresheaf 1).map e.inv.op x)
  refine ⟨y, ?_⟩
  change ((pointsSheaf B (base k) hS A hA).cohomologyPresheaf 1).map
    (thickeningObjSucc B hS fX hXn n).op y = x
  rw [← thickeningObjIsoBaseChange_hom_baseChangeFst B hS fX hXn n, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply, hy, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, Iso.hom_inv_id, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

end Main

end Stacks.Examples.NonAlgebraicHomStack
