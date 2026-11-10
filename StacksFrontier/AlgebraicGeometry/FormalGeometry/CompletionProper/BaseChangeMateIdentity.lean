module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.MateComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicBaseChangeSituation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageComparison
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.CompletionProjectionQuotient

/-!
# The mate identity for the unit of the morphism being base changed, and the square `hγ`

For a commuting square of schemes

```
X' --g'--> X
|f'        |f
S' --g-->  S
```

the degree-zero base-change comparison `g^*f_*F ⟶ f'_*(g')^*F` of
`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange` is related by
`StacksFrontier/AlgebraicGeometry/FlatBaseChange/Pushforward.lean` to the unit of `(g')^* ⊣ g'_*`,
and only on global sections. The square `hγ` of the second paragraph of Stacks 088B needs it related
to the unit of the adjunction of the morphism *being base changed*: that for an `𝒪_S`-module `𝒢`,

`g^*𝒢 ⟶ g^*(f_*f^*𝒢) ⟶ f'_*((g')^*f^*𝒢) ≅ f'_*((f')^*g^*𝒢)`

is the unit of `(f')^* ⊣ (f')_*` at `g^*𝒢`. That is a mate identity for the two adjunctions of
the square, and it turns out to be **already in the library**, for the other construction of the
comparison: `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is the mate of the
comparison of the two composite direct images along the adjunctions of `g'` and `g`, and
`Stacks.Modules.baseChangeNatTrans_eq_mateEquiv` (`Descent/FlatBaseChangeComparison.lean`)
identifies it with the mate of `Stacks.Modules.pullbackSquareIso` along the adjunctions of `f`
and `f'`, whose two triangle identities are
`Stacks.Modules.map_unit_comp_baseChangeNatTrans_app` and
`…pullback_map_baseChangeNatTrans_app_comp_counit`. What was missing is only the bridge to the
adjoint-transpose construction, `baseChangeNatTrans_app_eq_pushforwardBaseChange`.

## Main results

* `Stacks.Algebraization.unit_comp_pushforwardBaseChange` — **the mate identity**, for
  `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange` and
  `Stacks.Modules.pullbackSquareIso`.
* `Stacks.Algebraization.completionPullbackIso_inv_app_comp` — **the level `n` of Stacks 0887 is
  the identification of the levels**: the inverse of `(f^*𝒢) ^∧ ≅ f^*(𝒢 ^∧)` at level `n`,
  followed by a transport of ideal sheaves, by the identification of the `n`-th term of a
  completion with the quotient and by the inverse of
  `Stacks.Algebraization.pullbackIdealPowerQuotientIsoOfEq`, is the pullback of the
  identification of the `n`-th term of `𝒢 ^∧` with the quotient.
* `Stacks.Algebraization.completionProjection_comp_completionFunctorObjCongr`,
  `…completionPullbackIso_inv_hom_id_app` and
  `…completionProjection_comp_completionPullbackIso_hom_app_comp` — the three composites with the
  projection onto the `n`-th term of a completion out of which that identification is cancelled:
  the transport along an equality of ideal sheaves carries one projection to the other, the
  inverse of Stacks 0887 is a section of it at the level, and the level `n` of Stacks 0887
  followed by the pullback of the transport of the level is the pullback of the quotient
  projection.
* `Stacks.Algebraization.comp_comp_eq_of_epi_factorizations` — **that cancellation**, as a general
  categorical lemma with all its data implicit: it is what lets the identification of the levels
  be *proved* at a base change rather than transported there, where the transport of ideal sheaves
  is not definitional and the kernel cannot reduce the `Eq.rec`; see "What the kernel's budget is
  sensitive to" in `CompletionProper/AdicBaseChangeSquares.lean`.
* `Stacks.Algebraization.unit_comp_map_of_factorizations` — **the unit half of the square `hγ`**:
  the unit of `(f')^* ⊣ (f')_*` at `g^*M` followed by `f'_*b'` is the pullback along `g` of the
  unit of `f^* ⊣ f_*` followed by `f_*b`, followed by the degree-zero base-change comparison at
  `A` and by `f'_*c`.
* `Stacks.Algebraization.pushforwardBaseChange_comp_of_factorizations` — **the level half**: that
  same comparison followed by `f'_*c`, by `e'` and by `θ` is the pullback along `g` of `e`; it is
  in turn `Stacks.Algebraization.pushforward_map_comp_of_factorizations` — itself
  `…comp_eq_map_comp_comp_of_factorizations` followed by `…map_comp_map_comp_of_factorization` —
  and `Stacks.Algebraization.pushforwardBaseChange_comp_map_of_factorizations`.
* `Stacks.Algebraization.directImageComparison_square_of_factorizations` — **the square `hγ`
  from its ingredients**, for arbitrary comparison maps: given a factorization of the
  base-changed `β'_n` through the composition isomorphism and the pullback of `β_n`, a
  factorization of the tail of `β'_n` through the identification of the levels, the mate identity
  at the module in question, and the invertibility of the degree-zero base change at the level,
  the two `γ`'s correspond. It is the two halves, chained by
  `Stacks.Algebraization.comp_eq_map_comp_of_factorizations`.

## Implementation notes

`Stacks.Algebraization.directImageComparison_square_of_factorizations` takes the comparison maps
themselves as binders, together with the equations they satisfy. The reason is the one recorded
in the module docstring of `CompletionProper/AdicBaseChangeSquares.lean`: a declaration whose
statement spells more than about one composition of morphisms of modules on the base change
`X' ×_{Spec B} Spec B ^∧`, and which has to be matched against another spelling by unfolding,
exhausts the kernel's reduction budget. With the maps as binders the conclusion becomes the
statement of `hγ` under substitution alone.

Its mathematical content is the mate identity, the naturality
`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality` of the comparison in
the module used twice, and the two factorizations.

**Why it is assembled from halves rather than proved in one go.** Even with the maps as binders,
the single application of this reduction at the base change is over the kernel's budget, and so
is one declaration applying both halves: the budget is spent on *checking the
arguments* of the application, of which the full reduction has two dozen. So the reduction is
split into two general lemmas with about half the data each, meeting at the named intermediate
morphism `pushforwardBaseChange w A ≫ f'_*c`, and chained by
`Stacks.Algebraization.comp_eq_map_comp_of_factorizations`; the level half is split again, at
`f'_*((g')^*u) ≫ ν` and at `f'_*(u' ≫ q) ≫ ν`. The three chaining lemmas
`…comp_eq_map_comp_of_factorizations`, `…comp_comp_eq_of_factorizations` and
`…comp_eq_of_factorizations_right` have all their data implicit on purpose: an application of one
of them is determined by its two equations, so chaining two halves at the base change costs
nothing beyond naming them.

With this split, each piece of `hγ` at the actual base change is inside the budget, and `hγ` is
a theorem there (`Stacks.Algebraization.adicBaseChangeDirectImageComparison_square`). The one
piece which cannot be had by instantiating a general lemma at all is the identification of the
levels, because the transport of ideal sheaves on the base change is not definitional; it is
proved there by the epimorphism-cancelling argument of
`Stacks.Algebraization.comp_comp_eq_of_epi_factorizations`, with that transport left as a binder.
See "What the kernel's budget is sensitive to" in
`CompletionProper/AdicBaseChangeSquares.lean`.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe v₁ v₂ u₁ u₂ u

namespace Stacks.Algebraization

open Stacks.Coherent Stacks.AlgebraicGeometry.FlatBaseChange

/-! ### The mate identity -/

/-- **The degree-zero base-change comparison is compatible with the unit of the adjunction of the
morphism being base changed.** -/
public theorem unit_comp_pushforwardBaseChange {X X' S S' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g) (M : S.Modules) :
    (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        pushforwardBaseChange w ((Scheme.Modules.pullback f).obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
          ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pushforward f').map
          ((Stacks.Modules.pullbackSquareIso f f' g g' w).hom.app M) :=
  (congrArg
      (fun k => (Scheme.Modules.pullback g).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫ k)
      (baseChangeNatTrans_app_eq_pushforwardBaseChange w
        ((Scheme.Modules.pullback f).obj M)).symm).trans
    (Stacks.Modules.map_unit_comp_baseChangeNatTrans_app w M)

/-! ### The levels of the pullback of a completion -/

/-- **The projection onto a term of a completion is compatible with a transport of the ideal
sheaf.** The projection of `F` onto the `n`-th term of its completion along `I`, followed by the
`n`-th component of `Stacks.Algebraization.completionFunctorObjCongr` at an equality `I = J` of
ideal sheaves, is the projection of `F` onto the `n`-th term of its completion along `J`.

The transport is the identity once the equality is substituted. It is stated separately so that it
can be *used* at an equality which is not definitional: the two sides then still hold by this one
lemma, whereas a declaration that both carries the transport and identifies the terms of the two
completions at such an equality is beyond the kernel's reduction budget. -/
public theorem completionProjection_comp_completionFunctorObjCongr {X : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] {I J : X.IdealSheafData} (e : I = J)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    completionProjection X I F n ≫ (completionFunctorObjCongr e F).hom.app (op n) =
      completionProjection X J F n := by
  cases e
  exact Category.comp_id (obj := X.Modules) _

/-- The inverse of `Stacks.Coherent.completionPullbackIso` followed by the isomorphism itself is
the identity, read at the level `n`. -/
public theorem completionPullbackIso_inv_hom_id_app {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] (f : X ⟶ Y) (K : Y.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (n : ℕᵒᵖ) :
    ((ObjectProperty.ι _).mapIso (completionPullbackIso f K G).symm).hom.app n ≫
        (completionPullbackIso f K G).hom.hom.app n = 𝟙 _ := by
  simp

/-- **The projection onto a term of the completion of a pullback, followed by the level `n` of
Stacks 0887 and by the pullback of the transport of the level.** It is the pullback of the
quotient projection of `𝒢`.

This is the normalization
`Stacks.Coherent.completionProjection_completionPullbackComparison` of the comparison, followed
by the reading `Stacks.Algebraization.completionProjection_comp_eqToHom` of the projection of
`𝒢` as its quotient projection, pulled back along `f`. -/
public theorem completionProjection_comp_completionPullbackIso_hom_app_comp {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) (K : Y.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (n : ℕ) :
    completionProjection X (K.comap f) ((pullbackCoherentModules f).obj G) n ≫
        ((completionPullbackIso f K G).hom.hom.app (op n) ≫
          (Scheme.Modules.pullback f).map (eqToHom (completionFunctor_obj Y K G n))) =
      (Scheme.Modules.pullback f).map
        (cokernel.π (C := Y.Modules) (idealPowerMultiple K (n + 1) G.obj).ι) :=
  (Category.assoc (obj := X.Modules) _ _ _).symm.trans
    ((congrArg
        (fun k => k ≫ (Scheme.Modules.pullback f).map
          (eqToHom (completionFunctor_obj Y K G n)))
        (completionProjection_completionPullbackComparison f K G (op n))).trans
      (((Scheme.Modules.pullback f).map_comp _ _).symm.trans
        (congrArg (Scheme.Modules.pullback f).map
          (Stacks.Algebraization.completionProjection_comp_eqToHom_cokernelπ K G n))))

/-- **The level `n` of Stacks 0887 is the identification of the levels.** -/
public theorem completionPullbackIso_inv_app_comp
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) (K : Y.IdealSheafData)
    {I : X.IdealSheafData} (h : K.comap f = I)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (n : ℕ) :
    ((ObjectProperty.ι _).mapIso (completionPullbackIso f K G).symm ≪≫
          completionFunctorObjCongr h ((pullbackCoherentModules f).obj G)).hom.app (op n) ≫
        (eqToHom (completionFunctor_obj X I ((pullbackCoherentModules f).obj G) n) ≫
          (pullbackIdealPowerQuotientIsoOfEq f K h (n + 1) G.obj).inv) =
      (Scheme.Modules.pullback f).map (eqToHom (completionFunctor_obj Y K G n)) := by
  subst h
  have hA : completionProjection X (K.comap f) ((pullbackCoherentModules f).obj G) n ≫
      (eqToHom (completionFunctor_obj X (K.comap f) ((pullbackCoherentModules f).obj G) n) ≫
        (pullbackIdealPowerQuotientIsoOfEq f K rfl (n + 1) G.obj).inv) =
      (Scheme.Modules.pullback f).map
        (cokernel.π (C := Y.Modules) (idealPowerMultiple K (n + 1) G.obj).ι) :=
    (Category.assoc (obj := X.Modules) _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (pullbackIdealPowerQuotientIsoOfEq f K rfl (n + 1) G.obj).inv)
          (Stacks.Algebraization.completionProjection_comp_eqToHom_cokernelπ (K.comap f)
            ((pullbackCoherentModules f).obj G) n)).trans
        ((Iso.comp_inv_eq _).2
          (map_π_comp_pullbackIdealPowerQuotientIsoOfEq_hom f K rfl (n + 1) G.obj).symm))
  have hepi := Stacks.Algebraization.epi_completionProjection X (K.comap f)
    ((pullbackCoherentModules f).obj G) n
  have hmain :
      eqToHom (completionFunctor_obj X (K.comap f) ((pullbackCoherentModules f).obj G) n) ≫
          (pullbackIdealPowerQuotientIsoOfEq f K rfl (n + 1) G.obj).inv =
        (completionPullbackIso f K G).hom.hom.app (op n) ≫
          (Scheme.Modules.pullback f).map (eqToHom (completionFunctor_obj Y K G n)) :=
    (@cancel_epi _ _ _ _ _ _ hepi _ _).mp
      (hA.trans (completionProjection_comp_completionPullbackIso_hom_app_comp f K G n).symm)
  have hcongr : (completionFunctorObjCongr (rfl : K.comap f = K.comap f)
      ((pullbackCoherentModules f).obj G)).hom.app (op n) = 𝟙 _ := rfl
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, hcongr]
  rw [hmain]
  erw [Category.id_comp]
  exact (Category.assoc (obj := X.Modules) _ _ _).symm.trans
    ((congrArg (· ≫ _) (completionPullbackIso_inv_hom_id_app f K G (op n))).trans
      (Category.id_comp _))

/-! ### Chaining two factorizations through a functor -/

/-- **Two factorizations meeting at one morphism compose to a functor image.** If `a` is `F.map p`
followed by `m` and `m` followed by `t` is `F.map q`, then `a ≫ t` is `F.map (p ≫ q)`.

Everything but the functor is implicit, so an application of this is determined by the two
equations alone; that is what makes it usable to chain
`Stacks.Algebraization.unit_comp_map_of_factorizations` with
`Stacks.Algebraization.pushforwardBaseChange_comp_of_factorizations` without respelling any of
their data. -/
public theorem comp_eq_map_comp_of_factorizations {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) {X Y Z : C} {Q : D} {p : X ⟶ Y} {q : Y ⟶ Z}
    {a : F.obj X ⟶ Q} {m : F.obj Y ⟶ Q} {t : Q ⟶ F.obj Z} (ha : a = F.map p ≫ m)
    (hm : m ≫ t = F.map q) :
    a ≫ t = F.map (p ≫ q) :=
  (congrArg (fun k => k ≫ t) ha).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => F.map p ≫ k) hm).trans (F.map_comp p q).symm))

/-- **Two factorizations meeting at one morphism compose.** If `b` followed by `t` is `m` and `a`
followed by `m` is `z`, then `a ≫ b` followed by `t` is `z`.

As with `Stacks.Algebraization.comp_eq_map_comp_of_factorizations`, everything is implicit, so an
application is determined by the two equations alone. -/
public theorem comp_comp_eq_of_factorizations {C : Type u₁} [Category.{v₁} C] {W X Y Z : C}
    {a : W ⟶ X} {b : X ⟶ Y} {t : Y ⟶ Z} {m : X ⟶ Z} {z : W ⟶ Z} (hb : b ≫ t = m)
    (ha : a ≫ m = z) :
    (a ≫ b) ≫ t = z :=
  (Category.assoc a b t).trans ((congrArg (fun k => a ≫ k) hb).trans ha)

/-- **A factorization of the second factor of a composite.** If `t` is `m` and `a` followed by
`m` is `z`, then `a` followed by `t` is `z`. All data is implicit. -/
public theorem comp_eq_of_factorizations_right {C : Type u₁} [Category.{v₁} C] {W X Y : C}
    {a : W ⟶ X} {t m : X ⟶ Y} {z : W ⟶ Y} (ht : t = m) (ha : a ≫ m = z) :
    a ≫ t = z :=
  (congrArg (fun k => a ≫ k) ht).trans ha

/-- **An identification out of a retract, pinned by an epimorphism.** Let `p` and `pK` be two
morphisms out of one object, `γ` a morphism carrying `pK` to `p`, and `ωinv` a section of `ω`.
If `p ≫ σ` and `pK ≫ ω ≫ τ` are one and the same morphism `z`, then `(ωinv ≫ γ) ≫ σ` is `τ`.

`pK` and the witness that it is an epimorphism are the only explicit arguments: everything else is
determined by the four equations, so an application costs no more than naming them. It is the
shape of the epimorphism-cancelling argument which pins a morphism out of a completion by its
composites with the projections — `pK` and `p` being the projections onto the `n`-th terms of the
completions along two equal ideal sheaves, `γ` the transport between them and `ω` the level `n` of
Stacks 0887 — so that no declaration has to carry both the transport and the identification of the
two presentations of the level. -/
public theorem comp_comp_eq_of_epi_factorizations {C : Type u₁} [Category.{v₁} C]
    {F CI CK D T : C} (pK : F ⟶ CK) (hepi : Epi pK) {p : F ⟶ CI} {γ : CK ⟶ CI} {ω : CK ⟶ D}
    {ωinv : D ⟶ CK} {σ : CI ⟶ T} {τ : D ⟶ T} {z : F ⟶ T} (hγ : pK ≫ γ = p)
    (hω : ωinv ≫ ω = 𝟙 D) (hσ : p ≫ σ = z) (hτ : pK ≫ ω ≫ τ = z) :
    (ωinv ≫ γ) ≫ σ = τ :=
  have hmain : γ ≫ σ = ω ≫ τ :=
    (@cancel_epi _ _ _ _ _ pK hepi _ _).mp
      (((Category.assoc pK γ σ).symm.trans (congrArg (fun k => k ≫ σ) hγ)).trans
        (hσ.trans hτ.symm))
  (Category.assoc ωinv γ σ).trans
    ((congrArg (fun k => ωinv ≫ k) hmain).trans
      ((Category.assoc ωinv ω τ).symm.trans
        ((congrArg (fun k => k ≫ τ) hω).trans (Category.id_comp τ))))

/-! ### The two halves of the square `hγ` -/

/-- **The unit half of the square `hγ`.** In the situation of
`Stacks.Algebraization.directImageComparison_square_of_factorizations`, the unit of
`(f')^* ⊣ (f')_*` at `g^*M` followed by `f'_*b'` is the pullback along `g` of the unit of
`f^* ⊣ f_*` at `M` followed by `f_*b`, followed by the degree-zero base-change comparison at `A`
and by `f'_*c`.

This is the mate identity `hr` and the naturality
`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality` of the comparison in
the module, read at `b`, together with the factorization `b' = r ≫ (g'^*b ≫ c)`.

The morphism `pushforwardBaseChange w A ≫ f'_*c` is the named intermediate at which this half
meets `Stacks.Algebraization.pushforwardBaseChange_comp_of_factorizations`. -/
public theorem unit_comp_map_of_factorizations {X X' S S' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g) (M : S.Modules)
    {A : X.Modules} {A' : X'.Modules}
    {b : (Scheme.Modules.pullback f).obj M ⟶ A}
    {b' : (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj M) ⟶ A'}
    {c : (Scheme.Modules.pullback g').obj A ⟶ A'}
    {r : (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj M) ⟶
      (Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback f).obj M)}
    {cc : (Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback f).obj M) ⟶ A'}
    (hr : (Scheme.Modules.pullback g).map
            ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
          pushforwardBaseChange w ((Scheme.Modules.pullback f).obj M) =
        (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
            ((Scheme.Modules.pullback g).obj M) ≫
          (Scheme.Modules.pushforward f').map r)
    (hb : b' = r ≫ cc)
    (hcc : cc = (Scheme.Modules.pullback g').map b ≫ c) :
    (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
          ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pushforward f').map b' =
      (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
            (Scheme.Modules.pushforward f).map b) ≫
        (pushforwardBaseChange w A ≫ (Scheme.Modules.pushforward f').map c) := by
  subst hb hcc
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 1 2 => rw [← hr]
  slice_lhs 2 3 => rw [← pushforwardBaseChange_naturality w b]
  simp

/-- **The tail of the level half of the square `hγ`.** `e'` followed by `θ` is the direct image
along `f'` of `u' ≫ q` followed by `ν`.

Only `f'` enters, and only the two readings `he'` and `hθ` of `e'` and of `θ`: neither `f`, nor
`g`, nor `g'`, nor the commuting square, nor `c`, nor `u` occurs, and the target of `q` and the
common target of `ν` and `θ` are arbitrary modules. -/
public theorem comp_eq_map_comp_comp_of_factorizations {X' S' : Scheme.{u}} (f' : X' ⟶ S')
    {A' L' Lq : X'.Modules} {T : S'.Modules} {u' : A' ⟶ L'} {q : L' ⟶ Lq}
    {e' : (Scheme.Modules.pushforward f').obj A' ⟶ (Scheme.Modules.pushforward f').obj L'}
    {ν : (Scheme.Modules.pushforward f').obj Lq ⟶ T}
    {θ : (Scheme.Modules.pushforward f').obj L' ⟶ T}
    (he' : e' = (Scheme.Modules.pushforward f').map u')
    (hθ : θ = (Scheme.Modules.pushforward f').map q ≫ ν) :
    e' ≫ θ = (Scheme.Modules.pushforward f').map (u' ≫ q) ≫ ν := by
  subst he' hθ
  rw [Functor.map_comp, Category.assoc]

/-- **The level identification inside the level half of the square `hγ`.** The direct image along
`f'` of `c`, followed by the direct image of `u' ≫ q` and by `ν`, is the direct image of
`(g')^*u` followed by `ν`.

Only the factorization `hc` of `(g')^*u` through `c`, `u'` and `q` enters: neither `f`, nor `g`,
nor the commuting square, nor `e'`, nor `θ` occurs, and the common target is an arbitrary
module. -/
public theorem map_comp_map_comp_of_factorization {X X' S' : Scheme.{u}} (f' : X' ⟶ S')
    (g' : X' ⟶ X) {A L : X.Modules} {A' L' : X'.Modules} {T : S'.Modules} {u : A ⟶ L}
    {u' : A' ⟶ L'} {q : L' ⟶ (Scheme.Modules.pullback g').obj L}
    {c : (Scheme.Modules.pullback g').obj A ⟶ A'}
    {ν : (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj L) ⟶ T}
    (hc : c ≫ u' ≫ q = (Scheme.Modules.pullback g').map u) :
    (Scheme.Modules.pushforward f').map c ≫
        ((Scheme.Modules.pushforward f').map (u' ≫ q) ≫ ν) =
      (Scheme.Modules.pushforward f').map ((Scheme.Modules.pullback g').map u) ≫ ν := by
  rw [← Category.assoc, ← Functor.map_comp, hc]

/-- **The level identification of the level half of the square `hγ`.** The direct image along
`f'` of `c`, followed by `e'` and by `θ`, is the direct image of `(g')^*u` followed by `ν`.

Only `f'` and `g'` enter: this is the part of the level half which does not see the base-change
comparison, so neither `f`, nor `g`, nor the commuting square occurs, and the common target of
`ν` and `θ` is an arbitrary module. It is
`Stacks.Algebraization.comp_eq_map_comp_comp_of_factorizations` followed by
`Stacks.Algebraization.map_comp_map_comp_of_factorization`. -/
public theorem pushforward_map_comp_of_factorizations {X X' S' : Scheme.{u}} (f' : X' ⟶ S')
    (g' : X' ⟶ X) {A L : X.Modules} {A' L' : X'.Modules} {T : S'.Modules} {u : A ⟶ L}
    {u' : A' ⟶ L'} {q : L' ⟶ (Scheme.Modules.pullback g').obj L}
    {c : (Scheme.Modules.pullback g').obj A ⟶ A'}
    {e' : (Scheme.Modules.pushforward f').obj A' ⟶ (Scheme.Modules.pushforward f').obj L'}
    {ν : (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj L) ⟶ T}
    {θ : (Scheme.Modules.pushforward f').obj L' ⟶ T}
    (hc : c ≫ u' ≫ q = (Scheme.Modules.pullback g').map u)
    (he' : e' = (Scheme.Modules.pushforward f').map u')
    (hθ : θ = (Scheme.Modules.pushforward f').map q ≫ ν) :
    (Scheme.Modules.pushforward f').map c ≫ e' ≫ θ =
      (Scheme.Modules.pushforward f').map ((Scheme.Modules.pullback g').map u) ≫ ν :=
  comp_eq_of_factorizations_right (comp_eq_map_comp_comp_of_factorizations f' he' hθ)
    (map_comp_map_comp_of_factorization f' g' hc)

/-- **The base-change comparison inside the level half of the square `hγ`.** The degree-zero
base-change comparison at `A`, followed by the direct image along `f'` of `(g')^*u` and by `ν`,
is the pullback along `g` of `e`.

This is the naturality
`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality` of the comparison in
the module read at `u`, followed by the invertibility `hν` of the comparison at `L`. Neither the
modules on `X'` nor the comparison maps between them occur. -/
public theorem pushforwardBaseChange_comp_map_of_factorizations {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    {A L : X.Modules} {u : A ⟶ L}
    {e : (Scheme.Modules.pushforward f).obj A ⟶ (Scheme.Modules.pushforward f).obj L}
    {ν : (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj L) ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj L)}
    (he : e = (Scheme.Modules.pushforward f).map u)
    (hν : pushforwardBaseChange w L ≫ ν = 𝟙 _) :
    pushforwardBaseChange w A ≫
        ((Scheme.Modules.pushforward f').map ((Scheme.Modules.pullback g').map u) ≫ ν) =
      (Scheme.Modules.pullback g).map e := by
  subst he
  rw [← Category.assoc, ← pushforwardBaseChange_naturality w u, Category.assoc, hν,
    Category.comp_id]

/-- **The level half of the square `hγ`.** In the situation of
`Stacks.Algebraization.directImageComparison_square_of_factorizations`, the degree-zero
base-change comparison at `A` followed by `f'_*c`, by `e'` and by `θ` is the pullback along `g`
of `e`.

This is the factorization `hc` of `g'^*u` through `c`, `u'` and `q`, the naturality
`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality` of the comparison in
the module read at `u`, and the invertibility `hν` of the comparison at `L`.

The morphism `pushforwardBaseChange w A ≫ f'_*c` is the named intermediate at which this half
meets `Stacks.Algebraization.unit_comp_map_of_factorizations`. -/
public theorem pushforwardBaseChange_comp_of_factorizations {X X' S S' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g) {A L : X.Modules}
    {A' L' : X'.Modules} {u : A ⟶ L} {u' : A' ⟶ L'}
    {q : L' ⟶ (Scheme.Modules.pullback g').obj L}
    {c : (Scheme.Modules.pullback g').obj A ⟶ A'}
    {e : (Scheme.Modules.pushforward f).obj A ⟶ (Scheme.Modules.pushforward f).obj L}
    {e' : (Scheme.Modules.pushforward f').obj A' ⟶ (Scheme.Modules.pushforward f').obj L'}
    {ν : (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj L) ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj L)}
    {θ : (Scheme.Modules.pushforward f').obj L' ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj L)}
    (hc : c ≫ u' ≫ q = (Scheme.Modules.pullback g').map u)
    (he : e = (Scheme.Modules.pushforward f).map u)
    (he' : e' = (Scheme.Modules.pushforward f').map u')
    (hθ : θ = (Scheme.Modules.pushforward f').map q ≫ ν)
    (hν : pushforwardBaseChange w L ≫ ν = 𝟙 _) :
    (pushforwardBaseChange w A ≫ (Scheme.Modules.pushforward f').map c) ≫ e' ≫ θ =
      (Scheme.Modules.pullback g).map e :=
  comp_comp_eq_of_factorizations
    (pushforward_map_comp_of_factorizations f' g' hc he' hθ)
    (pushforwardBaseChange_comp_map_of_factorizations f f' g g' w he hν)

/-! ### The square `hγ` from its ingredients -/

/-- **The square `hγ` from its ingredients.** -/
public theorem directImageComparison_square_of_factorizations
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (M : S.Modules) {A L : X.Modules} {A' L' : X'.Modules}
    {b : (Scheme.Modules.pullback f).obj M ⟶ A} {u : A ⟶ L}
    {b' : (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj M) ⟶ A'}
    {u' : A' ⟶ L'} {q : L' ⟶ (Scheme.Modules.pullback g').obj L}
    {c : (Scheme.Modules.pullback g').obj A ⟶ A'}
    {r : (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj M) ⟶
      (Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback f).obj M)}
    {cc : (Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback f).obj M) ⟶ A'}
    {e : (Scheme.Modules.pushforward f).obj A ⟶ (Scheme.Modules.pushforward f).obj L}
    {e' : (Scheme.Modules.pushforward f').obj A' ⟶ (Scheme.Modules.pushforward f').obj L'}
    {ν : (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj L) ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj L)}
    {θ : (Scheme.Modules.pushforward f').obj L' ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj L)}
    (hr : (Scheme.Modules.pullback g).map
            ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
          pushforwardBaseChange w ((Scheme.Modules.pullback f).obj M) =
        (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
            ((Scheme.Modules.pullback g).obj M) ≫
          (Scheme.Modules.pushforward f').map r)
    (hb : b' = r ≫ cc)
    (hcc : cc = (Scheme.Modules.pullback g').map b ≫ c)
    (hc : c ≫ u' ≫ q = (Scheme.Modules.pullback g').map u)
    (he : e = (Scheme.Modules.pushforward f).map u)
    (he' : e' = (Scheme.Modules.pushforward f').map u')
    (hθ : θ = (Scheme.Modules.pushforward f').map q ≫ ν)
    (hν : pushforwardBaseChange w L ≫ ν = 𝟙 _) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
            ((Scheme.Modules.pullback g).obj M) ≫
          (Scheme.Modules.pushforward f').map b') ≫ e' ≫ θ =
      (Scheme.Modules.pullback g).map
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
          (Scheme.Modules.pushforward f).map b) ≫ e) :=
  comp_eq_map_comp_of_factorizations (Scheme.Modules.pullback g)
    (unit_comp_map_of_factorizations f f' g g' w M hr hb hcc)
    (pushforwardBaseChange_comp_of_factorizations f f' g g' w hc he he' hθ hν)

end Stacks.Algebraization

end
