module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedAffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaGoodBaseChange.StalkOfPullbackEta
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafReductionStalk
public import StacksFrontier.Homology.Eta.Perfect.GoodBaseChangeRingInputs

/-!
# The chain-level stalk bridge: the stalk of the pullback comparison *is* the ring-level one

Let `f : X ⟶ Y` be a morphism of ringed spaces, `x` a point of `X`, `ι : I ⟶ 𝒪_Y` an invertible
ideal subsheaf, and `F^•` a complex of `I`-torsion-free `𝒪_Y`-modules whose termwise pullback is
`f^*I`-torsion-free.  Let `a` generate the stalk ideal `I_{f x}` and let its germ `b` generate
`(f^*I)_x`.

`StacksFrontier/AlgebraicGeometry/Divisors/EtaGoodBaseChange/StalkOfPullbackEta.lean` computes the
stalk of the comparison `f^*(η_I F^•) ⟶ η_{f^*I}(f^*F^•)` *degreewise and after composing with
the inclusion of the décalage term into the localization*, and deduces from that computation that
the comparison is an isomorphism as soon as the ring-level comparison of Tag 0F7X is bijective at
every stalk.  **This file upgrades that computation to an identification of maps of complexes**:
the stalk of `Stacks.IdealTorsion.Eta.pullbackEtaMap` is, up to two isomorphisms of complexes of
`𝒪_{X,x}`-modules, the ring-level base-change comparison
`Stacks.Eta.GoodBaseChange.etaBaseChangeMap` for the germ map `𝒪_{Y,f(x)} → 𝒪_{X,x}`, the
generator `a` and the stalk complex `F^•_{f(x)}`.

That is strictly stronger than the bijectivity criterion, and it is what the goodness form of
Tag 0F9X needs.  Bijectivity of the *degreewise* ring-level comparison is only available at a
bounded complex of finite free modules with principal determinantal ideals, and a stalk complex
is such a complex only up to a **derived** isomorphism, across which degreewise bijectivity does
not transport.  What does transport is quasi-isomorphy, and the ring-level goodness form of
Tag 0F7X, `Stacks.Eta.GoodBaseChange.quasiIso_baseChangeMap_comp_etaBaseChangeMap_of_kFlat`,
delivers exactly that.  The identification below converts it into quasi-isomorphy of the stalk of
`pullbackEtaMap`, and quasi-isomorphy of a map of complexes of sheaves of modules is stalk-local
(Tag 08TL); no flatness of `f` is used anywhere in the file.

## Main definitions

* `Stacks.IdealTorsion.Eta.stalkPullbackComplexIso`: **Stacks tag 0098 on complexes** — the
  degreewise stalk at `x` of the pullback of a complex is the base change along the germ map of
  its degreewise stalk at `f x`.
* `Stacks.IdealTorsion.Eta.stalkPullbackEtaSourceIso`: the stalk of `f^*(η_I F^•)` is the base
  change of `η_a(F^•_{f(x)})`; Tag 0098 followed by the base change of Tag 0GT6 on `Y`.
* `Stacks.IdealTorsion.Eta.stalkPullbackEtaTargetIso`: the stalk of `η_{f^*I}(f^*F^•)` is `η_b`
  of the base change of `F^•_{f(x)}`; Tag 0GT6 on `X` followed by `η_b` of Tag 0098.

## Main results

* `Stacks.IdealTorsion.Eta.stalkPullbackEtaBridge_f`: **the bridge, degreewise.**
* `Stacks.IdealTorsion.Eta.stalkComplex_map_pullbackEtaMap_eq`: **the bridge** — the stalk of the
  comparison of décalages, conjugated by the two isomorphisms above, is
  `Stacks.Eta.GoodBaseChange.etaBaseChangeMap`.
* `Stacks.IdealTorsion.Eta.quasiIso_stalkComplex_map_pullbackEtaMap`: the stalk of the comparison
  is a quasi-isomorphism as soon as the ring-level comparison at that stalk is one.
* `Stacks.IdealTorsion.Eta.quasiIso_pullbackEtaMap_of_forall_stalk`: **the comparison of
  décalages `f^*(η_I F^•) ⟶ η_{f^*I}(f^*F^•)` is a quasi-isomorphism as soon as the ring-level
  base-change comparison of the décalage is a quasi-isomorphism at every stalk**, with no
  flatness hypothesis.
* `Stacks.IdealTorsion.Eta.stalkComplex_map_comp_pullbackEtaMap_eq` and
  `Stacks.IdealTorsion.Eta.quasiIso_comp_pullbackEtaMap_of_forall_stalk`: the same at a
  presentation `p : P^• ⟶ η_I F^•`, which is the form Stacks tag 0F9X consumes — the hypothesis
  there is literally the conclusion of
  `Stacks.Eta.GoodBaseChange.quasiIso_baseChangeMap_comp_etaBaseChangeMap_of_kFlat` at each
  stalk, and the conclusion is (up to the transport along `f^*ℐ_D ≅ ℐ_E`) the hypothesis `hΨ` of
  `Stacks.Divisors.Eta.nonempty_derivedPullback_derivedEta_iso_of_quasiIso`.

## Implementation notes

The degreewise bridge is `Stacks.IdealTorsion.Eta.stalkOfPullbackEtaTermMap_factor` with the
inclusion of the décalage term cancelled.  Cancelling it is possible because the three remaining
discrepancies compose away: `Stacks.IdealTorsion.Eta.etaBaseChangeMap_f_comp_subtype` — which is
`Stacks.IdealTorsion.Eta.stalkPsiMap_comp_eq` read as an equality of morphisms — identifies the
middle factor of that factorization with the degreewise comparison followed by the inclusion,
`Stacks.IdealTorsion.Eta.etaMap_f_comp_subtype` moves the inclusion across the décalage of a map
of complexes, and the localizations of Tag 0098 and of its inverse are mutually inverse
(`Stacks.IdealTorsion.Eta.stalkLocBaseChangeInv_comp_fLoc`).  All of the bookkeeping is isolated
in the diagram lemma `Stacks.IdealTorsion.Eta.cancel_bridge`, which takes the factorization in
exactly the shape it is proved in and is stated in an arbitrary category, so that rearranging the
composites performs no unification and no instance search in `ModuleCat`; for the same reason its
monomorphism hypothesis is an explicit argument rather than an instance.  This matters: the
composites in question are type-correct only at default transparency, so a `rw` applied to them
directly reports that it cannot find its pattern.

Two spellings of base change meet here: Mathlib's `ModuleCat.extendScalars` along the germ map,
which is what Tag 0098 is stated with, and `Stacks.Eta.GoodBaseChange.baseChangeComplex` for the
algebra structure that germ map defines, which is what the ring-level décalage files are stated
with.  They are definitionally equal — `Stacks.extendScalars_eq_algebraBaseChange_toAlgebra` says
the two functors are literally the same — but not syntactically, and the difference is *not*
pushed down into the décalage terms: every statement below that mentions a décalage term of a
base change writes that base change as `baseChangeComplex`, which is the spelling in which
`EtaComplex.term` unfolds to the `EtaPow.fetaTerm` of a `LinearMap.baseChange`.  Spelling it the
other way instead makes the comparison of the two décalage terms a definitional check that
exhausts the elaborator.  As in
`StacksFrontier/AlgebraicGeometry/Divisors/EtaGoodBaseChange/StalkOfPullbackEta.lean`, every
remaining step is a ground equation closed by `exact`, `Eq.trans` or `congrArg`, and each factor
of the argument is a declaration of its own.

## References

* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0F7X](https://stacks.math.columbia.edu/tag/0F7X)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor commStalkGermMap commStalkBaseChange
  stalkPullbackBaseChangeIso stalkPullbackBaseChangeIso_naturality)

open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

open Stacks.IdealTorsion.Reduction (stalkComplexFunctor)

open scoped TensorProduct

universe u

namespace Stacks.IdealTorsion.Eta

/-! ### Two lemmas with no sheaves in them -/

/-- **The diagram lemma behind the bridge.**  Suppose `s₂` is a monomorphism, that `g` and `l`
are mutually inverse in the order `l ≫ g = 𝟙`, that `m` carries `s₁` to `s₂` through `g`, that
`q ≫ s₂` is `W ≫ p`, and that `P ≫ E ≫ s₁` is `S ≫ V ≫ W ≫ p ≫ l`.  Then
`P ≫ E ≫ m = (S ≫ V) ≫ q`.

This is the shape of the degreewise bridge.  `P ≫ E ≫ s₁ = S ≫ V ≫ W ≫ p ≫ l` is the
factorization `Stacks.IdealTorsion.Eta.stalkOfPullbackEtaTermMap_factor` verbatim: `P` is the
stalk of the comparison of décalages, `E` the comparison of Tag 0GT6 on `X`, `s₁` and `s₂` the
inclusions of the two décalage terms into their localizations, `S` the comparison of Tag 0098,
`V` the base change of Tag 0GT6 on `Y`, `W ≫ p` the base-changed inclusion followed by the
comparison of Tag 0F7X, `l` the localization of the inverse of Tag 0098 and `g` that of Tag 0098
itself; `m` is `η_b` of Tag 0098 and `q` the degreewise ring-level comparison.

It is stated in an arbitrary category, with the monomorphism hypothesis an explicit argument, so
that rearranging the composites performs no unification and no instance search in `ModuleCat`;
the composites occurring in the application are type-correct only at default transparency, so a
`rw` performed on them directly reports that it cannot find its pattern. -/
theorem cancel_bridge {C : Type*} [Category C] {A₀ A₁ A₂ A₃ T₁ T₂ S₀ S₁ S₂ : C}
    (P : A₀ ⟶ A₁) (E : A₁ ⟶ A₂) (m : A₂ ⟶ A₃) (s₁ : A₂ ⟶ T₁) (s₂ : A₃ ⟶ T₂)
    (g : T₁ ⟶ T₂) (l : T₂ ⟶ T₁) (S : A₀ ⟶ S₀) (V : S₀ ⟶ S₁) (W : S₁ ⟶ S₂) (p : S₂ ⟶ T₂)
    (q : S₁ ⟶ A₃)
    (h₁ : P ≫ E ≫ s₁ = S ≫ V ≫ W ≫ p ≫ l) (h₄ : q ≫ s₂ = W ≫ p)
    (h₂ : m ≫ s₂ = s₁ ≫ g) (h₃ : l ≫ g = 𝟙 T₂) (hmono : Mono s₂) :
    P ≫ E ≫ m = (S ≫ V) ≫ q := by
  have := hmono
  apply (cancel_mono s₂).mp
  simpa [h₂, h₃, h₄] using h₁ =≫ g

/-- **The diagram lemma behind the bridge at a presentation.**  Granted the bridge
`v ≫ t = S₁ ≫ z`, the naturality square `u ≫ c₁ = e ≫ d`, the decomposition `S₁ = c₁ ≫ k` of
the bridge's left isomorphism and the composition law `d ≫ k = r`, a composite `U = u ≫ v` is
carried by `t` onto `e ≫ r ≫ z`.

Here `u` is the stalk of the pullback of a quasi-isomorphism `p : P ⟶ η_I F^•`, `v` the stalk of
the comparison of décalages, `t` and `e` the two comparison isomorphisms, `c₁ ≫ k` the
factorization of the left one through Tag 0098 on complexes, `d` the base change of the stalk of
`p`, `r` the base change of its composite with Tag 0GT6 and `z` the ring-level comparison.
Stated in an arbitrary category for the reason given in
`Stacks.IdealTorsion.Eta.cancel_bridge`. -/
theorem bridge_comp {C : Type*} [Category C] {A₀ A₁ A₂ A₃ B₀ B₀' B₁ : C}
    (U : A₀ ⟶ A₂) (u : A₀ ⟶ A₁) (v : A₁ ⟶ A₂) (t : A₂ ⟶ A₃) (S₁ : A₁ ⟶ B₁) (z : B₁ ⟶ A₃)
    (e : A₀ ⟶ B₀) (c₁ : A₁ ⟶ B₀') (d : B₀ ⟶ B₀') (k : B₀' ⟶ B₁) (r : B₀ ⟶ B₁)
    (hU : U = u ≫ v) (hbridge : v ≫ t = S₁ ≫ z) (hnat : u ≫ c₁ = e ≫ d) (hS : S₁ = c₁ ≫ k)
    (hr : d ≫ k = r) :
    U ≫ t = e ≫ r ≫ z := by
  subst hU hS hr
  simp only [Category.assoc] at hbridge ⊢
  rw [hbridge, reassoc_of% hnat]

/-- **The inclusion of the décalage term moves across the décalage of a map of complexes**: in
degree `n`, `η_r g` followed by the inclusion of the degree-`n` term of `η_r D` is the inclusion
of the degree-`n` term of `η_r C` followed by the localization of `g^n`.  Both sides are the
localization of `g^n` read on the décalage term, so the equality holds pointwise by
`EtaComplex.etaMapLinear_val`. -/
theorem etaMap_f_comp_subtype {R : Type u} [CommRing R] (r : R)
    {C D : EtaComplex.Complex.{u, u} R} (g : C ⟶ D) (n : ℤ) :
    (EtaComplex.etaMap r g).f n ≫ ModuleCat.ofHom (EtaComplex.term r D n).subtype =
      ModuleCat.ofHom (EtaComplex.term r C n).subtype ≫
        ModuleCat.ofHom (EtaPow.fLoc r (g.f n).hom) :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-! ### Stacks tag 0098 on complexes -/

noncomputable section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y) (x : X)

/-- **Stacks tag 0098 on complexes, at the spelling of the décalage files.**  The degreewise
stalk at `x` of the pullback of a complex of `𝒪_Y`-modules is the base change along the germ map
`𝒪_{Y,f(x)} → 𝒪_{X,x}` of its degreewise stalk at `f x`.

Degreewise this is `Stacks.RingedSpace.stalkPullbackBaseChangeIso`, and the commutation with the
differentials is its naturality. -/
def stalkPullbackComplexIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ) :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (commStalkGermMap f x).toAlgebra
    stalkComplex X x (pullbackComplex f K) ≅
      Stacks.Eta.GoodBaseChange.baseChangeComplex (B := ringStalk X x)
        (stalkComplex Y (f.hom.base x) K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (stalkPullbackBaseChangeIso f x).app (K.X n))
    (fun i j _ => ((stalkPullbackBaseChangeIso f x).hom.naturality (K.d i j)).symm)

/-- Degreewise, Tag 0098 on complexes is Tag 0098. -/
theorem stalkPullbackComplexIso_hom_f
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) :
    (stalkPullbackComplexIso f x K).hom.f n =
      (stalkPullbackBaseChangeIso f x).hom.app (K.X n) := rfl

/-- **Tag 0098 on complexes is natural in the complex.**  Degreewise this is
`Stacks.RingedSpace.stalkPullbackBaseChangeIso_naturality`. -/
theorem stalkPullbackComplexIso_natural
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (φ : K ⟶ L) :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (commStalkGermMap f x).toAlgebra
    (stalkComplexFunctor X x).map
          (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ≫
        (stalkPullbackComplexIso f x L).hom =
      (stalkPullbackComplexIso f x K).hom ≫
        Stacks.Eta.GoodBaseChange.baseChangeMap (B := ringStalk X x)
          ((stalkComplexFunctor Y (f.hom.base x)).map φ) :=
  HomologicalComplex.hom_ext _ _ fun n =>
    stalkPullbackBaseChangeIso_naturality f x (φ.f n)

/-- **The localizations of Tag 0098 and of its inverse are mutually inverse.**  The localization
at `b` of the inverse comparison, which is
`Stacks.IdealTorsion.Eta.stalkLocBaseChangeInv`, followed by the localization at `b` of the
comparison itself, is the identity. -/
theorem stalkLocBaseChangeInv_comp_fLoc
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (a : ringStalk Y (f.hom.base x)) :
    stalkLocBaseChangeInv f x M a ≫
        ModuleCat.ofHom (EtaPow.fLoc (commStalkGermMap f x a)
          ((stalkPullbackBaseChangeIso f x).hom.app M).hom) =
      𝟙 (stalkLocBaseChange f x M a) := by
  have hid : ((stalkPullbackBaseChangeIso f x).hom.app M).hom.comp
      ((stalkPullbackBaseChangeIso f x).inv.app M).hom = LinearMap.id :=
    (ModuleCat.hom_comp _ _).symm.trans (congrArg ModuleCat.Hom.hom
      (Iso.inv_hom_id_app (stalkPullbackBaseChangeIso f x) M))
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  change EtaPow.fLoc (commStalkGermMap f x a)
      ((stalkPullbackBaseChangeIso f x).hom.app M).hom
      (EtaPow.fLoc (commStalkGermMap f x a)
        ((stalkPullbackBaseChangeIso f x).inv.app M).hom z) = z
  rw [EtaComplex.localizedMap_comp_apply, hid, EtaComplex.localizedMap_id_apply]

/-! ### The two comparison isomorphisms of complexes -/

section Bridge

variable (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Mono ι]
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
  (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
  (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
  (a : ringStalk Y (f.hom.base x)) (ha : GeneratesStalkIdeal Y ι (f.hom.base x) a)
  (hb : GeneratesStalkIdeal X (pullbackIdealIncl f I ι) x (commStalkGermMap f x a))

/-- **The stalk of `f^*(η_I F^•)` is the base change of `η_a(F^•_{f(x)})`.**  Tag 0098 on
complexes, followed by the base change along the germ map of the comparison of Tag 0GT6 on
`Y`. -/
def stalkPullbackEtaSourceIso :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (commStalkGermMap f x).toAlgebra
    stalkComplex X x (pullbackComplex f (etaObj Y I ι F hF)) ≅
      Stacks.Eta.GoodBaseChange.baseChangeComplex (B := ringStalk X x)
        (EtaComplex.etaObject a (stalkComplex Y (f.hom.base x) F)) :=
  stalkPullbackComplexIso f x (etaObj Y I ι F hF) ≪≫
    ((commStalkBaseChange f x).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (etaStalkIso Y I ι F hF (f.hom.base x) a ha)

/-- **The stalk of `η_{f^*I}(f^*F^•)` is `η_b` of the base change of `F^•_{f(x)}`.**  The
comparison of Tag 0GT6 on `X` at the germ `b` of the generator, followed by `η_b` of Tag 0098 on
complexes. -/
def stalkPullbackEtaTargetIso :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (commStalkGermMap f x).toAlgebra
    stalkComplex X x (etaObj X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
        (pullbackComplex f F) hF') ≅
      EtaComplex.etaObject (commStalkGermMap f x a)
        (Stacks.Eta.GoodBaseChange.baseChangeComplex (B := ringStalk X x)
          (stalkComplex Y (f.hom.base x) F)) :=
  etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) (pullbackComplex f F) hF'
      x (commStalkGermMap f x a) hb ≪≫
    (Stacks.Eta.DerivedFunctor.etaObjectFunctor (commStalkGermMap f x a)).mapIso
      (stalkPullbackComplexIso f x F)

/-! ### The middle factor of the factorization is the ring-level comparison -/

/-- **The degreewise ring-level comparison followed by the inclusion of the décalage term is the
middle factor of `Stacks.IdealTorsion.Eta.stalkOfPullbackEtaTermMap_factor`.**  This is
`Stacks.IdealTorsion.Eta.stalkPsiMap_comp_eq` read as an equality of morphisms of
`𝒪_{X,x}`-modules rather than of linear maps. -/
theorem etaBaseChangeMap_f_comp_subtype (n : ℤ) :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (commStalkGermMap f x).toAlgebra
    (Stacks.Eta.GoodBaseChange.etaBaseChangeMap (B := ringStalk X x) a
            (stalkComplex Y (f.hom.base x) F)).f n ≫
          ModuleCat.ofHom (EtaComplex.term (commStalkGermMap f x a)
            (Stacks.Eta.GoodBaseChange.baseChangeComplex (B := ringStalk X x)
              (stalkComplex Y (f.hom.base x) F)) n).subtype =
      (commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
          (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))) ≫
        stalkPsiMap f x (F.X n) a :=
  ModuleCat.hom_ext ((ModuleCat.hom_comp _ _).trans (stalkPsiMap_comp_eq f x F a n).symm)

/-! ### The bridge -/

include hF hF' ha hb in
/-- **The bridge, degreewise.**  In degree `n`, the stalk at `x` of the comparison of décalages,
followed by the comparison isomorphism `Stacks.IdealTorsion.Eta.stalkPullbackEtaTargetIso`, is
the comparison isomorphism `Stacks.IdealTorsion.Eta.stalkPullbackEtaSourceIso` followed by the
degreewise ring-level base-change comparison of the décalage.

No flatness is assumed: the input is
`Stacks.IdealTorsion.Eta.stalkOfPullbackEtaTermMap_factor`, which assumes none. -/
theorem stalkPullbackEtaBridge_f (n : ℤ) :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (commStalkGermMap f x).toAlgebra
    ((stalkComplexFunctor X x).map (pullbackEtaMap f I ι F hF hF')).f n ≫
        (stalkPullbackEtaTargetIso f x I ι F hF' a hb).hom.f n =
      (stalkPullbackEtaSourceIso f x I ι F hF a ha).hom.f n ≫
        (Stacks.Eta.GoodBaseChange.etaBaseChangeMap (B := ringStalk X x) a
          (stalkComplex Y (f.hom.base x) F)).f n :=
  cancel_bridge _ _ _ _ _ _ _ _ _ _ _ _
    (stalkOfPullbackEtaTermMap_factor f x I ι F hF hF' a ha hb n)
    (etaBaseChangeMap_f_comp_subtype f x F a n)
    (etaMap_f_comp_subtype (commStalkGermMap f x a) (stalkPullbackComplexIso f x F).hom n)
    (stalkLocBaseChangeInv_comp_fLoc f x (F.X n) a)
    ((ModuleCat.mono_iff_injective _).mpr Subtype.val_injective)

include hF hF' ha hb in
/-- **The chain-level stalk bridge.**  The stalk at `x` of the comparison of décalages
`f^*(η_I F^•) ⟶ η_{f^*I}(f^*F^•)`, conjugated by the two comparison isomorphisms of complexes
`Stacks.IdealTorsion.Eta.stalkPullbackEtaSourceIso` and
`Stacks.IdealTorsion.Eta.stalkPullbackEtaTargetIso`, **is the ring-level base-change comparison
of the décalage** `Stacks.Eta.GoodBaseChange.etaBaseChangeMap` for the germ map
`𝒪_{Y,f(x)} → 𝒪_{X,x}`, the generator `a` of the stalk ideal and the stalk complex of `F^•` at
`f x`.

Degreewise this is `Stacks.IdealTorsion.Eta.stalkPullbackEtaBridge_f`.  No flatness is
assumed. -/
theorem stalkComplex_map_pullbackEtaMap_eq :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (commStalkGermMap f x).toAlgebra
    (stalkComplexFunctor X x).map (pullbackEtaMap f I ι F hF hF') ≫
        (stalkPullbackEtaTargetIso f x I ι F hF' a hb).hom =
      (stalkPullbackEtaSourceIso f x I ι F hF a ha).hom ≫
        Stacks.Eta.GoodBaseChange.etaBaseChangeMap (B := ringStalk X x) a
          (stalkComplex Y (f.hom.base x) F) :=
  HomologicalComplex.hom_ext _ _ fun n =>
    stalkPullbackEtaBridge_f f x I ι F hF hF' a ha hb n

/-! ### Quasi-isomorphy -/

include hF hF' ha hb in
/-- **The stalk of the comparison of décalages is a quasi-isomorphism as soon as the ring-level
base-change comparison of the décalage at that stalk is one.**  By the bridge the first is the
second conjugated by two isomorphisms of complexes. -/
theorem quasiIso_stalkComplex_map_pullbackEtaMap
    (hq : letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
        (commStalkGermMap f x).toAlgebra
      QuasiIso (Stacks.Eta.GoodBaseChange.etaBaseChangeMap (B := ringStalk X x) a
        (stalkComplex Y (f.hom.base x) F))) :
    QuasiIso ((stalkComplexFunctor X x).map (pullbackEtaMap f I ι F hF hF')) :=
  (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk' _ _
    (stalkPullbackEtaSourceIso f x I ι F hF a ha)
    (stalkPullbackEtaTargetIso f x I ι F hF' a hb)
    (stalkComplex_map_pullbackEtaMap_eq f x I ι F hF hF' a ha hb).symm)).2 hq

/-! ### The bridge at a presentation of `η_I F^•` -/

include hF hF' ha hb in
/-- **The bridge at a presentation.**  Let `p : P^• ⟶ η_I F^•` be any map of complexes of
`𝒪_Y`-modules.  The stalk at `x` of `f^*p` followed by the comparison of décalages, conjugated by
`Stacks.IdealTorsion.Eta.stalkPullbackComplexIso` at `P^•` and by
`Stacks.IdealTorsion.Eta.stalkPullbackEtaTargetIso`, is

`𝒪_{X,x} ⊗ (P^•_{f(x)} ⟶ η_a F^•_{f(x)}) ⟶ η_b (𝒪_{X,x} ⊗ F^•_{f(x)})`,

the composite whose quasi-isomorphy is the conclusion of the goodness form of Tag 0F7X at the
ring level, `Stacks.Eta.GoodBaseChange.quasiIso_baseChangeMap_comp_etaBaseChangeMap_of_kFlat`.

The three inputs are the bridge `Stacks.IdealTorsion.Eta.stalkComplex_map_pullbackEtaMap_eq`, the
naturality `Stacks.IdealTorsion.Eta.stalkPullbackComplexIso_natural` of Tag 0098 on complexes,
and the composition law of base change; they are assembled by
`Stacks.IdealTorsion.Eta.bridge_comp`. -/
theorem stalkComplex_map_comp_pullbackEtaMap_eq
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (p : P ⟶ etaObj Y I ι F hF) :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (commStalkGermMap f x).toAlgebra
    (stalkComplexFunctor X x).map
          (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map p ≫
            pullbackEtaMap f I ι F hF hF') ≫
        (stalkPullbackEtaTargetIso f x I ι F hF' a hb).hom =
      (stalkPullbackComplexIso f x P).hom ≫
        Stacks.Eta.GoodBaseChange.baseChangeMap (B := ringStalk X x)
            ((stalkComplexFunctor Y (f.hom.base x)).map p ≫
              (etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom) ≫
          Stacks.Eta.GoodBaseChange.etaBaseChangeMap (B := ringStalk X x) a
            (stalkComplex Y (f.hom.base x) F) :=
  bridge_comp _ _ _ _ _ _ _ _ _ _ _
    ((stalkComplexFunctor X x).map_comp _ _)
    (stalkComplex_map_pullbackEtaMap_eq f x I ι F hF hF' a ha hb)
    (stalkPullbackComplexIso_natural f x p) rfl
    ((((commStalkBaseChange f x).mapHomologicalComplex (ComplexShape.up ℤ)).map_comp
      ((stalkComplexFunctor Y (f.hom.base x)).map p)
      ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom)).symm)

include hF hF' ha hb in
/-- **The stalk of the comparison of décalages at a presentation is a quasi-isomorphism as soon
as the ring-level composite of the goodness form of Tag 0F7X is one at that stalk.** -/
theorem quasiIso_stalkComplex_map_comp_pullbackEtaMap
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (p : P ⟶ etaObj Y I ι F hF)
    (hq : letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
        (commStalkGermMap f x).toAlgebra
      QuasiIso (Stacks.Eta.GoodBaseChange.baseChangeMap (B := ringStalk X x)
          ((stalkComplexFunctor Y (f.hom.base x)).map p ≫
            (etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom) ≫
        Stacks.Eta.GoodBaseChange.etaBaseChangeMap (B := ringStalk X x) a
          (stalkComplex Y (f.hom.base x) F))) :
    QuasiIso ((stalkComplexFunctor X x).map
      (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map p ≫
        pullbackEtaMap f I ι F hF hF')) :=
  (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk' _ _
    (stalkPullbackComplexIso f x P)
    (stalkPullbackEtaTargetIso f x I ι F hF' a hb)
    (stalkComplex_map_comp_pullbackEtaMap_eq f x I ι F hF hF' a ha hb P p).symm)).2 hq

end Bridge

/-! ### The criterion: goodness in place of flatness, for quasi-isomorphy -/

section Criterion

variable (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Mono ι]
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
  (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
  (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))

include hF hF' in
/-- **The comparison of décalages under a pullback is a quasi-isomorphism as soon as the
ring-level base-change comparison of the décalage is a quasi-isomorphism at every stalk**:
`f^*(η_I F^•) ⟶ η_{f^*I}(f^*F^•)` with **no flatness hypothesis on `f`**.

Concretely the hypothesis asks that at every point `x` of `X` there be a generator `a` of the
stalk ideal `I_{f(x)}` whose germ generates `(f^*I)_x`, and for which the ring-level comparison

`𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} (η_a F^•_{f(x)}) ⟶ η_b (𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} F^•_{f(x)})`

of `Stacks.Eta.GoodBaseChange.etaBaseChangeMap` is a quasi-isomorphism.  That is the conclusion
of the goodness form of Tag 0F7X; unlike its degreewise bijectivity form
`Stacks.Eta.GoodBaseChange.bijective_psiTermMap_mulVecLin`, which is the hypothesis of
`Stacks.IdealTorsion.Eta.isIso_pullbackEtaMap_of_forall_stalk`, it transports across a *derived*
isomorphism of the stalk complex with a bounded complex of finite free modules whose
determinantal ideals are principal — see
`Stacks.Eta.GoodBaseChange.quasiIso_baseChangeMap_comp_etaBaseChangeMap_of_kFlat`.

The proof is `Stacks.IdealTorsion.Eta.quasiIso_stalkComplex_map_pullbackEtaMap` at each point,
together with the stalk-locality of quasi-isomorphy (Tag 08TL,
`AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso`) read over the commutative
stalk ring by
`Stacks.IdealTorsion.Reduction.quasiIso_stalkFunctor_map_of_stalkComplexFunctor_map`. -/
theorem quasiIso_pullbackEtaMap_of_forall_stalk
    (h : ∀ z : X, ∃ (a : ringStalk Y (f.hom.base z))
        (_ : GeneratesStalkIdeal Y ι (f.hom.base z) a)
        (_ : GeneratesStalkIdeal X (pullbackIdealIncl f I ι) z (commStalkGermMap f z a)),
        letI : Algebra (ringStalk Y (f.hom.base z)) (ringStalk X z) :=
          (commStalkGermMap f z).toAlgebra
        QuasiIso (Stacks.Eta.GoodBaseChange.etaBaseChangeMap (B := ringStalk X z) a
          (stalkComplex Y (f.hom.base z) F))) :
    QuasiIso (pullbackEtaMap f I ι F hF hF') := by
  refine AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso _ _ fun z => ?_
  obtain ⟨a, ha, hb, hq⟩ := h z
  exact Stacks.IdealTorsion.Reduction.quasiIso_stalkFunctor_map_of_stalkComplexFunctor_map X z _
    (quasiIso_stalkComplex_map_pullbackEtaMap f z I ι F hF hF' a ha hb hq)

include hF hF' in
/-- **The criterion in the form Stacks tag 0F9X consumes.**  Let `p : P^• ⟶ η_I F^•` be a map of
complexes of `𝒪_Y`-modules.  Then

`f^*P^• ⟶ f^*(η_I F^•) ⟶ η_{f^*I}(f^*F^•)`

is a quasi-isomorphism as soon as, at every point `x` of `X`, there is a generator `a` of the
stalk ideal `I_{f(x)}` whose germ generates `(f^*I)_x` and for which the ring-level composite

`𝒪_{X,x} ⊗ P^•_{f(x)} ⟶ 𝒪_{X,x} ⊗ (η_a F^•_{f(x)}) ⟶ η_b (𝒪_{X,x} ⊗ F^•_{f(x)})`

is a quasi-isomorphism.  **There is no flatness hypothesis on `f`.**

That hypothesis is exactly the conclusion of the goodness form of Tag 0F7X at the ring level,
`Stacks.Eta.GoodBaseChange.quasiIso_baseChangeMap_comp_etaBaseChangeMap_of_kFlat`, taken at the
K-flat complex `P^•_{f(x)}` and the quasi-isomorphism obtained from `p` by taking stalks and
composing with Tag 0GT6; and the conclusion is, up to the transport along `f^*ℐ_D ≅ ℐ_E` of
`Stacks.IdealTorsion.Eta.IdealCongr.etaIso`, the hypothesis `hΨ` of
`Stacks.Divisors.Eta.nonempty_derivedPullback_derivedEta_iso_of_quasiIso`. -/
theorem quasiIso_comp_pullbackEtaMap_of_forall_stalk
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (p : P ⟶ etaObj Y I ι F hF)
    (h : ∀ z : X, ∃ (a : ringStalk Y (f.hom.base z))
        (ha : GeneratesStalkIdeal Y ι (f.hom.base z) a)
        (_ : GeneratesStalkIdeal X (pullbackIdealIncl f I ι) z (commStalkGermMap f z a)),
        letI : Algebra (ringStalk Y (f.hom.base z)) (ringStalk X z) :=
          (commStalkGermMap f z).toAlgebra
        QuasiIso (Stacks.Eta.GoodBaseChange.baseChangeMap (B := ringStalk X z)
            ((stalkComplexFunctor Y (f.hom.base z)).map p ≫
              (etaStalkIso Y I ι F hF (f.hom.base z) a ha).hom) ≫
          Stacks.Eta.GoodBaseChange.etaBaseChangeMap (B := ringStalk X z) a
            (stalkComplex Y (f.hom.base z) F))) :
    QuasiIso (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map p ≫
      pullbackEtaMap f I ι F hF hF') := by
  refine AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso _ _ fun z => ?_
  obtain ⟨a, ha, hb, hq⟩ := h z
  exact Stacks.IdealTorsion.Reduction.quasiIso_stalkFunctor_map_of_stalkComplexFunctor_map X z _
    (quasiIso_stalkComplex_map_comp_pullbackEtaMap f z I ι F hF hF' a ha hb P p hq)

end Criterion

end

end Stacks.IdealTorsion.Eta

end
