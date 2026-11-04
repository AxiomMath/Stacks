module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiLocal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructibility may be checked Zariski locally on an arbitrary scheme

Tag 095F says that constructibility of a sheaf of sets, of abelian groups, or of modules over a
Noetherian ring on the small étale site of a scheme `X` is a Zariski-local condition: if
`X = ⋃ U_i` is an open covering and the restriction of the sheaf to each `U_i` is constructible,
then the sheaf is constructible. No hypothesis on `X` is needed.

The two ingredients are already available. Restriction to an open subscheme preserves
constructibility, which is the easy half, and an affine open `U` of `X` is quasi-compact and
quasi-separated, so Tag 095E applies to it: covering `U` by the affine opens it has inside the
members of the given covering and restricting the hypothesis there produces a single
stratification of `U`, which is exactly what constructibility on `U` demands. That reduction is
`AlgebraicGeometry.isStratifiedSheaf_of_openCover`, stated for an arbitrary condition on the
strata and taking the two assertions of Tag 095E as hypotheses; this file discharges those
hypotheses with `AlgebraicGeometry.isStratifiedSheaf_tfae` and specializes the result to the three
kinds of coefficients.

## Main results

* `AlgebraicGeometry.isStratifiedSheaf_of_openCover_of_immersionStable` — Zariski descent of
  being a stratified sheaf, for any condition on the strata that is closed under isomorphism of
  sheaves and stable under inverse image along an immersion.
* `AlgebraicGeometry.isConstructibleFiniteSheaf_of_openCover` — **Tag 095F for sheaves of sets
  and of abelian groups.**
* `AlgebraicGeometry.isConstructibleModuleSheaf_of_openCover` — **Tag 095F for sheaves of modules
  over a Noetherian ring.**
* `AlgebraicGeometry.isConstructibleFiniteSheaf_iff_forall_restrict` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_iff_forall_restrict` — the same statements as
  equivalences, the converse direction being restriction to an open subscheme.

## Implementation notes

Finite local constancy and local constancy of finite type are stable under inverse image along an
*arbitrary* morphism of the big étale site, by
`AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback'` and
`AlgebraicGeometry.isFiniteTypeLocallyConstant_smallEtaleSheafPullback`, so the hypothesis that
the morphism is an immersion is simply discarded when the general statement is specialized. This
keeps the coefficient hypotheses to those of Tag 03RW: inverse image exists for base change
between objects of the big étale site, and the localized sites admit weak sheafification.

The index type of the covering is in an arbitrary universe, and the covering is recorded by open
immersions in the big étale site whose images cover the underlying space, as elsewhere in this
directory.

## References

* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w v t r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

section General

variable {D : Type w} [Category.{v} D]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **Zariski descent for stratified sheaves, for an arbitrary condition on the strata.** If a
sheaf on `X` restricts to a stratified sheaf on each member of a Zariski open covering of `X`,
then it is a stratified sheaf, provided the condition on the strata is closed under isomorphism of
sheaves and stable under inverse image along an immersion.

The two inputs of `AlgebraicGeometry.isStratifiedSheaf_of_openCover` are the assertions of
Tag 095E on a quasi-compact quasi-separated scheme, and both are read off
`AlgebraicGeometry.isStratifiedSheaf_tfae`. -/
public theorem isStratifiedSheaf_of_openCover_of_immersionStable (X : B.Scheme)
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPImmersion : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) D, P T G →
        P T' (((smallEtaleBaseChange B g).sheafPullback D
          (SmallEtale.topology B T.obj T.property)
          (SmallEtale.topology B T'.obj T'.property)).obj G))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    {I : Type*} (U : I → B.Scheme) (j : ∀ k, U k ⟶ X)
    (hj : ∀ k, IsOpenImmersion (B.inclusion.map (j k)))
    (hcover : Set.univ = ⋃ k, Set.range (B.inclusion.map (j k)).base)
    (hlocal : ∀ k, IsStratifiedSheaf B (U k) P
      (((smallEtaleBaseChange B (j k)).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (U k).obj (U k).property)).obj F)) :
    IsStratifiedSheaf B X P F := by
  refine isStratifiedSheaf_of_openCover B X P hPIso ?_ ?_ F U j hj hcover hlocal
  · intro Z _ _ G
    exact (isStratifiedSheaf_tfae B P hPIso hPImmersion Z G).out 1 2
  · intro Z _ _ G
    exact ((isStratifiedSheaf_tfae B P hPIso hPImmersion Z G).out 1 3).mp

end General

section Finite

variable {D : Type w} [Category.{v} D] {FD : D → D → Type*} {CD : D → Type t}
  [∀ A A', FunLike (FD A A') (CD A) (CD A')] [ConcreteCategory.{t} D FD]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) D]

/-- **Stacks 095F for sheaves of sets and of abelian groups.** Let `X` be a scheme covered by the
images of open immersions `U k ⟶ X`. A sheaf with values in a concrete category whose restriction
to every `U k` is constructible is constructible. -/
@[stacks 095F "sets and abelian groups"]
public theorem isConstructibleFiniteSheaf_of_openCover (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    {I : Type*} (U : I → B.Scheme) (j : ∀ k, U k ⟶ X)
    (hj : ∀ k, IsOpenImmersion (B.inclusion.map (j k)))
    (hcover : Set.univ = ⋃ k, Set.range (B.inclusion.map (j k)).base)
    (hlocal : ∀ k, IsConstructibleFiniteSheaf B (U k)
      (((smallEtaleBaseChange B (j k)).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (U k).obj (U k).property)).obj F)) :
    IsConstructibleFiniteSheaf B X F := by
  have hPIso : ∀ (T : B.Scheme)
      {F G : Sheaf (SmallEtale.topology B T.obj T.property) D}, (F ≅ G) →
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T.obj T.property) F →
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T.obj T.property) G := by
    intro T F G e h
    exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) e (hF := h)
  have hPImmersion : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) D,
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T.obj T.property) G →
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
        (SmallEtale.topology B T'.obj T'.property)
        (((smallEtaleBaseChange B g).sheafPullback D
          (SmallEtale.topology B T.obj T.property)
          (SmallEtale.topology B T'.obj T'.property)).obj G) := by
    intro T T' g _ G h
    exact isFiniteLocallyConstant_smallEtaleSheafPullback' B D g G (hH := h)
  exact isStratifiedSheaf_of_openCover_of_immersionStable B X _ hPIso hPImmersion F U j hj
    hcover hlocal

/-- **Constructibility of a sheaf of sets or of abelian groups is Zariski local.** Given an open
covering of `X`, a sheaf with values in a concrete category is constructible exactly when its
restriction to every member of the covering is.

The direction not proved by `AlgebraicGeometry.isConstructibleFiniteSheaf_of_openCover` is
restriction of a constructible sheaf to an open subscheme, which needs no covering hypothesis. -/
@[sga "4 IX 2.4" "(ii)"]
public theorem isConstructibleFiniteSheaf_iff_forall_restrict (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    {I : Type*} (U : I → B.Scheme) (j : ∀ k, U k ⟶ X)
    (hj : ∀ k, IsOpenImmersion (B.inclusion.map (j k)))
    (hcover : Set.univ = ⋃ k, Set.range (B.inclusion.map (j k)).base) :
    IsConstructibleFiniteSheaf B X F ↔
      ∀ k, IsConstructibleFiniteSheaf B (U k)
        (((smallEtaleBaseChange B (j k)).sheafPullback D
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (U k).obj (U k).property)).obj F) :=
  ⟨fun hF k => isConstructibleFiniteSheaf_pullback_of_isOpenImmersion B (j k) (hj k) F hF,
    fun hlocal => isConstructibleFiniteSheaf_of_openCover B X F U j hj hcover hlocal⟩

end Finite

section Modules

variable (R : Type r) [CommRing R] [IsNoetherianRing R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]

omit [IsNoetherianRing R] in
/-- **Stacks 095F for sheaves of modules over a Noetherian ring.** Let `X` be a scheme covered by
the images of open immersions `U k ⟶ X`. A sheaf of modules over a Noetherian ring whose
restriction to every `U k` is constructible is constructible. -/
@[stacks 095F "modules over a Noetherian ring"]
public theorem isConstructibleModuleSheaf_of_openCover (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R))
    {I : Type*} (U : I → B.Scheme) (j : ∀ k, U k ⟶ X)
    (hj : ∀ k, IsOpenImmersion (B.inclusion.map (j k)))
    (hcover : Set.univ = ⋃ k, Set.range (B.inclusion.map (j k)).base)
    (hlocal : ∀ k, IsConstructibleModuleSheaf B (U k) R
      (((smallEtaleBaseChange B (j k)).sheafPullback (ModuleCat.{w} R)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (U k).obj (U k).property)).obj F)) :
    IsConstructibleModuleSheaf B X R F := by
  have hPIso : ∀ (T : B.Scheme)
      {F G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} R)}, (F ≅ G) →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T.obj T.property) F →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T.obj T.property) G := by
    intro T F G e h
    exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) R e h
  have hPImmersion : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} R),
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T.obj T.property) G →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B T'.obj T'.property)
        (((smallEtaleBaseChange B g).sheafPullback (ModuleCat.{w} R)
          (SmallEtale.topology B T.obj T.property)
          (SmallEtale.topology B T'.obj T'.property)).obj G) := by
    intro T T' g _ G h
    exact isFiniteTypeLocallyConstant_smallEtaleSheafPullback B R g G h
  exact isStratifiedSheaf_of_openCover_of_immersionStable B X _ hPIso hPImmersion F U j hj
    hcover hlocal

omit [IsNoetherianRing R] in
/-- **Constructibility of a sheaf of modules over a Noetherian ring is Zariski local.** Given an
open covering of `X`, a sheaf of modules over a Noetherian ring is constructible exactly when its
restriction to every member of the covering is.

The direction not proved by `AlgebraicGeometry.isConstructibleModuleSheaf_of_openCover` is
restriction of a constructible sheaf to an open subscheme, which needs no covering hypothesis. -/
@[sga "4 IX 2.4" "(ii), special case"]
public theorem isConstructibleModuleSheaf_iff_forall_restrict (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R))
    {I : Type*} (U : I → B.Scheme) (j : ∀ k, U k ⟶ X)
    (hj : ∀ k, IsOpenImmersion (B.inclusion.map (j k)))
    (hcover : Set.univ = ⋃ k, Set.range (B.inclusion.map (j k)).base) :
    IsConstructibleModuleSheaf B X R F ↔
      ∀ k, IsConstructibleModuleSheaf B (U k) R
        (((smallEtaleBaseChange B (j k)).sheafPullback (ModuleCat.{w} R)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (U k).obj (U k).property)).obj F) :=
  ⟨fun hF k => isConstructibleModuleSheaf_pullback_of_isOpenImmersion B R (j k) (hj k) F hF,
    fun hlocal => isConstructibleModuleSheaf_of_openCover B R X F U j hj hcover hlocal⟩

end Modules

end AlgebraicGeometry

end
