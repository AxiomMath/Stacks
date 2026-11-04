module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackIdealPowerStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackComplex
public import StacksFrontier.Homology.Eta.BaseChange
public import StacksFrontier.Homology.Eta.Perfect.GoodBaseChange
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# The stalk of the pullback comparison of décalages, and the crux of general Tag 0F9X

Let `f : X ⟶ Y` be a morphism of ringed spaces, `ι : I ⟶ 𝒪_Y` an invertible ideal subsheaf and
`F^•` a complex of `I`-torsion-free `𝒪_Y`-modules whose termwise pullback is `f^*I`-torsion-free.
`Stacks.IdealTorsion.Eta.pullbackEtaTermMap` is the canonical degreewise comparison
`f^*(η_I F^•)^n ⟶ (η_{f^*I}(f^*F^•))^n`, defined with no flatness hypothesis; the only criterion
for it to be an isomorphism that the library had was flatness of `f`
(`Stacks.IdealTorsion.Eta.isIso_pullbackEtaTermMap`).

**This file replaces flatness by the hypothesis that the comparison of Tag 0F7X is bijective at
every stalk**, which is what goodness of the triple supplies.  The route is the one the source
takes: isomorphy of a morphism of sheaves of modules is stalkwise, and at a stalk the comparison
of décalages *is* the ring-level base-change comparison of Tag 0F7X for the germ map
`𝒪_{Y,f(x)} → 𝒪_{X,x}`.  Carrying that out is the content of the file, and no flatness is used
anywhere in it.

## Main results

* `Stacks.IdealTorsion.Eta.isIso_of_forall_stalk_bijective`: isomorphy is stalkwise, at the
  spelling of the décalage files.
* `Stacks.IdealTorsion.Eta.stalkOfPullbackEtaTermMap_ambient`: the sheaf-to-ring bridge — the
  stalk of the comparison, read inside the localization, is the normalized ideal-power
  comparison applied to the pulled-back first projection.
* `Stacks.IdealTorsion.Eta.map_fLoc_fetaTerm`: a décalage term is carried onto a décalage term
  by an isomorphism of the ambient modules compatible with the differentials.
* `Stacks.IdealTorsion.Eta.stalkOfPullbackEtaTermMap_factor`: **the stalk of the comparison,
  factored** as an isomorphism, the ambient form of the ring-level comparison of Tag 0F7X, and
  the localization of the inverse comparison of Tag 0098.
* `Stacks.IdealTorsion.Eta.stalkPsiMap_comp_eq` and
  `Stacks.IdealTorsion.Eta.map_stalkLocBaseChangeInv_fetaTerm`: the two identifications that turn
  that factorization into a statement about `Stacks.Eta.GoodBaseChange.psiTermMap` and the
  décalage term it lands in.
* `Stacks.IdealTorsion.Eta.bijective_stalk_pullbackEtaTermMap`: the stalk of the comparison is
  bijective as soon as `Stacks.Eta.GoodBaseChange.psiTermMap` is.
* `Stacks.IdealTorsion.Eta.isIso_pullbackEtaTermMap_of_forall_stalk` and
  `Stacks.IdealTorsion.Eta.isIso_pullbackEtaMap_of_forall_stalk`: **the crux — the comparison of
  décalages is an isomorphism, degreewise and as a map of complexes, with no flatness
  hypothesis.**

## What this leaves to the consumer

The hypothesis of the two last statements is exactly the conclusion of Tag 0F7X
(`Stacks.Eta.GoodBaseChange.bijective_psiTermMap_mulVecLin`) at every stalk.  Discharging it from
goodness of the triple needs, at each point, the identification of the stalk complex with a
bounded complex of finite free modules having principal determinantal ideals — the model produced
by
`AlgebraicGeometry.ComplexAndDivisorSituation.exists_affineOpen_stalk_goodModel` — together
with the invariance of bijectivity of `Stacks.Eta.GoodBaseChange.psiTermMap` under an
isomorphism of the differential, which is
`Stacks.Eta.GoodBaseChange.etaBaseChangeMap_naturality` in degree `n`.  Neither of those is in
this file; they are joined into the tag in
`StacksFrontier/AlgebraicGeometry/Flatness/BlowUpSquare/GoodTripleEtaPullbackGeneral.lean`.

## Implementation notes

Every step below is a ground equation closed by `Eq.trans` and `congrArg`, or a `rw` with a
hypothesis stated in the exact spelling the goal carries.  The reason is the one recorded in the
implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafPullbackIdealPowerStalk.lean`: the objects
in these composites — `(F ⋙ G).obj N` against `G.obj (F.obj N)`, the carrier of
`ModuleCat.extendScalars` against a plain tensor product, `(η_a F_{f(x)}).X n` against
`ModuleCat.of _ (η_a F_{f(x)})^n` — agree definitionally and not syntactically, so a rewrite
reports that it did not find its pattern while `exact` goes through.  For the same reason the
long bijectivity argument is split into one statement per factor: a single declaration carrying
all of it exceeds the heartbeat limit on the definitional checks alone.

## References

* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0F7X](https://stacks.math.columbia.edu/tag/0F7X)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor commStalkGermMap commStalkBaseChange
  stalkPullbackBaseChangeIso stalkPullbackBaseChangeIso_naturality)

open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

open scoped TensorProduct

universe u

namespace Stacks.IdealTorsion.Eta

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y) (x : X)

/-- The ambient form of the degreewise comparison: the stalk at `x` of
`Stacks.IdealTorsion.Eta.pullbackEtaTermMap`, read inside the localization through the
comparison of Tag 0GT6, is the normalized ideal-power comparison applied to the pulled-back
first projection. -/
theorem stalkOfPullbackEtaTermMap_ambient
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
    [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
      (pullbackIdealIncl f I ι)]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
    (b : ringStalk X x)
    (hb : GeneratesStalkIdeal X (pullbackIdealIncl f I ι) x b) (n : ℤ) :
    (stalkModuleFunctor X x).map (pullbackEtaTermMap f I ι F n) ≫
        (etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
            (pullbackComplex f F) hF' x b hb).hom.f n ≫
          ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term b (stalkComplex X x (pullbackComplex f F)) n)) =
      (stalkModuleFunctor X x).map ((pullbackFunctor f).map (etaFst Y I ι F n)) ≫
        (stalkModuleFunctor X x).map (pullbackIdealPowerIso f I n (F.X n)).hom ≫
          (idealPowerStalkComparison X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
            ((pullbackFunctor f).obj (F.X n)) x b hb).map n := by
  set S := stalkModuleFunctor X x with hS
  set c := (idealPowerStalkComparison X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
    ((pullbackFunctor f).obj (F.X n)) x b hb).map n with hc
  have h := etaStalkIso_hom X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
    (pullbackComplex f F) hF' x b hb n
  have step₁ : S.map (pullbackEtaTermMap f I ι F n) ≫
      ((etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (pullbackComplex f F) hF' x b hb).hom.f n ≫
        ModuleCat.ofHom (Submodule.subtype
          (EtaComplex.term b (stalkComplex X x (pullbackComplex f F)) n))) =
      S.map (pullbackEtaTermMap f I ι F n) ≫
        (S.map (etaFst X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (pullbackComplex f F) n) ≫ c) :=
    congrArg (fun k => S.map (pullbackEtaTermMap f I ι F n) ≫ k) h
  have step₂ : S.map (pullbackEtaTermMap f I ι F n) ≫
        (S.map (etaFst X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (pullbackComplex f F) n) ≫ c) =
      S.map (pullbackEtaTermMap f I ι F n ≫
        etaFst X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (pullbackComplex f F) n) ≫ c :=
    (Category.assoc _ _ c).symm.trans
      (congrArg (fun k => k ≫ c) (S.map_comp _ _).symm)
  have step₃ : S.map (pullbackEtaTermMap f I ι F n ≫
        etaFst X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (pullbackComplex f F) n) ≫ c =
      S.map ((pullbackFunctor f).map (etaFst Y I ι F n) ≫
        (pullbackIdealPowerIso f I n (F.X n)).hom) ≫ c :=
    congrArg (fun k => S.map k ≫ c) (pullbackEtaTermMap_fst f I ι F n)
  have step₄ : S.map ((pullbackFunctor f).map (etaFst Y I ι F n) ≫
        (pullbackIdealPowerIso f I n (F.X n)).hom) ≫ c =
      S.map ((pullbackFunctor f).map (etaFst Y I ι F n)) ≫
        S.map (pullbackIdealPowerIso f I n (F.X n)).hom ≫ c :=
    (congrArg (fun k => k ≫ c) (S.map_comp _ _)).trans (Category.assoc _ _ c)
  exact step₁.trans (step₂.trans (step₃.trans step₄))


/-! ### Isomorphy is stalkwise, at the spelling of the décalage files -/

/-- **A morphism of sheaves of modules is an isomorphism as soon as every one of its maps of
stalks is bijective**, at the `Stacks.IdealTorsion.Eta.stalkModuleFunctor` spelling of the stalk,
which is the one the décalage calculus uses.  This is the module-valued stalk criterion
`AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map` read over the
commutative local ring: restriction of scalars along
`SemilinearStalk.commStalkIso` does not change the underlying map, so bijectivity over
`𝒪_{X,x}` is bijectivity over the `RingCat`-valued stalk. -/
theorem isIso_of_forall_stalk_bijective {Z : RingedSpace.{u}}
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)} (g : M ⟶ N)
    (h : ∀ z : Z, Function.Bijective ((stalkModuleFunctor Z z).map g).hom) : IsIso g :=
  (AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf) g).2
      fun z => (ConcreteCategory.isIso_iff_bijective _).2 (h z)

/-! ### Transport of a décalage term along a square of isomorphisms -/

/-- **The degree-`k` décalage term is carried onto the degree-`k` décalage term by an
isomorphism of the ambient modules compatible with the differentials.**  Both inclusions are
`Stacks.Eta.GoodBaseChange.fLoc_mem_fetaTerm_of_square`, the second applied to the square of the
inverse isomorphisms.

The isomorphisms are given as pairs of linear maps rather than as `LinearEquiv`s, because the
consumer has them as components of an isomorphism of `ModuleCat`; only the one composition
`g ∘ g' = id` is needed, together with the two commuting squares. -/
theorem map_fLoc_fetaTerm {R : Type u} [CommRing R] (r : R)
    {P Q P' Q' : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q']
    (d : P →ₗ[R] Q) (d' : P' →ₗ[R] Q')
    (g : P →ₗ[R] P') (g' : P' →ₗ[R] P) (h : Q →ₗ[R] Q') (h' : Q' →ₗ[R] Q)
    (hgg' : g.comp g' = LinearMap.id)
    (hcomm : d'.comp g = h.comp d) (hcomm' : d.comp g' = h'.comp d') (k : ℤ) :
    Submodule.map (EtaPow.fLoc r g) (EtaPow.fetaTerm r d k) = EtaPow.fetaTerm r d' k := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact Stacks.Eta.GoodBaseChange.fLoc_mem_fetaTerm_of_square r d d' g h hcomm k hz
  · intro w hw
    refine ⟨EtaPow.fLoc r g' w,
      Stacks.Eta.GoodBaseChange.fLoc_mem_fetaTerm_of_square r d' d g' h' hcomm' k hw, ?_⟩
    rw [EtaComplex.localizedMap_comp_apply, hgg', EtaComplex.localizedMap_id_apply]

/-- Equal composites of morphisms of modules give equal composites of the underlying linear maps. -/
private theorem hom_comp_eq_hom_comp {R : Type u} [Ring R] {A B C D : ModuleCat.{u} R}
    {p : A ⟶ B} {q : B ⟶ C} {p' : A ⟶ D} {q' : D ⟶ C} (h : p ≫ q = p' ≫ q') :
    q.hom.comp p.hom = q'.hom.comp p'.hom :=
  (ModuleCat.hom_comp _ _).symm.trans
    ((congrArg ModuleCat.Hom.hom h).trans (ModuleCat.hom_comp _ _))

/-- The underlying linear maps of a pair of mutually inverse morphisms of modules compose to the
identity. -/
private theorem hom_comp_eq_id {R : Type u} [Ring R] {A B : ModuleCat.{u} R} {p : A ⟶ B}
    {q : B ⟶ A} (h : p ≫ q = 𝟙 A) : q.hom.comp p.hom = LinearMap.id :=
  (ModuleCat.hom_comp _ _).symm.trans (congrArg ModuleCat.Hom.hom h)

/-! ### The stalk of the comparison is the ring-level comparison of Tag 0F7X -/

section Crux

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

/-- **The stalk of the degreewise comparison of décalages, factored.**  Read inside the
localization at `b` of the stalk at `x` of `f^*F^n`, the stalk at `x` of
`Stacks.IdealTorsion.Eta.pullbackEtaTermMap` is an isomorphism followed by the ambient form of
the ring-level comparison of Tag 0F7X and then by the localization of the inverse comparison of
Tag 0098.

The three steps are: the sheaf-to-ring bridge
`Stacks.IdealTorsion.Eta.stalkOfPullbackEtaTermMap_ambient`; the identification of the
normalized ideal-power comparison downstairs with the base change of the one upstairs
(`Stacks.IdealTorsion.Eta.idealPowerStalkComparison_pullback`); and the naturality of Tag 0098
in the module, which lets the first projection be moved across, after which the characterization
`Stacks.IdealTorsion.Eta.etaStalkIso_hom` of Tag 0GT6 upstairs applies.

No flatness is assumed. -/
theorem stalkOfPullbackEtaTermMap_factor (n : ℤ) :
    (stalkModuleFunctor X x).map (pullbackEtaTermMap f I ι F n) ≫
        (etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
              (pullbackComplex f F) hF' x (commStalkGermMap f x a) hb).hom.f n ≫
          ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term (commStalkGermMap f x a)
              (stalkComplex X x (pullbackComplex f F)) n)) =
      (stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫
        (commStalkBaseChange f x).map
            ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n) ≫
          (commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
              (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))) ≫
            stalkPsiMap f x (F.X n) a ≫ stalkLocBaseChangeInv f x (F.X n) a := by
  have hY : (etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n ≫
        ModuleCat.ofHom (Submodule.subtype
          (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n)) =
      (stalkModuleFunctor Y (f.hom.base x)).map (etaFst Y I ι F n) ≫
        (idealPowerStalkComparison Y I ι (F.X n) (f.hom.base x) a ha).map n :=
    etaStalkIso_hom Y I ι F hF (f.hom.base x) a ha n
  have hnat : (stalkModuleFunctor X x).map ((pullbackFunctor f).map (etaFst Y I ι F n)) ≫
        (stalkPullbackBaseChangeIso f x).hom.app (idealPowerTerm Y I n (F.X n)) =
      (stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫
        (commStalkBaseChange f x).map
          ((stalkModuleFunctor Y (f.hom.base x)).map (etaFst Y I ι F n)) :=
    stalkPullbackBaseChangeIso_naturality f x (etaFst Y I ι F n)
  rw [stalkOfPullbackEtaTermMap_ambient f x I ι F hF' (commStalkGermMap f x a) hb n,
    idealPowerStalkComparison_pullback f x I ι (F.X n) a ha hb n]
  simp only
  rw [← Category.assoc ((stalkModuleFunctor X x).map
    ((pullbackFunctor f).map (etaFst Y I ι F n))), hnat]
  simp only [Category.assoc]
  rw [← Category.assoc ((commStalkBaseChange f x).map
      ((stalkModuleFunctor Y (f.hom.base x)).map (etaFst Y I ι F n))),
    ← Functor.map_comp, ← hY]
  simp only
  exact congrArg
    (fun k => (stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫ k)
    ((congrArg (fun k => k ≫ (stalkPsiMap f x (F.X n) a ≫
          stalkLocBaseChangeInv f x (F.X n) a))
        ((commStalkBaseChange f x).map_comp
          ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n)
          (ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))))).trans
      (Category.assoc _ _ _))


/-- The two naturality squares of Tag 0098 at the differential of `F`, as equations of linear
maps: they are the two commuting squares that
`Stacks.IdealTorsion.Eta.map_fLoc_fetaTerm` consumes. -/
private theorem stalkPullbackBaseChange_square (n : ℤ) :
    ((stalkModuleFunctor X x).map ((pullbackFunctor f).map (F.d n (n + 1)))).hom.comp
          ((stalkPullbackBaseChangeIso f x).inv.app (F.X n)).hom =
        ((stalkPullbackBaseChangeIso f x).inv.app (F.X (n + 1))).hom.comp
          ((commStalkBaseChange f x).map
            ((stalkModuleFunctor Y (f.hom.base x)).map (F.d n (n + 1)))).hom ∧
      ((commStalkBaseChange f x).map
            ((stalkModuleFunctor Y (f.hom.base x)).map (F.d n (n + 1)))).hom.comp
          ((stalkPullbackBaseChangeIso f x).hom.app (F.X n)).hom =
        ((stalkPullbackBaseChangeIso f x).hom.app (F.X (n + 1))).hom.comp
          ((stalkModuleFunctor X x).map ((pullbackFunctor f).map (F.d n (n + 1)))).hom :=
  ⟨hom_comp_eq_hom_comp ((stalkPullbackBaseChangeIso f x).inv.naturality (F.d n (n + 1))).symm,
    hom_comp_eq_hom_comp ((stalkPullbackBaseChangeIso f x).hom.naturality (F.d n (n + 1))).symm⟩

/-- **The localization at `b` of the inverse comparison of Tag 0098 carries the degree-`n`
décalage term of the base change of the stalk complex onto the degree-`n` décalage term of the
stalk complex of the pullback.** -/
theorem map_stalkLocBaseChangeInv_fetaTerm (n : ℤ) :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (commStalkGermMap f x).toAlgebra
    Submodule.map (stalkLocBaseChangeInv f x (F.X n) a).hom
        (EtaPow.fetaTerm (commStalkGermMap f x a)
          (LinearMap.baseChange (ringStalk X x)
            ((stalkComplex Y (f.hom.base x) F).d n (n + 1)).hom) n) =
      EtaComplex.term (commStalkGermMap f x a) (stalkComplex X x (pullbackComplex f F)) n := by
  obtain ⟨hsq, hsq'⟩ := stalkPullbackBaseChange_square f x F n
  exact map_fLoc_fetaTerm (commStalkGermMap f x a)
    ((commStalkBaseChange f x).map
      ((stalkModuleFunctor Y (f.hom.base x)).map (F.d n (n + 1)))).hom
    ((stalkModuleFunctor X x).map ((pullbackFunctor f).map (F.d n (n + 1)))).hom
    ((stalkPullbackBaseChangeIso f x).inv.app (F.X n)).hom
    ((stalkPullbackBaseChangeIso f x).hom.app (F.X n)).hom
    ((stalkPullbackBaseChangeIso f x).inv.app (F.X (n + 1))).hom
    ((stalkPullbackBaseChangeIso f x).hom.app (F.X (n + 1))).hom
    (hom_comp_eq_id (Iso.hom_inv_id_app (stalkPullbackBaseChangeIso f x) (F.X n))) hsq hsq' n


/-- **The ambient form of the ring-level comparison of Tag 0F7X.**  The base change of the
inclusion of the degree-`n` décalage term, followed by the comparison
`Stacks.Eta.BaseChange.psiEquiv`, is the comparison `Stacks.Eta.GoodBaseChange.psiTermMap`
followed by the inclusion of the décalage term of the base change. -/
theorem stalkPsiMap_comp_eq (n : ℤ) :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (commStalkGermMap f x).toAlgebra
    ((commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))) ≫
          stalkPsiMap f x (F.X n) a).hom =
      (EtaPow.fetaTerm (commStalkGermMap f x a)
          (LinearMap.baseChange (ringStalk X x)
            ((stalkComplex Y (f.hom.base x) F).d n (n + 1)).hom) n).subtype.comp
        (Stacks.Eta.GoodBaseChange.psiTermMap (B := ringStalk X x) a
          ((stalkComplex Y (f.hom.base x) F).d n (n + 1)).hom n) := rfl


include hF hF' ha hb in
/-- The factorization of `Stacks.IdealTorsion.Eta.stalkOfPullbackEtaTermMap_factor` with its
right-hand side regrouped as an isomorphism, the ambient ring-level comparison, and an
isomorphism. -/
theorem stalkOfPullbackEtaTermMap_factor' (n : ℤ) :
    (stalkModuleFunctor X x).map (pullbackEtaTermMap f I ι F n) ≫
        (etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
            (pullbackComplex f F) hF' x (commStalkGermMap f x a) hb).hom.f n ≫
          ModuleCat.ofHom (Submodule.subtype
          (EtaComplex.term (commStalkGermMap f x a)
            (stalkComplex X x (pullbackComplex f F)) n)) =
      ((stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫
        (commStalkBaseChange f x).map
          ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n)) ≫
        (((commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))) ≫
          stalkPsiMap f x (F.X n) a) ≫ stalkLocBaseChangeInv f x (F.X n) a) :=
  (stalkOfPullbackEtaTermMap_factor f x I ι F hF hF' a ha hb n).trans
    (congrArg (fun k => (stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫
        (commStalkBaseChange f x).map
          ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n) ≫ k)
      (Category.assoc ((commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))))
        (stalkPsiMap f x (F.X n) a) (stalkLocBaseChangeInv f x (F.X n) a)).symm)

/-- The localization at `b` of the inverse comparison of Tag 0098 is bijective. -/
theorem bijective_stalkLocBaseChangeInv
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (a : ringStalk Y (f.hom.base x)) :
    Function.Bijective (stalkLocBaseChangeInv f x M a).hom := by
  have hLhom : (stalkLocBaseChangeInv f x M a).hom =
      EtaPow.fLoc (commStalkGermMap f x a)
        ((stalkPullbackBaseChangeIso f x).inv.app M).hom := rfl
  rw [hLhom]
  have h1 : ((stalkPullbackBaseChangeIso f x).hom.app M).hom.comp
      ((stalkPullbackBaseChangeIso f x).inv.app M).hom = LinearMap.id :=
    hom_comp_eq_id (Iso.inv_hom_id_app (stalkPullbackBaseChangeIso f x) M)
  have h2 : ((stalkPullbackBaseChangeIso f x).inv.app M).hom.comp
      ((stalkPullbackBaseChangeIso f x).hom.app M).hom = LinearMap.id :=
    hom_comp_eq_id (Iso.hom_inv_id_app (stalkPullbackBaseChangeIso f x) M)
  refine ⟨fun z w hzw => ?_, fun w => ⟨EtaPow.fLoc (commStalkGermMap f x a)
    ((stalkPullbackBaseChangeIso f x).hom.app M).hom w, ?_⟩⟩
  · have h := congrArg (EtaPow.fLoc (commStalkGermMap f x a)
      ((stalkPullbackBaseChangeIso f x).hom.app M).hom) hzw
    rwa [EtaComplex.localizedMap_comp_apply, EtaComplex.localizedMap_comp_apply, h1,
      EtaComplex.localizedMap_id_apply, EtaComplex.localizedMap_id_apply] at h
  · rw [EtaComplex.localizedMap_comp_apply, h2, EtaComplex.localizedMap_id_apply]

omit [Mono (pullbackIdealIncl f I ι)] in
include hF ha in
/-- The left factor of the factorization is bijective: it is the comparison of Tag 0098 followed
by the base change of the comparison of Tag 0GT6 upstairs. -/
theorem bijective_stalkFactorIso (n : ℤ) :
    Function.Bijective (((stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫
        (commStalkBaseChange f x).map
          ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n))).hom := by
  rw [ModuleCat.hom_comp]
  exact ((ConcreteCategory.isIso_iff_bijective ((commStalkBaseChange f x).map
          ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n))).1 inferInstance).comp
    -- the component is an isomorphism because the natural transformation is; the instance is
    -- given by name, `etaTerm` being indexed by a spelling of the structure sheaf that instance
    -- search does not reach from the one `stalkPullbackBaseChangeIso` is typed over
    ((ConcreteCategory.isIso_iff_bijective
      ((stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n))).1
        ((stalkPullbackBaseChangeIso f x).app (etaTerm Y I ι F n)).isIso_hom)

/-- The middle factor of the factorization is the ambient ring-level comparison of Tag 0F7X, so
it is injective as soon as that comparison is. -/
theorem injective_stalkFactorPsi (n : ℤ)
    (hinj : letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
        (commStalkGermMap f x).toAlgebra
      Function.Injective (Stacks.Eta.GoodBaseChange.psiTermMap (B := ringStalk X x) a
        ((stalkComplex Y (f.hom.base x) F).d n (n + 1)).hom n)) :
    Function.Injective (((commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))) ≫
          stalkPsiMap f x (F.X n) a)).hom := by
  let : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) := (commStalkGermMap f x).toAlgebra
  rw [stalkPsiMap_comp_eq]
  exact Subtype.val_injective.comp hinj

/-- The image of the middle factor is the whole décalage term of the base change as soon as the
ring-level comparison of Tag 0F7X is surjective. -/
theorem range_stalkFactorPsi (n : ℤ)
    (hsurj : letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
        (commStalkGermMap f x).toAlgebra
      Function.Surjective (Stacks.Eta.GoodBaseChange.psiTermMap (B := ringStalk X x) a
        ((stalkComplex Y (f.hom.base x) F).d n (n + 1)).hom n)) :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (commStalkGermMap f x).toAlgebra
    LinearMap.range (((commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))) ≫
          stalkPsiMap f x (F.X n) a)).hom = EtaPow.fetaTerm (commStalkGermMap f x a)
        (LinearMap.baseChange (ringStalk X x)
          ((stalkComplex Y (f.hom.base x) F).d n (n + 1)).hom) n := by
  let : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) := (commStalkGermMap f x).toAlgebra
  rw [stalkPsiMap_comp_eq]
  exact (LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.2 hsurj)).trans (Submodule.range_subtype _)

omit [Mono ι] in
include hF' hb in
/-- The comparison of Tag 0GT6 downstairs, followed by the inclusion of the décalage term into
the localization, is injective with image that décalage term. -/
theorem injective_and_range_stalkEtaSub (n : ℤ) :
    Function.Injective ((etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
            (pullbackComplex f F) hF' x (commStalkGermMap f x a) hb).hom.f n ≫
        ModuleCat.ofHom (Submodule.subtype
          (EtaComplex.term (commStalkGermMap f x a)
            (stalkComplex X x (pullbackComplex f F)) n))).hom ∧
      LinearMap.range ((etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
            (pullbackComplex f F) hF' x (commStalkGermMap f x a) hb).hom.f n ≫
        ModuleCat.ofHom (Submodule.subtype
          (EtaComplex.term (commStalkGermMap f x a)
            (stalkComplex X x (pullbackComplex f F)) n))).hom =
        EtaComplex.term (commStalkGermMap f x a)
          (stalkComplex X x (pullbackComplex f F)) n := by
  have hbijX := (ConcreteCategory.isIso_iff_bijective
    ((etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
            (pullbackComplex f F) hF' x (commStalkGermMap f x a) hb).hom.f n)).1
    ((HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso
      (etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
        (pullbackComplex f F) hF' x (commStalkGermMap f x a) hb)).isIso_hom
  have hjhom : ((etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
            (pullbackComplex f F) hF' x (commStalkGermMap f x a) hb).hom.f n ≫
        ModuleCat.ofHom (Submodule.subtype
          (EtaComplex.term (commStalkGermMap f x a)
            (stalkComplex X x (pullbackComplex f F)) n))).hom =
      (Submodule.subtype (EtaComplex.term (commStalkGermMap f x a)
          (stalkComplex X x (pullbackComplex f F)) n)).comp
        ((etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
            (pullbackComplex f F) hF' x (commStalkGermMap f x a) hb).hom.f n).hom :=
    ModuleCat.hom_comp _ _
  refine ⟨?_, ?_⟩
  · rw [hjhom]
    exact Subtype.val_injective.comp hbijX.injective
  · rw [hjhom]
    exact (LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 hbijX.surjective)).trans (Submodule.range_subtype _)

include hF hF' ha hb in
/-- **The stalk of the degreewise comparison of décalages is bijective as soon as the ring-level
comparison of Tag 0F7X is bijective at that stalk.**

No flatness is assumed anywhere: the hypothesis is exactly the conclusion of Tag 0F7X for the
germ map `𝒪_{Y,f(x)} → 𝒪_{X,x}`, the generator `a` of the stalk ideal and the differential of
the stalk complex of `F` in degree `n`. -/
theorem bijective_stalk_pullbackEtaTermMap (n : ℤ)
    (hbij : letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
        (commStalkGermMap f x).toAlgebra
      Function.Bijective (Stacks.Eta.GoodBaseChange.psiTermMap (B := ringStalk X x) a
        ((stalkComplex Y (f.hom.base x) F).d n (n + 1)).hom n)) :
    Function.Bijective ((stalkModuleFunctor X x).map (pullbackEtaTermMap f I ι F n)).hom := by
  let : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) := (commStalkGermMap f x).toAlgebra
  obtain ⟨hjinj, hjrange⟩ := injective_and_range_stalkEtaSub f x I ι F hF' a hb n
  have hRhom : (((stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫
        (commStalkBaseChange f x).map
          ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n)) ≫
        (((commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))) ≫
          stalkPsiMap f x (F.X n) a) ≫ stalkLocBaseChangeInv f x (F.X n) a)).hom =
      ((stalkLocBaseChangeInv f x (F.X n) a).hom.comp
          (((commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
              (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))) ≫
            stalkPsiMap f x (F.X n) a)).hom).comp
        (((stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫
          (commStalkBaseChange f x).map
            ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n))).hom :=
    (ModuleCat.hom_comp _ _).trans
      (congrArg (fun k => LinearMap.comp k
          (((stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫
            (commStalkBaseChange f x).map
              ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n))).hom)
        (ModuleCat.hom_comp _ _))
  have hRinj : Function.Injective (((stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫
        (commStalkBaseChange f x).map
          ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n)) ≫
        (((commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))) ≫
          stalkPsiMap f x (F.X n) a) ≫ stalkLocBaseChangeInv f x (F.X n) a)).hom := by
    rw [hRhom]
    exact (((bijective_stalkLocBaseChangeInv f x (F.X n) a).injective).comp
      (injective_stalkFactorPsi f x F a n hbij.injective)).comp
      (bijective_stalkFactorIso f x I ι F hF a ha n).injective
  have hRrange : LinearMap.range (((stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫
        (commStalkBaseChange f x).map
          ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n)) ≫
        (((commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))) ≫
          stalkPsiMap f x (F.X n) a) ≫ stalkLocBaseChangeInv f x (F.X n) a)).hom =
      EtaComplex.term (commStalkGermMap f x a)
        (stalkComplex X x (pullbackComplex f F)) n := by
    rw [hRhom]
    exact (LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2
        (bijective_stalkFactorIso f x I ι F hF a ha n).surjective)).trans
      ((LinearMap.range_comp _ _).trans
        ((congrArg (Submodule.map (stalkLocBaseChangeInv f x (F.X n) a).hom)
            (range_stalkFactorPsi f x F a n hbij.surjective)).trans
          (map_stalkLocBaseChangeInv_fetaTerm f x F a n)))
  have hp : ∀ z, ((etaStalkIso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
            (pullbackComplex f F) hF' x (commStalkGermMap f x a) hb).hom.f n ≫
          ModuleCat.ofHom (Submodule.subtype
          (EtaComplex.term (commStalkGermMap f x a)
            (stalkComplex X x (pullbackComplex f F)) n))).hom
        (((stalkModuleFunctor X x).map (pullbackEtaTermMap f I ι F n)).hom z) =
      (((stalkPullbackBaseChangeIso f x).hom.app (etaTerm Y I ι F n) ≫
        (commStalkBaseChange f x).map
          ((etaStalkIso Y I ι F hF (f.hom.base x) a ha).hom.f n)) ≫
        (((commStalkBaseChange f x).map (ModuleCat.ofHom (Submodule.subtype
            (EtaComplex.term a (stalkComplex Y (f.hom.base x) F) n))) ≫
          stalkPsiMap f x (F.X n) a) ≫ stalkLocBaseChangeInv f x (F.X n) a)).hom z := fun z =>
    ConcreteCategory.congr_hom (stalkOfPullbackEtaTermMap_factor' f x I ι F hF hF' a ha hb n) z
  refine ⟨fun z w hzw => hRinj ?_, fun t => ?_⟩
  · rw [← hp, ← hp, hzw]
  · obtain ⟨z, hz⟩ := (hRrange.trans hjrange.symm).ge ⟨t, rfl⟩
    exact ⟨z, hjinj ((hp z).trans hz)⟩

end Crux


/-! ### The crux: goodness in place of flatness -/

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
/-- **The degreewise comparison of décalages under a pullback is an isomorphism as soon as the
ring-level comparison of Tag 0F7X is bijective at every stalk.**

Concretely, the hypothesis asks that at every point `x` of `X` there be a generator `a` of the
stalk ideal `I_{f(x)}` whose image under the germ map generates `(f^*I)_x`, and for which the
comparison
`𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} (η_a F_{f(x)})^n ⟶ (η_b (𝒪_{X,x} ⊗ F_{f(x)}))^n`
of `Stacks.Eta.GoodBaseChange.psiTermMap` is bijective.  That is exactly the conclusion of Tag
0F7X, which holds when the stalk complex of `F` at `f(x)` is a bounded complex of finite free
modules whose determinantal ideals `I_i(F_{f(x)}, a)` are principal — the goodness condition of
Stacks tag 0F8S.  **There is no flatness hypothesis**: the only criterion for this comparison
previously available, `Stacks.IdealTorsion.Eta.isIso_pullbackEtaTermMap`, assumes `f` flat and is
not used.

The proof is the stalk criterion `Stacks.IdealTorsion.Eta.isIso_of_forall_stalk_bijective`
together with `Stacks.IdealTorsion.Eta.bijective_stalk_pullbackEtaTermMap`. -/
theorem isIso_pullbackEtaTermMap_of_forall_stalk (n : ℤ)
    (h : ∀ x : X, ∃ (a : ringStalk Y (f.hom.base x))
        (_ : GeneratesStalkIdeal Y ι (f.hom.base x) a)
        (_ : GeneratesStalkIdeal X (pullbackIdealIncl f I ι) x (commStalkGermMap f x a)),
        letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
          (commStalkGermMap f x).toAlgebra
        Function.Bijective (Stacks.Eta.GoodBaseChange.psiTermMap (B := ringStalk X x) a
          ((stalkComplex Y (f.hom.base x) F).d n (n + 1)).hom n)) :
    IsIso (pullbackEtaTermMap f I ι F n) := by
  refine isIso_of_forall_stalk_bijective _ fun x => ?_
  obtain ⟨a, ha, hb, hbij⟩ := h x
  exact bijective_stalk_pullbackEtaTermMap f x I ι F hF hF' a ha hb n hbij

include hF hF' in
/-- **The comparison of décalages under a pullback is an isomorphism of complexes as soon as the
ring-level comparison of Tag 0F7X is bijective at every stalk in every degree**:
`f^*(η_I F^•) ≅ η_{f^*I}(f^* F^•)` with no flatness hypothesis.

Degreewise this is `Stacks.IdealTorsion.Eta.isIso_pullbackEtaTermMap_of_forall_stalk`; the
passage to complexes is `CategoryTheory.HomologicalComplex.Hom.isIso_of_components`, exactly as
in the flat case `Stacks.IdealTorsion.Eta.isIso_pullbackEtaMap`. -/
theorem isIso_pullbackEtaMap_of_forall_stalk
    (h : ∀ (n : ℤ) (x : X), ∃ (a : ringStalk Y (f.hom.base x))
        (_ : GeneratesStalkIdeal Y ι (f.hom.base x) a)
        (_ : GeneratesStalkIdeal X (pullbackIdealIncl f I ι) x (commStalkGermMap f x a)),
        letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
          (commStalkGermMap f x).toAlgebra
        Function.Bijective (Stacks.Eta.GoodBaseChange.psiTermMap (B := ringStalk X x) a
          ((stalkComplex Y (f.hom.base x) F).d n (n + 1)).hom n)) :
    IsIso (pullbackEtaMap f I ι F hF hF') := by
  have hcomp : ∀ n : ℤ, IsIso ((pullbackEtaMap f I ι F hF hF').f n) := fun n => by
    rw [pullbackEtaMap_f]
    exact isIso_pullbackEtaTermMap_of_forall_stalk f I ι F hF hF' n (h n)
  exact HomologicalComplex.Hom.isIso_of_components _

end Criterion

end Stacks.IdealTorsion.Eta

end
