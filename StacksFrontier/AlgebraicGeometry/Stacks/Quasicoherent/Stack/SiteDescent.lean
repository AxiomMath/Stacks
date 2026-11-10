module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Stack.Fibre
import all StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Stack.Fibre

/-!
# Stacks 03YM, part 2: descent data on the site compared with the fibres

This file continues the proof of Stacks 03YM (assembled in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Stack`):

* the naturality and composition coherences of the chosen cartesian lifts, and the comparison
  isomorphisms `modulePullbackComparison` and `modulePullbackCompIso`;
* the transition morphisms `moduleTransition` of the fibres along arrows of the site;
* the comparison `moduleDescentFunctor` of fibre-wise descent data with the sieve-free descent
  data of Stacks 023B read on the site, and the proof that it is an equivalence;
* the comparison of iterated pullbacks, `modulePullbackCompIso'` and `moduleCanonicalComparison`.

## References

* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
* [Stacks Project, Tag 03YM](https://stacks.math.columbia.edu/tag/03YM)
* [Stacks Project, Tag 04U2](https://stacks.math.columbia.edu/tag/04U2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.QCoh

universe u

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The two coherence computations of the chosen cartesian lifts

The cartesian lift chosen above is the unit of the pullback–pushforward adjunction read as an
`f`-map, so both its naturality and its compatibility with composition are, after the hom-set
identification of Stacks 04U2 is unwound, equations between composites of that unit with the three
structural isomorphisms of `AlgebraicGeometry.Scheme.Modules.pushforward`.  Each of those
isomorphisms is componentwise the identity
(`AlgebraicGeometry.Stacks.Modules.pushforwardId_inv_app` and the two lemmas beside
it), so rewriting with the three identifications turns the whole computation into a chain of
`eqToHom`s that `eqToHom_trans` collapses, leaving only the adjunction fact.

Both equations are stated here over a *variable* scheme, module and morphism and instantiated at
the concrete data afterwards.  At the concrete data the two sides are composites in
`(ofModule _).val`, whose module arguments are spelled through `modulePullback` and
`ObjectProperty.lift`; `simp` indexes neither, so none of the three identifications fires and the
only remaining route is to split `AlgebraicGeometry.Scheme.Modules.Hom.app` of the composite one
factor at a time, whose `Eq.mpr` tower then exceeds the heartbeat budget in the final `whnf`.
Over variable data every rewrite fires on the first try, and the single instantiation that
follows is one unification. -/

/-- The unit of the pullback–pushforward adjunction is natural. -/
lemma moduleUnit_naturality {X Y : Scheme.{u}} (g : X ⟶ Y) {M N : Y.Modules}
    (φ : N ⟶ M) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N ≫
        (Scheme.Modules.pushforward g).map ((Scheme.Modules.pullback g).map φ) =
      φ ≫ (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality φ).symm

/-- Comparing pullbacks along one and the same morphism is the identity.

`Scheme.Modules.pullbackCongr` takes an equality of two morphisms; here both are `g`, and the only
inhabitant of `g = g` is `rfl`, so the equality is written out rather than bound. Binding it as a
hypothesis `h : g = g` would carry no information. -/
private lemma pullbackCongr_app_inv_eq_id {X Y : Scheme.{u}} {g : X ⟶ Y}
    (M : Y.Modules) : ((Scheme.Modules.pullbackCongr (rfl : g = g)).app M).inv = 𝟙 _ :=
  rfl

/-- The coherence form of naturality of the unit: the shape taken by naturality of the chosen
cartesian lift once the `f`-map description of the hom-sets is unwound, stated over variable data.

`p` and `q` stand for the two identity morphisms produced by `FMap.id`, and
the four equalities for the coherence isomorphisms that the identity and the composition of
`f`-maps carry; only their types matter, the proofs being irrelevant. -/
private lemma moduleUnit_naturality_coherence {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M N : Y.Modules} (φ : N ⟶ M)
    {p : X ⟶ X} (hp : p = 𝟙 X) (hpg : g = p ≫ g)
    {q : Y ⟶ Y} (hq : q = 𝟙 Y) (hgq : g = g ≫ q) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pullback g).map φ ≫
            (Scheme.Modules.pushforwardId X).inv.app ((Scheme.Modules.pullback g).obj M) ≫
              (Scheme.Modules.pushforwardCongr hp).inv.app
                ((Scheme.Modules.pullback g).obj M)) ≫
          (Scheme.Modules.pushforwardComp p g).hom.app ((Scheme.Modules.pullback g).obj M) ≫
            (Scheme.Modules.pushforwardCongr hpg).inv.app ((Scheme.Modules.pullback g).obj M) =
      (φ ≫ (Scheme.Modules.pushforwardId Y).inv.app M ≫
          (Scheme.Modules.pushforwardCongr hq).inv.app M) ≫
        (Scheme.Modules.pushforward q).map
            ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) ≫
          (Scheme.Modules.pushforwardComp g q).hom.app ((Scheme.Modules.pullback g).obj M) ≫
            (Scheme.Modules.pushforwardCongr hgq).inv.app
              ((Scheme.Modules.pullback g).obj M) := by
  subst hp
  subst hq
  simp only [Stacks.Modules.pushforwardId_inv_app,
    Stacks.Modules.pushforwardComp_hom_app,
    Stacks.Modules.pushforwardCongr_inv_app, CategoryTheory.Functor.map_comp,
    eqToHom_refl, Category.assoc]
  rw [CategoryTheory.Functor.congr_hom Stacks.Modules.pushforward_id_eq
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)]
  simp only [CategoryTheory.Functor.id_map, Category.assoc]
  exact moduleUnit_naturality g φ

/-- The coherence form of the compatibility of the unit with composition: the shape taken by the
composition law of the chosen cartesian lifts once the `f`-map description of the hom-sets is
unwound, stated over variable data.

The content is that the unit of the composite adjunction is conjugate to the unit of the
adjunction of the composite along `AlgebraicGeometry.Scheme.Modules.pullbackComp`, which is
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`. -/
private lemma moduleUnit_comp_coherence {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (M : Z.Modules) {k : X ⟶ Z} (hk : g ≫ f = k) {p : X ⟶ X} (hp : p = 𝟙 X)
    {m : X ⟶ Z} (hmk : m = p ≫ k) (hmgf : m = g ≫ f) :
    (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M ≫
        (Scheme.Modules.pushforward k).map
          (((Scheme.Modules.pullbackComp g f).app M ≪≫
              (Scheme.Modules.pullbackCongr hk).app M).inv ≫
            (Scheme.Modules.pushforwardId X).inv.app
                ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M)) ≫
              (Scheme.Modules.pushforwardCongr hp).inv.app
                ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M))) ≫
          (Scheme.Modules.pushforwardComp p k).hom.app
              ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M)) ≫
            (Scheme.Modules.pushforwardCongr hmk).inv.app
              ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map
            ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
              ((Scheme.Modules.pullback f).obj M)) ≫
          (Scheme.Modules.pushforwardComp g f).hom.app
              ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M)) ≫
            (Scheme.Modules.pushforwardCongr hmgf).inv.app
              ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M)) := by
  subst hk
  subst hp
  subst hmgf
  rw [Iso.trans_inv, pullbackCongr_app_inv_eq_id]
  simp only [Stacks.Modules.pushforwardId_inv_app,
    Stacks.Modules.pushforwardComp_hom_app,
    Stacks.Modules.pushforwardCongr_inv_app, CategoryTheory.Functor.map_comp,
    eqToHom_refl, Category.assoc]
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f))
    (Scheme.Modules.pullbackComp g f).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  simp only [Adjunction.comp_unit_app, Stacks.Modules.pushforwardComp_hom_app] at h
  exact h.symm

/-- Two composites of morphisms of `QCohObject` agree once their `f`-map descriptions do. -/
private lemma comp_eq_of_rawHom_comp {A C C' D : AlgebraicGeometry.QCohObject B S hS}
    (m : A ⟶ C) (n : C ⟶ D) (m' : A ⟶ C') (n' : C' ⟶ D)
    (h : FMap.comp (rawHom _ _ m) (rawHom _ _ n) = FMap.comp (rawHom _ _ m') (rawHom _ _ n')) :
    m ≫ n = m' ≫ n' := by
  apply (rawHom _ _).injective
  change Equiv.cast (catData.hom_type _ _) (_ ≫ _) = Equiv.cast (catData.hom_type _ _) (_ ≫ _)
  rw [catData.composition, catData.composition]
  exact h

/-- Naturality of the chosen cartesian lift. -/
private lemma moduleCartesianMap_naturality
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (f : V ⟶ U) {M N : modulesOn U} (φ : N ⟶ M) :
    (ofModuleMap ((modulePullback f).map φ)).val ≫ moduleCartesianMap f N =
      moduleCartesianMap f M ≫ (ofModuleMap φ).val := by
  refine comp_eq_of_rawHom_comp _ _ _ _ ?_
  dsimp only [ofModuleMap, moduleCartesianMap]
  simp only [Equiv.apply_symm_apply]
  refine Sigma.ext (by simp [FMap.comp]) (heq_of_eq ?_)
  dsimp [FMap.comp, FMap.id, modulePullback]
  exact moduleUnit_naturality_coherence (schemeFunctor.map f) φ.hom rfl (Category.id_comp _).symm
    rfl (Category.comp_id _).symm

attribute [local instance] isFibered_rawProjection

/-- The pullback of a quasi-coherent module along `f`, read in the fibre over the source of `f`, is
the chosen pullback of the fibre. -/
private noncomputable def modulePullbackComparison
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (f : V ⟶ U) (M : modulesOn U) :
    ofModule ((modulePullback f).obj M) ≅ Functor.pullbackFiber rawProjection (ofModule M) f :=
  Functor.fiberIsoOfCartesian f (moduleCartesianMap f M)
    (Functor.IsPreFibered.pullbackMap (ofModule M).2 f)
    (by have := moduleCartesianMap_isStronglyCartesian f M; infer_instance) inferInstance

/-- The chosen pullback comparison factors the chosen cartesian lift.  Every argument of
`CategoryTheory.Functor.fiberIsoOfCartesian` is supplied, matching the body of
`modulePullbackComparison`: with any of them left as a metavariable the unifier would have to
unfold that semireducible definition, which it will not do at the transparency used for implicit
arguments. -/
private lemma modulePullbackComparison_hom_fac
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (f : V ⟶ U) (M : modulesOn U) :
    Functor.Fiber.fiberInclusion.map (modulePullbackComparison f M).hom ≫
      Functor.IsPreFibered.pullbackMap (ofModule M).2 f = moduleCartesianMap f M := by
  dsimp only [modulePullbackComparison]
  exact Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _

private lemma modulePullbackComparison_naturality
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (f : V ⟶ U) {M N : modulesOn U} (φ : N ⟶ M) :
    ofModuleMap ((modulePullback f).map φ) ≫ (modulePullbackComparison f N).hom =
      (modulePullbackComparison f M).hom ≫ Functor.pullbackFiberHom (ofModuleMap φ) f := by
  apply Functor.fiber_hom_ext_of_cartesian f (Functor.IsPreFibered.pullbackMap (ofModule N).2 f)
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
  -- The chosen pullback and the inclusion of a fibre are semireducible, so the goal is not
  -- type-correct at the transparency `simp` indexes at and `simp only` makes no progress on it.
  -- Each factorisation is therefore named at the spelling the goal presents it, and the
  -- rewriting is done at `default` transparency with those closed equations.
  have hN := modulePullbackComparison_hom_fac f N
  have hM := modulePullbackComparison_hom_fac f M
  have hpf : Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberHom (ofModuleMap φ) f) ≫
      Functor.IsPreFibered.pullbackMap (ofModule N).2 f =
      Functor.IsPreFibered.pullbackMap (ofModule M).2 f ≫
        Functor.Fiber.fiberInclusion.map (ofModuleMap φ) :=
    Functor.pullbackFiberHom_fac (ofModuleMap φ) f
  have hnat : Functor.Fiber.fiberInclusion.map (ofModuleMap ((modulePullback f).map φ)) ≫
      moduleCartesianMap f N =
      moduleCartesianMap f M ≫ Functor.Fiber.fiberInclusion.map (ofModuleMap φ) :=
    moduleCartesianMap_naturality f φ
  rw (transparency := .default) [Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, hN, hpf, ← Category.assoc, hM]
  exact hnat

/-- Pullback along a composite is the composite of the pullbacks. -/
private noncomputable def modulePullbackCompIso
    {U V W : AlgebraicGeometry.BigFppfOver B S hS} (f : V ⟶ U) (g : W ⟶ V) :
    modulePullback f ⋙ modulePullback g ≅ modulePullback (g ≫ f) := by
  let e := Scheme.Modules.pullbackComp (schemeFunctor.map g) (schemeFunctor.map f) ≪≫
    Scheme.Modules.pullbackCongr (schemeFunctor.map_comp g f).symm
  exact NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (e.app M.obj))
    (fun φ => ObjectProperty.hom_ext _ (e.hom.naturality φ.hom))

private lemma moduleCartesianMap_comp
    {U V W : AlgebraicGeometry.BigFppfOver B S hS} (f : V ⟶ U) (g : W ⟶ V)
    (M : modulesOn U) :
    (ofModuleMap ((modulePullbackCompIso f g).app M).inv).val ≫
        moduleCartesianMap (g ≫ f) M =
      moduleCartesianMap g ((modulePullback f).obj M) ≫ moduleCartesianMap f M := by
  refine comp_eq_of_rawHom_comp _ _ _ _ ?_
  dsimp only [ofModuleMap, moduleCartesianMap]
  simp only [Equiv.apply_symm_apply]
  refine Sigma.ext (by simp [FMap.comp]) (heq_of_eq ?_)
  dsimp [FMap.comp, FMap.id, modulePullbackCompIso, modulePullback]
  -- As in `moduleCartesianMap_naturality`.
  exact moduleUnit_comp_coherence (schemeFunctor.map g) (schemeFunctor.map f) M.obj rfl rfl
    (Category.id_comp _).symm rfl

private lemma modulePullbackComparison_comp
    {U V W : AlgebraicGeometry.BigFppfOver B S hS} (f : V ⟶ U) (g : W ⟶ V)
    (M : modulesOn U) :
    ofModuleMap ((modulePullbackCompIso f g).app M).inv ≫
        (modulePullbackComparison (g ≫ f) M).hom =
      (modulePullbackComparison g ((modulePullback f).obj M)).hom ≫
        Functor.pullbackFiberHom (modulePullbackComparison f M).hom g ≫
          (Functor.pullbackFiberCompIso (ofModule M) f g).hom := by
  apply Functor.fiber_hom_ext_of_cartesian (g ≫ f)
    (Functor.IsPreFibered.pullbackMap (ofModule M).2 (g ≫ f))
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
  -- As in `modulePullbackComparison_naturality`.
  have hq := modulePullbackComparison_hom_fac (g ≫ f) M
  have hg := modulePullbackComparison_hom_fac g ((modulePullback f).obj M)
  have hM := modulePullbackComparison_hom_fac f M
  have hpc : Functor.Fiber.fiberInclusion.map
        (Functor.pullbackFiberCompIso (ofModule M) f g).hom ≫
      Functor.IsPreFibered.pullbackMap (ofModule M).2 (g ≫ f) =
      Functor.IsPreFibered.pullbackMap (Functor.pullbackFiber rawProjection (ofModule M) f).2 g ≫
        Functor.IsPreFibered.pullbackMap (ofModule M).2 f :=
    Functor.pullbackFiberCompIso_hom_fac (ofModule M) f g
  have hpfh : Functor.Fiber.fiberInclusion.map
        (Functor.pullbackFiberHom (modulePullbackComparison f M).hom g) ≫
      Functor.IsPreFibered.pullbackMap (Functor.pullbackFiber rawProjection (ofModule M) f).2 g ≫
        Functor.IsPreFibered.pullbackMap (ofModule M).2 f =
      Functor.IsPreFibered.pullbackMap (ofModule ((modulePullback f).obj M)).2 g ≫
        Functor.Fiber.fiberInclusion.map (modulePullbackComparison f M).hom ≫
          Functor.IsPreFibered.pullbackMap (ofModule M).2 f :=
    Functor.pullbackFiberHom_fac_assoc (modulePullbackComparison f M).hom g _
  have hcomp : Functor.Fiber.fiberInclusion.map
      (ofModuleMap ((modulePullbackCompIso f g).app M).inv) ≫
      moduleCartesianMap (g ≫ f) M =
      moduleCartesianMap g ((modulePullback f).obj M) ≫ moduleCartesianMap f M :=
    moduleCartesianMap_comp f g M
  rw (transparency := .default) [Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, Category.assoc, hq, hpc, hpfh, hM, ← Category.assoc, hg]
  exact hcomp

/-! ### Transition morphisms -/

/-- A morphism of pulled-back modules, read as a morphism of chosen pullbacks in the fibres. -/
private noncomputable def moduleTransition
    {U V W : AlgebraicGeometry.BigFppfOver B S hS} (M : modulesOn U) (N : modulesOn V)
    (f : W ⟶ U) (g : W ⟶ V)
    (φ : (modulePullback g).obj N ⟶ (modulePullback f).obj M) :
    Functor.pullbackFiber rawProjection (ofModule M) f ⟶
      Functor.pullbackFiber rawProjection (ofModule N) g :=
  (modulePullbackComparison f M).inv ≫ ofModuleMap φ ≫
    (modulePullbackComparison g N).hom

private lemma moduleTransition_id
    {U W : AlgebraicGeometry.BigFppfOver B S hS} (M : modulesOn U) (f : W ⟶ U) :
    moduleTransition M M f f (𝟙 _) = 𝟙 _ := by
  simp [moduleTransition, ofModuleMap_id]

private lemma moduleTransition_comp
    {U V Z W : AlgebraicGeometry.BigFppfOver B S hS}
    (M : modulesOn U) (N : modulesOn V) (P : modulesOn Z)
    (f : W ⟶ U) (g : W ⟶ V) (h : W ⟶ Z)
    (φ : (modulePullback g).obj N ⟶ (modulePullback f).obj M)
    (ψ : (modulePullback h).obj P ⟶ (modulePullback g).obj N) :
    moduleTransition M P f h (ψ ≫ φ) =
      moduleTransition M N f g φ ≫ moduleTransition N P g h ψ := by
  simp [moduleTransition, ofModuleMap_comp]

/-- `moduleTransition` is a bijection: it is `ofModuleMap`, a bijection by
`ofModuleMap_bijective`, followed by conjugation with the two chosen pullback comparisons. -/
private lemma moduleTransition_bijective
    {U V W : AlgebraicGeometry.BigFppfOver B S hS} (M : modulesOn U) (N : modulesOn V)
    (f : W ⟶ U) (g : W ⟶ V) :
    Function.Bijective (moduleTransition M N f g) := by
  have h : moduleTransition M N f g =
      (Iso.homCongr (modulePullbackComparison f M) (modulePullbackComparison g N)) ∘
        (ofModuleMap (M := (modulePullback f).obj M) (N := (modulePullback g).obj N)) := rfl
  rw [h]
  exact (Equiv.bijective _).comp
    (ofModuleMap_bijective ((modulePullback f).obj M) ((modulePullback g).obj N))

private lemma ofModuleMap_iso_hom_inv
    {U : AlgebraicGeometry.BigFppfOver B S hS} {M N : modulesOn U} (e : M ≅ N) :
    ofModuleMap e.hom ≫ ofModuleMap e.inv = 𝟙 _ := by
  rw [← ofModuleMap_comp, e.inv_hom_id, ofModuleMap_id]

private lemma ofModuleMap_iso_inv_hom
    {U : AlgebraicGeometry.BigFppfOver B S hS} {M N : modulesOn U} (e : M ≅ N) :
    ofModuleMap e.inv ≫ ofModuleMap e.hom = 𝟙 _ := by
  rw [← ofModuleMap_comp, e.hom_inv_id, ofModuleMap_id]

private lemma moduleTransition_naturality_iff
    {U V W : AlgebraicGeometry.BigFppfOver B S hS} {M M' : modulesOn U} {N N' : modulesOn V}
    (f : W ⟶ U) (g : W ⟶ V) (a : M' ⟶ M) (b : N' ⟶ N)
    (t : (modulePullback g).obj N ⟶ (modulePullback f).obj M)
    (t' : (modulePullback g).obj N' ⟶ (modulePullback f).obj M') :
    (Functor.pullbackFiberHom (ofModuleMap a) f ≫ moduleTransition M' N' f g t' =
      moduleTransition M N f g t ≫ Functor.pullbackFiberHom (ofModuleMap b) g) ↔
      (modulePullback g).map b ≫ t = t' ≫ (modulePullback f).map a := by
  rw [← cancel_epi (modulePullbackComparison f M).hom]
  simp only [moduleTransition, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← modulePullbackComparison_naturality]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← modulePullbackComparison_naturality, ← Category.assoc, ← Category.assoc,
    ← ofModuleMap_comp, ← ofModuleMap_comp, cancel_mono,
    (ofModuleMap_bijective _ _).injective.eq_iff]
  exact eq_comm

private noncomputable def ofModuleIso
    {U : AlgebraicGeometry.BigFppfOver B S hS} {M N : modulesOn U} (e : M ≅ N) :
    ofModule N ≅ ofModule M where
  hom := ofModuleMap e.hom
  inv := ofModuleMap e.inv
  hom_inv_id := ofModuleMap_iso_hom_inv e
  inv_hom_id := ofModuleMap_iso_inv_hom e

/-- The pseudofunctor of sheaves of modules read on the big fppf site over `S`. -/
private noncomputable abbrev restrictedModules :
    Pseudofunctor (LocallyDiscrete (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ) Cat :=
  (schemeFunctor (B := B) (S := S) (hS := hS)).op.toPseudofunctor.comp
    AlgebraicGeometry.modulePullbackPseudofunctor

private lemma restrictedModules_pullHom
    {U V W Z : AlgebraicGeometry.BigFppfOver B S hS} (M : modulesOn U) (N : modulesOn V)
    (f : W ⟶ U) (g : W ⟶ V) (k : Z ⟶ W)
    (φ : (modulePullback f).obj M ⟶ (modulePullback g).obj N) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := restrictedModules) (M₁ := M.obj) (M₂ := N.obj) (f₁ := f) (f₂ := g)
        φ.hom k (k ≫ f) (k ≫ g) rfl rfl =
      (((modulePullbackCompIso f k).app M).inv ≫ (modulePullback k).map φ ≫
        ((modulePullbackCompIso g k).app N).hom).hom :=
  rfl

private lemma moduleTransition_pullHom
    {U V W Z : AlgebraicGeometry.BigFppfOver B S hS} (M : modulesOn U) (N : modulesOn V)
    (f : W ⟶ U) (g : W ⟶ V) (k : Z ⟶ W)
    (φ : (modulePullback g).obj N ⟶ (modulePullback f).obj M) :
    moduleTransition M N (k ≫ f) (k ≫ g)
        (((modulePullbackCompIso g k).app N).inv ≫ (modulePullback k).map φ ≫
          ((modulePullbackCompIso f k).app M).hom) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := Functor.IsFibered.pullbackPseudofunctor rawProjection)
        (M₁ := ofModule M) (M₂ := ofModule N) (f₁ := f) (f₂ := g)
        (moduleTransition M N f g φ) k (k ≫ f) (k ≫ g) rfl rfl := by
  rw [Functor.pullHom_eq]
  have : IsIso (ofModuleMap ((modulePullbackCompIso f k).app M).inv) :=
    (ofModuleIso ((modulePullbackCompIso f k).app M)).isIso_inv
  apply (cancel_epi (ofModuleMap ((modulePullbackCompIso f k).app M).inv ≫
    (modulePullbackComparison (k ≫ f) M).hom)).mp
  conv_rhs => rw [modulePullbackComparison_comp]
  simp only [moduleTransition, ofModuleMap_comp, Category.assoc,
    Iso.hom_inv_id_assoc, Functor.pullbackFiberHom_comp]
  rw [← Category.assoc, ofModuleMap_iso_inv_hom]
  simp only [Category.id_comp]
  rw [modulePullbackComparison_comp]
  rw [← Category.assoc, modulePullbackComparison_naturality]
  simp only [Functor.comp_obj, Category.assoc, Functor.pullbackFiberHom_hom_inv_id_assoc]

/-! ### Descent data on the site compared with the fibres -/

universe w

/-- Descent data on the big fppf site over `S` whose component modules are quasi-coherent. -/
private abbrev restrictedQCohData {I : Type w} {U : AlgebraicGeometry.BigFppfOver B S hS}
    {X : I → AlgebraicGeometry.BigFppfOver B S hS} (f : ∀ i, X i ⟶ U) :=
  (show ObjectProperty (restrictedModules.DescentData f) from
    fun D => ∀ i, (D.obj i).IsQuasicoherent).FullSubcategory

private noncomputable def moduleDescentToFiber
    {I : Type w} {U : AlgebraicGeometry.BigFppfOver B S hS}
    {X : I → AlgebraicGeometry.BigFppfOver B S hS} {f : ∀ i, X i ⟶ U}
    (D : restrictedQCohData f) :
    (Functor.IsFibered.pullbackPseudofunctor rawProjection).DescentData f where
  obj i := ofModule ⟨D.obj.obj i, D.property i⟩
  hom Y q i j a b ha hb := moduleTransition ⟨D.obj.obj i, D.property i⟩
    ⟨D.obj.obj j, D.property j⟩ a b (ObjectProperty.homMk (D.obj.hom q b a hb ha))
  hom_self Y q i a ha := by
    dsimp
    rw [D.obj.hom_self q a ha]
    exact moduleTransition_id _ _
  hom_comp Y q i j l a b c ha hb hc := by
    dsimp
    rw (transparency := .default) [← moduleTransition_comp]
    congr 1
    exact ObjectProperty.hom_ext _ (D.obj.hom_comp q c b a hc hb ha)
  pullHom_hom Y' Y k q q' hq i j a b ha hb ka kb hka hkb := by
    subst ka kb q'
    dsimp
    rw [← moduleTransition_pullHom]
    congr 1
    apply ObjectProperty.hom_ext
    rw [← restrictedModules_pullHom]
    exact D.obj.pullHom_hom k q (k ≫ q) rfl b a hb ha (k ≫ b) (k ≫ a) rfl rfl

private noncomputable def moduleDescentMap
    {I : Type w} {U : AlgebraicGeometry.BigFppfOver B S hS}
    {X : I → AlgebraicGeometry.BigFppfOver B S hS} {f : ∀ i, X i ⟶ U}
    {D E : restrictedQCohData f} (φ : E ⟶ D) :
    moduleDescentToFiber D ⟶ moduleDescentToFiber E where
  hom i := ofModuleMap (ObjectProperty.homMk (φ.hom.hom i))
  comm Y q i j a b ha hb := by
    apply (moduleTransition_naturality_iff _ _ _ _ _ _).mpr
    apply ObjectProperty.hom_ext
    exact φ.hom.comm q b a hb ha

private noncomputable def moduleDescentFunctor
    {I : Type w} {U : AlgebraicGeometry.BigFppfOver B S hS}
    {X : I → AlgebraicGeometry.BigFppfOver B S hS} (f : ∀ i, X i ⟶ U) :
    (restrictedQCohData f)ᵒᵖ ⥤
      (Functor.IsFibered.pullbackPseudofunctor rawProjection).DescentData f where
  obj D := moduleDescentToFiber D.unop
  map φ := moduleDescentMap φ.unop
  map_id D := by
    ext i
    exact ofModuleMap_id _
  map_comp φ ψ := by
    ext i
    exact ofModuleMap_comp _ _

private lemma moduleDescentFunctor_faithful
    {I : Type w} {U : AlgebraicGeometry.BigFppfOver B S hS}
    {X : I → AlgebraicGeometry.BigFppfOver B S hS} (f : ∀ i, X i ⟶ U) :
    (moduleDescentFunctor f).Faithful := by
  constructor
  intro D E φ ψ h
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext i
  exact congrArg (fun a => a.hom) ((ofModuleMap_bijective _ _).injective
    (congrArg (fun a => a.hom i) h))

private lemma moduleDescentFunctor_full
    {I : Type w} {U : AlgebraicGeometry.BigFppfOver B S hS}
    {X : I → AlgebraicGeometry.BigFppfOver B S hS} (f : ∀ i, X i ⟶ U) :
    (moduleDescentFunctor f).Full := by
  constructor
  intro D E ψ
  choose φ hφ using fun i => (ofModuleMap_bijective
    (⟨D.unop.obj.obj i, D.unop.property i⟩ : modulesOn (X i))
    (⟨E.unop.obj.obj i, E.unop.property i⟩ : modulesOn (X i))).surjective (ψ.hom i)
  refine ⟨(ObjectProperty.homMk
    (show E.unop.obj ⟶ D.unop.obj from { hom := fun i => (φ i).hom, comm := ?_ })).op, ?_⟩
  · intro Y q i j a b ha hb
    have hc := ψ.comm q b a hb ha
    simp only [← hφ] at hc
    have hm := (moduleTransition_naturality_iff b a (φ j) (φ i) _ _).mp hc
    exact congrArg (fun m => m.hom) hm
  · ext i
    exact hφ i

/-- Every object of a fibre of `rawProjection` is `ofModule` of a quasi-coherent module on the
underlying scheme. -/
private lemma exists_module_of_fiber {U : AlgebraicGeometry.BigFppfOver B S hS}
    (x : rawProjection.Fiber U) : ∃ M : modulesOn U, ofModule M = x := by
  rcases x with ⟨⟨V, M, hM⟩, hx⟩
  change V = U at hx
  subst U
  exact ⟨⟨M, hM⟩, rfl⟩

/-- `moduleDescentFunctor` is essentially surjective: a descent datum for the pullback
pseudofunctor of `rawProjection` has each of its objects of the form `ofModule`, and each of its
gluing morphisms is `moduleTransition` of a unique morphism of pulled-back modules, by
`moduleTransition_bijective`.  Those morphisms satisfy the three conditions of a descent datum on
the site because `moduleTransition` is injective and takes them to the conditions of the given
datum. -/
private lemma moduleDescentFunctor_essSurj
    {I : Type w} {U : AlgebraicGeometry.BigFppfOver B S hS}
    {X : I → AlgebraicGeometry.BigFppfOver B S hS} (f : ∀ i, X i ⟶ U) :
    (moduleDescentFunctor f).EssSurj := by
  classical
  constructor
  rintro ⟨obj, hom, pull, self, comp⟩
  choose M hM using fun i => exists_module_of_fiber (obj i)
  obtain rfl : (fun i => ofModule (M i)) = obj := funext hM
  let D : (Functor.IsFibered.pullbackPseudofunctor rawProjection).DescentData f :=
    ⟨_, hom, pull, self, comp⟩
  let t : ∀ {Y : AlgebraicGeometry.BigFppfOver B S hS} (q : Y ⟶ U) {i j : I}
      (a : Y ⟶ X i) (b : Y ⟶ X j) (_ : a ≫ f i = q) (_ : b ≫ f j = q),
      (modulePullback a).obj (M i) ⟶ (modulePullback b).obj (M j) :=
    fun q i j a b ha hb =>
      (Equiv.ofBijective _ (moduleTransition_bijective (M j) (M i) b a)).symm
        (D.hom q b a hb ha)
  have ht {Y : AlgebraicGeometry.BigFppfOver B S hS} (q : Y ⟶ U) {i j : I}
      (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
      moduleTransition (M j) (M i) b a (t q a b ha hb) = D.hom q b a hb ha :=
    (Equiv.ofBijective _ (moduleTransition_bijective (M j) (M i) b a)).apply_symm_apply _
  have inj {Y : AlgebraicGeometry.BigFppfOver B S hS} {i j : I} (a : Y ⟶ X i) (b : Y ⟶ X j)
      (x y : (modulePullback a).obj (M i) ⟶ (modulePullback b).obj (M j))
      (h : moduleTransition (M j) (M i) b a x = moduleTransition (M j) (M i) b a y) :
      x.hom = y.hom :=
    congrArg (fun k => k.hom) ((moduleTransition_bijective (M j) (M i) b a).injective h)
  let E : restrictedQCohData f := ⟨{
    obj i := (M i).obj
    hom Y q i j a b ha hb := (t q a b ha hb).hom
    hom_self Y q i a ha := by
      refine inj a a _ _ ?_
      rw [ht]
      exact (D.hom_self q a ha).trans (moduleTransition_id (M i) a).symm
    hom_comp Y q i j l a b c ha hb hc := by
      change (t q a b ha hb ≫ t q b c hb hc).hom = (t q a c ha hc).hom
      refine inj a c _ _ ?_
      rw [moduleTransition_comp, ht, ht, ht]
      exact D.hom_comp q c b a hc hb ha
    pullHom_hom Y' Y k q q' hq i j a b ha hb ka kb hka hkb := by
      subst ka kb q'
      rw [restrictedModules_pullHom]
      refine inj (k ≫ a) (k ≫ b) _ _ ?_
      rw [moduleTransition_pullHom, ht, ht]
      exact D.pullHom_hom k q (k ≫ q) rfl b a hb ha (k ≫ b) (k ≫ a) rfl rfl
    }, fun i => (M i).property⟩
  refine ⟨Opposite.op E, ⟨Pseudofunctor.DescentData.isoMk (fun i => Iso.refl _) ?_⟩⟩
  intro Y q i j a b ha hb
  change Functor.pullbackFiberHom (𝟙 (ofModule (M i))) a ≫ D.hom q a b ha hb =
    moduleTransition (M i) (M j) a b (t q b a hb ha) ≫
      Functor.pullbackFiberHom (𝟙 (ofModule (M j))) b
  simp only [Functor.pullbackFiberHom_id, Category.comp_id]
  exact (Category.id_comp _).trans (ht q b a hb ha).symm

private lemma moduleDescentFunctor_isEquivalence
    {I : Type w} {U : AlgebraicGeometry.BigFppfOver B S hS}
    {X : I → AlgebraicGeometry.BigFppfOver B S hS} (f : ∀ i, X i ⟶ U) :
    (moduleDescentFunctor f).IsEquivalence := by
  have := moduleDescentFunctor_faithful f
  have := moduleDescentFunctor_full f
  have := moduleDescentFunctor_essSurj f
  exact {}

/-! ### The comparison of iterated pullbacks -/

private noncomputable def modulePullbackCompIso'
    {U V W : AlgebraicGeometry.BigFppfOver B S hS}
    (f : V ⟶ U) (g : W ⟶ V) (q : W ⟶ U) (h : g ≫ f = q) :
    modulePullback f ⋙ modulePullback g ≅ modulePullback q :=
  modulePullbackCompIso f g ≪≫ eqToIso (congrArg modulePullback h)

private lemma modulePullbackComparison_comp'
    {U V W : AlgebraicGeometry.BigFppfOver B S hS}
    (f : V ⟶ U) (g : W ⟶ V) (q : W ⟶ U) (h : g ≫ f = q)
    (M : modulesOn U) :
    ofModuleMap ((modulePullbackCompIso' f g q h).app M).inv ≫
        (modulePullbackComparison q M).hom =
      (modulePullbackComparison g ((modulePullback f).obj M)).hom ≫
        Functor.pullbackFiberHom (modulePullbackComparison f M).hom g ≫
          (Functor.pullbackFiberCompIso' (ofModule M) f g q h).hom := by
  subst q
  simpa [modulePullbackCompIso', Functor.pullbackFiberCompIso'_rfl]
    using modulePullbackComparison_comp f g M

private lemma modulePullbackCompIso'_hom
    {U V W : AlgebraicGeometry.BigFppfOver B S hS}
    (f : V ⟶ U) (g : W ⟶ V) (q : W ⟶ U) (h : g ≫ f = q)
    (M : modulesOn U) :
    ((modulePullbackCompIso' f g q h).app M).hom.hom =
      (restrictedModules.mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).inv.toNatTrans.app M.obj := by
  subst q
  rfl

private lemma modulePullbackCompIso'_inv
    {U V W : AlgebraicGeometry.BigFppfOver B S hS}
    (f : V ⟶ U) (g : W ⟶ V) (q : W ⟶ U) (h : g ≫ f = q)
    (M : modulesOn U) :
    ((modulePullbackCompIso' f g q h).app M).inv.hom =
      (restrictedModules.mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).hom.toNatTrans.app M.obj := by
  subst q
  rfl

private lemma modulePullbackCompIso'_hom_comp_inv
    {U V W Z : AlgebraicGeometry.BigFppfOver B S hS}
    (f : V ⟶ U) (g : W ⟶ U) (a : Z ⟶ V) (b : Z ⟶ W)
    (q : Z ⟶ U) (ha : a ≫ f = q) (hb : b ≫ g = q) (M : modulesOn U) :
    ((modulePullbackCompIso' g b q hb).app M).hom ≫
      ((modulePullbackCompIso' f a q ha).app M).inv =
    ObjectProperty.homMk
      ((restrictedModules.mapComp' g.op.toLoc b.op.toLoc q.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hb])).inv.toNatTrans.app M.obj ≫
        (restrictedModules.mapComp' f.op.toLoc a.op.toLoc q.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ha])).hom.toNatTrans.app
            M.obj) := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    modulePullbackCompIso'_hom, modulePullbackCompIso'_inv]
  rfl

private lemma moduleCanonicalComparison
    {U V W Z : AlgebraicGeometry.BigFppfOver B S hS}
    (M : modulesOn U) (f : V ⟶ U) (g : W ⟶ U) (a : Z ⟶ V) (b : Z ⟶ W)
    (q : Z ⟶ U) (ha : a ≫ f = q) (hb : b ≫ g = q) :
    Functor.pullbackFiberHom (modulePullbackComparison f M).hom a ≫
        (Functor.pullbackFiberCompIso' (ofModule M) f a q ha).hom ≫
        (Functor.pullbackFiberCompIso' (ofModule M) g b q hb).inv =
      moduleTransition ((modulePullback f).obj M) ((modulePullback g).obj M) a b
        (((modulePullbackCompIso' g b q hb).app M).hom ≫
          ((modulePullbackCompIso' f a q ha).app M).inv) ≫
        Functor.pullbackFiberHom (modulePullbackComparison g M).hom b := by
  apply (cancel_epi (modulePullbackComparison a ((modulePullback f).obj M)).hom).mp
  simp only [moduleTransition, ofModuleMap_comp, Category.assoc, Iso.hom_inv_id_assoc]
  have hf := modulePullbackComparison_comp' f a q ha M
  have hg := modulePullbackComparison_comp' g b q hb M
  rw [← reassoc_of% hf]
  have : IsIso (ofModuleMap ((modulePullbackCompIso' f a q ha).app M).inv) :=
    (ofModuleIso ((modulePullbackCompIso' f a q ha).app M)).isIso_inv
  apply (cancel_epi (ofModuleMap ((modulePullbackCompIso' f a q ha).app M).inv)).mpr
  apply (cancel_mono (Functor.pullbackFiberCompIso' (ofModule M) g b q hb).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hg, ← Category.assoc, ofModuleMap_iso_hom_inv, Category.id_comp]

end Stacks.QCoh

end
