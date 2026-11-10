module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartRingMap
public import StacksFrontier.CategoryTheory.Sites.LeftAdjointLocalLift

/-!
# Locally nilpotent kernels under the direct image along an equivalence of small étale topoi

Let `t : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of the small étale ringed topoi
of two algebraic spaces whose direct image is an equivalence of topoi, and let `φ : 𝒪_X ⟶ ℛ` be
a map of sheaves of commutative rings on the small étale site of `X` whose kernel is locally
nilpotent.  This file proves that the direct image `t_*φ : t_*𝒪_X ⟶ t_*ℛ` again has a locally
nilpotent kernel.

Local nilpotence of the kernel is a property of the topos: it says that the subsheaves
`{a ∈ ker φ | aⁿ = 0}`, `n ∈ ℕ`, cover the kernel, and an equivalence of topoi carries covering
families of subsheaves to covering families of subsheaves.  The proof makes this explicit with
sections.  A section `x` of `t_*𝒪_X` over a chart `V` of `Y` is the adjoint of a map
`t⁻¹h_V ⟶ 𝒪_X`, whose value at a section `s` of `t⁻¹h_V` over a chart `U` of `X` is a ring
homomorphism `ev_s : (t_*𝒪_X)(V) ⟶ 𝒪_X(U)` (`AlgebraicGeometry.Space.inverseImageSectionRingHom'`);
these determine `x`.  If `t_*φ` kills `x` then `φ` kills every `ev_s x`, so locally `ev_s x` is
nilpotent.  The sections of `t⁻¹h_V` at which some power of `ev x` vanishes therefore generate
`t⁻¹h_V` locally, and since `t_*` is a left adjoint (being an equivalence),
`CategoryTheory.Sheaf.exists_locally_lift_of_adjunction` lifts the tautological section of
`t_*t⁻¹h_V` over `V` locally on `V` along that family.  Over a member `q : V' ⟶ V` of the
resulting covering, the inverse image `t⁻¹h_q` factors through a single representable sheaf
classifying a section `s` with `(ev_s x)ⁿ = 0`, so `(ev x)ⁿ` vanishes on all of `t⁻¹h_{V'}`,
which is `(x|_{V'})ⁿ = 0`.

## Main definitions

* `AlgebraicGeometry.Space.KernelIsLocallyNilpotent`: a map of sheaves of commutative rings has
  locally nilpotent kernel when every section it kills is nilpotent on a covering sieve.

## Main results

* `AlgebraicGeometry.Space.kernelIsLocallyNilpotent_pushforward`: the direct image along a
  morphism of small étale ringed topoi whose direct image is an equivalence preserves locally
  nilpotent kernels.
* `AlgebraicGeometry.Space.KernelIsLocallyNilpotent.comp`,
  `AlgebraicGeometry.Space.KernelIsLocallyNilpotent.comp_isIso`,
  `AlgebraicGeometry.Space.KernelIsLocallyNilpotent.of_comp_isIso` and
  `AlgebraicGeometry.Space.KernelIsLocallyNilpotent.of_comp_of_isLocallySurjective`: stability of
  the condition under composition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPushforward

universe u w v

namespace AlgebraicGeometry.Space

section General

variable {C : Type*} [Category C] (J : GrothendieckTopology C)

/-- A map of sheaves of commutative rings **has locally nilpotent kernel** when every section it
kills becomes nilpotent on a covering sieve.  For the structure map of a morphism of ringed
topoi this is `Deformation.ToposThickening.HasLocallyNilpotentKernel`. -/
def KernelIsLocallyNilpotent {R R' : Sheaf J CommRingCat.{w}} (φ : R ⟶ R') : Prop :=
  ∀ (U : Cᵒᵖ) (a : ToType (R.obj.obj U)), φ.hom.app U a = 0 →
    ∃ T : Sieve U.unop, T ∈ J U.unop ∧
      ∀ ⦃V : C⦄ (p : V ⟶ U.unop), T p → IsNilpotent (R.obj.map p.op a)

variable {J}

/-- A map of sheaves commutes with restriction. -/
private theorem hom_app_map_apply {R R' : Sheaf J CommRingCat.{w}} (φ : R ⟶ R') {U V : C}
    (p : V ⟶ U) (a : ToType (R.obj.obj (op U))) :
    φ.hom.app (op V) (R.obj.map p.op a) = R'.obj.map p.op (φ.hom.app (op U) a) :=
  ConcreteCategory.congr_hom (φ.hom.naturality p.op) a

/-- If every restriction of a section along a covering sieve is locally nilpotent, so is the
section. -/
theorem exists_isNilpotent_of_locally {R : Sheaf J CommRingCat.{w}} {U : C}
    (a : ToType (R.obj.obj (op U))) (T : Sieve U) (hT : T ∈ J U)
    (h : ∀ ⦃V : C⦄ (p : V ⟶ U), T p → ∃ T' : Sieve V, T' ∈ J V ∧
      ∀ ⦃W : C⦄ (q : W ⟶ V), T' q → IsNilpotent (R.obj.map (q ≫ p).op a)) :
    ∃ T'' : Sieve U, T'' ∈ J U ∧
      ∀ ⦃W : C⦄ (p : W ⟶ U), T'' p → IsNilpotent (R.obj.map p.op a) := by
  refine ⟨Sieve.bind T.arrows (fun V p hp => (h p hp).choose), J.bind_covering hT
    (fun V p hp => (h p hp).choose_spec.1), ?_⟩
  rintro W _ ⟨V, q, p, hp, hq, rfl⟩
  exact (h p hp).choose_spec.2 q hq

/-- Composites of maps with locally nilpotent kernel have locally nilpotent kernel. -/
theorem KernelIsLocallyNilpotent.comp {R R' R'' : Sheaf J CommRingCat.{w}} {φ : R ⟶ R'}
    {ψ : R' ⟶ R''} (hφ : KernelIsLocallyNilpotent J φ) (hψ : KernelIsLocallyNilpotent J ψ) :
    KernelIsLocallyNilpotent J (φ ≫ ψ) := by
  rintro ⟨U⟩ a ha
  obtain ⟨T, hT, hTa⟩ := hψ (op U) (φ.hom.app (op U) a) ha
  refine exists_isNilpotent_of_locally a T hT fun V p hp => ?_
  obtain ⟨n, hn⟩ := hTa p hp
  have hker : φ.hom.app (op V) (R.obj.map p.op a ^ n) = 0 := by
    rwa [map_pow, hom_app_map_apply]
  obtain ⟨T', hT', hT'a⟩ := hφ (op V) _ hker
  refine ⟨T', hT', fun W q hq => ?_⟩
  obtain ⟨m, hm⟩ := hT'a q hq
  refine ⟨n * m, ?_⟩
  rwa [op_comp, Functor.map_comp, CategoryTheory.comp_apply, pow_mul, ← map_pow]

/-- Composing on the right with an isomorphism does not change the kernel. -/
theorem KernelIsLocallyNilpotent.comp_isIso {R R' R'' : Sheaf J CommRingCat.{w}} {φ : R ⟶ R'}
    (hφ : KernelIsLocallyNilpotent J φ) (e : R' ⟶ R'') [IsIso e] :
    KernelIsLocallyNilpotent J (φ ≫ e) := by
  intro U a ha
  refine hφ U a ?_
  have h2 : φ.hom.app U a = (inv e).hom.app U ((φ ≫ e).hom.app U a) := by
    change _ = ((φ ≫ e) ≫ inv e).hom.app U a
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h2, ha, map_zero]

/-- A map whose composite with an isomorphism has locally nilpotent kernel has locally nilpotent
kernel. -/
theorem KernelIsLocallyNilpotent.of_comp_isIso {R R' R'' : Sheaf J CommRingCat.{w}}
    {φ : R ⟶ R'} (e : R' ⟶ R'') (h : KernelIsLocallyNilpotent J (φ ≫ e)) :
    KernelIsLocallyNilpotent J φ := by
  intro U a ha
  refine h U a ?_
  change e.hom.app U (φ.hom.app U a) = 0
  rw [ha, map_zero]

/-- If `φ` is locally surjective and `φ ≫ ψ` has locally nilpotent kernel, so has `ψ`. -/
theorem KernelIsLocallyNilpotent.of_comp_of_isLocallySurjective
    {R R' R'' : Sheaf J CommRingCat.{w}} {φ : R ⟶ R'} {ψ : R' ⟶ R''}
    (hs : Presheaf.IsLocallySurjective J φ.hom) (h : KernelIsLocallyNilpotent J (φ ≫ ψ)) :
    KernelIsLocallyNilpotent J ψ := by
  rintro ⟨U⟩ b hb
  refine exists_isNilpotent_of_locally b _ (Presheaf.imageSieve_mem J φ.hom b) fun V p hp => ?_
  obtain ⟨a, ha⟩ := hp
  have hker : (φ ≫ ψ).hom.app (op V) a = 0 := by
    change ψ.hom.app (op V) (φ.hom.app (op V) a) = 0
    rw [ha, hom_app_map_apply, hb, map_zero]
  obtain ⟨T, hT, hTa⟩ := h (op V) a hker
  refine ⟨T, hT, fun W q hq => ?_⟩
  have := (hTa q hq).map (φ.hom.app (op W)).hom
  rwa [hom_app_map_apply, ha, ← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
    at this

end General

section Pushforward

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}
  (t : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))

attribute [local instance] smallEtaleTopology_subcanonical

/-- The evaluation of a section `x` of `t_*𝒪_X` over `V` at a section `s` of `t⁻¹h_V`. -/
abbrev pushforwardEval {V : SmallEtale B S hS Y.1} {U : SmallEtale B S hS X.1}
    (s : (invRep t V).obj.obj (op U)) :=
  inverseImageSectionRingHom' t V U s

/-- The evaluation at a restricted section is the restriction of the evaluation. -/
theorem pushforwardEval_restrict {V : SmallEtale B S hS Y.1} {U U' : SmallEtale B S hS X.1}
    (w : U' ⟶ U) (s : (invRep t V).obj.obj (op U))
    (x : ToType (((pushforwardCommRingFunctor t.toToposHom).obj
      (smallEtaleRingedTopos B S hS X).O).obj.obj (op V))) :
    pushforwardEval t ((invRep t V).obj.map w.op s) x =
      (smallEtaleRingedTopos B S hS X).O.obj.map w.op (pushforwardEval t s x) :=
  ConcreteCategory.congr_hom (((t.toToposHom.adj.homEquiv _ _).symm
    ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm x)).hom.naturality w.op) s

/-- The evaluation of a restriction `x|_{V'}` at a section `s` of `t⁻¹h_{V'}` is the evaluation
of `x` at the image of `s` in `t⁻¹h_V`. -/
theorem pushforwardEval_map {V V' : SmallEtale B S hS Y.1} {U : SmallEtale B S hS X.1}
    (q : V' ⟶ V) (s : (invRep t V').obj.obj (op U))
    (x : ToType (((pushforwardCommRingFunctor t.toToposHom).obj
      (smallEtaleRingedTopos B S hS X).O).obj.obj (op V))) :
    pushforwardEval t s
        ((((pushforwardCommRingFunctor t.toToposHom).obj
          (smallEtaleRingedTopos B S hS X).O).obj.map q.op) x) =
      pushforwardEval t ((t.toToposHom.inverseImage.map
        ((SmallEtale.topology B S hS Y.1).yoneda.map q)).hom.app (op U) s) x := by
  change ((t.toToposHom.adj.homEquiv _ _).symm
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm
        ((t.toToposHom.pushforward.obj (Sheaf.ringSheaf (ringO X))).obj.map q.op x))).hom.app
        (op U) s = ((t.toToposHom.adj.homEquiv _ _).symm
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm x)).hom.app (op U)
        ((t.toToposHom.inverseImage.map
          ((SmallEtale.topology B S hS Y.1).yoneda.map q)).hom.app (op U) s)
  have e1 : (SmallEtale.topology B S hS Y.1).yonedaEquiv.symm
      ((t.toToposHom.pushforward.obj (Sheaf.ringSheaf (ringO X))).obj.map q.op x) =
      (SmallEtale.topology B S hS Y.1).yoneda.map q ≫
        (SmallEtale.topology B S hS Y.1).yonedaEquiv.symm x :=
    GrothendieckTopology.yonedaEquiv_symm_map _ q.op x
  refine (congrArg (fun m => ((t.toToposHom.adj.homEquiv _ _).symm m).hom.app (op U) s)
    e1).trans ?_
  rw [Adjunction.homEquiv_naturality_left_symm]
  rfl

/-- A section of `t_*𝒪_X` is determined by its evaluations. -/
theorem pushforwardEval_ext {V : SmallEtale B S hS Y.1}
    {x y : ToType (((pushforwardCommRingFunctor t.toToposHom).obj
      (smallEtaleRingedTopos B S hS X).O).obj.obj (op V))}
    (h : ∀ (U : SmallEtale B S hS X.1) (s : (invRep t V).obj.obj (op U)),
      pushforwardEval t s x = pushforwardEval t s y) : x = y := by
  have h' : (t.toToposHom.adj.homEquiv _ _).symm
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm x) =
      (t.toToposHom.adj.homEquiv _ _).symm
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm y) := by
    apply Sheaf.hom_ext
    ext ⟨U⟩ s
    exact h U s
  exact (SmallEtale.topology B S hS Y.1).yonedaEquiv.symm.injective
    ((t.toToposHom.adj.homEquiv _ _).symm.injective h')

/-- Applying `φ` to an evaluation of a section of `t_*𝒪_X` evaluates its image under `t_*φ`. -/
theorem map_pushforwardEval {R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (φ : (smallEtaleRingedTopos B S hS X).O ⟶ R) {V : SmallEtale B S hS Y.1}
    {U : SmallEtale B S hS X.1} (s : (invRep t V).obj.obj (op U))
    (y : ToType (((pushforwardCommRingFunctor t.toToposHom).obj
      (smallEtaleRingedTopos B S hS X).O).obj.obj (op V))) :
    φ.hom.app (op U) (pushforwardEval t s y) =
      (inverseImageSectionTransport t V U s).app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj R)
        (((pushforwardCommRingFunctor t.toToposHom).map φ).hom.app (op V) y) := by
  have hmap : ((pushforwardCommRingFunctor t.toToposHom).map φ).hom.app (op V) y =
      (t.toToposHom.pushforward.map
        ((smallEtaleRingedTopos B S hS X).forgetRing.map φ)).hom.app (op V) y :=
    congrArg (fun m => (m.hom.app (op V)).hom y)
      (Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap
        (SmallEtale.topology B S hS Y.1) t.toToposHom.pushforward φ)
  rw [hmap]
  exact (types_congr_hom ((inverseImageSectionTransport t V U s).naturality
    ((smallEtaleRingedTopos B S hS X).forgetRing.map φ)) y).symm

/-- **The direct image along an equivalence of small étale topoi preserves locally nilpotent
kernels.**  If `t_*` is an equivalence and `φ : 𝒪_X ⟶ ℛ` has locally nilpotent kernel, so has
`t_*φ : t_*𝒪_X ⟶ t_*ℛ`. -/
theorem kernelIsLocallyNilpotent_pushforward [t.toToposHom.pushforward.IsEquivalence]
    {R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (φ : (smallEtaleRingedTopos B S hS X).O ⟶ R)
    (hφ : KernelIsLocallyNilpotent (SmallEtale.topology B S hS X.1) φ) :
    KernelIsLocallyNilpotent (SmallEtale.topology B S hS Y.1)
      ((pushforwardCommRingFunctor t.toToposHom).map φ) := by
  rintro ⟨V⟩ x hx
  have hker : ∀ (U : SmallEtale B S hS X.1) (s : (invRep t V).obj.obj (op U)),
      φ.hom.app (op U) (pushforwardEval t s x) = 0 := by
    intro U s
    have h0 := map_pushforwardEval t φ s 0
    simp only [map_zero] at h0
    rw [map_pushforwardEval, hx]
    exact h0.symm
  let ι := Σ (U : SmallEtale B S hS X.1),
    {s : (invRep t V).obj.obj (op U) // ∃ n : ℕ, (pushforwardEval t s x) ^ n = 0}
  have hgen : ∀ (W : SmallEtale B S hS X.1) (z : (invRep t V).obj.obj (op W)),
      ∃ T : Sieve W, T ∈ SmallEtale.topology B S hS X.1 W ∧
        ∀ ⦃W' : SmallEtale B S hS X.1⦄ (i : W' ⟶ W), T i →
          ∃ (k : ι) (φ' : W' ⟶ k.1),
            (invRep t V).obj.map φ'.op k.2.1 = (invRep t V).obj.map i.op z := by
    intro W z
    obtain ⟨T, hT, hTn⟩ := hφ (op W) _ (hker W z)
    refine ⟨T, hT, fun W' i hi => ⟨⟨W', (invRep t V).obj.map i.op z, ?_⟩, 𝟙 W', ?_⟩⟩
    · obtain ⟨n, hn⟩ := hTn i hi
      exact ⟨n, by rwa [pushforwardEval_restrict]⟩
    · simp
  let σ : (t.toToposHom.pushforward.obj (invRep t V)).obj.obj (op V) :=
    (SmallEtale.topology B S hS Y.1).yonedaEquiv
      (t.toToposHom.adj.unit.app ((SmallEtale.topology B S hS Y.1).yoneda.obj V))
  obtain ⟨T, hT, hTlift⟩ := Sheaf.exists_locally_lift_of_adjunction
    t.toToposHom.pushforward.asEquivalence.toAdjunction (fun k : ι => k.1)
    (fun k => k.2.1) hgen σ
  refine ⟨T, hT, fun V' q hq => ?_⟩
  obtain ⟨k, s', hs'⟩ := hTlift q hq
  obtain ⟨n, hn⟩ := k.2.2
  refine ⟨n, pushforwardEval_ext t fun U s'' => ?_⟩
  rw [map_pow, map_zero, pushforwardEval_map]
  -- the inverse image of `q` factors through the representable sheaf classifying `k`
  have hfac : t.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map q) =
      (t.toToposHom.adj.homEquiv _ _).symm
          ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm s') ≫
        (SmallEtale.topology B S hS X.1).yonedaEquiv.symm k.2.1 := by
    apply (t.toToposHom.adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
      t.toToposHom.adj.unit_naturality]
    apply (SmallEtale.topology B S hS Y.1).yonedaEquiv.injective
    rw [GrothendieckTopology.yonedaEquiv_comp, GrothendieckTopology.yonedaEquiv_comp]
    simp only [GrothendieckTopology.yonedaEquiv_yoneda_map]
    convert ((GrothendieckTopology.map_yonedaEquiv _ _ q).symm.trans hs'.symm) using 2 <;>
      first | rfl | exact Equiv.apply_symm_apply _ _
  have hs : (t.toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS Y.1).yoneda.map q)).hom.app (op U) s'' =
      (invRep t V).obj.map
        (((t.toToposHom.adj.homEquiv _ _).symm
          ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm s')).hom.app (op U) s'').op
        k.2.1 := by
    rw [hfac]
    rfl
  rw [hs, pushforwardEval_restrict, ← map_pow, hn, map_zero]

end Pushforward

end AlgebraicGeometry.Space

end
