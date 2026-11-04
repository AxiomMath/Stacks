module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.LocalRing.Quotient
public import StacksFrontier.Homology.Perfect.SystemDuality
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.FiniteDual
public import StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality
public import StacksFrontier.RingTheory.Dualizing.NormalizedFiniteMap
import all StacksFrontier.Homology.Perfect.SystemDuality

/-!
# Quotients by finite-length ideals and dualizing complexes

Let `A` be a Noetherian local ring with a normalized dualizing complex `ω_A`, let `E` be an
injective hull of the residue field, and let `I` be an ideal of finite length contained in the
maximal ideal. Applying `RHom_A(-, ω_A)` to the short exact sequence `0 → I → A → A/I → 0`
produces a distinguished triangle

`ω_{A/I} → ω_A → Hom_A(I, E)[0] → ω_{A/I}[1]`

in `D(A)`, whose first term is a normalized dualizing complex for `A/I`.

## Main results

* `Dualizing.exists_distTriang_normalizedDualizing_quotient_finiteLengthIdeal` produces the
  normalized dualizing complex of the quotient together with the displayed triangle over `A`.

## Implementation notes

The normalized dualizing complex of the quotient is `RHom_A(A/I, ω_A)`, which is normalized by
[stacks 0A7N]; the third term is identified by Matlis duality on finite-length modules,
[stacks 0A7Q]. The complex over `A/I` is viewed in `D(A)` by derived restriction of scalars,
and the degree-zero object `Hom_A(I, E)[0]` is the single complex on the `A`-linear maps
`I →ₗ[A] E`. The residue field is universe-lifted into the module category of its injective
hull. The four maps and objects of the displayed triangle are retained explicitly by
`CategoryTheory.Pretriangulated.Triangle.mk`.

## References

* [Stacks Project, Tag 0A7S](https://stacks.math.columbia.edu/tag/0A7S)
* [Stacks Project, Tag 0A7Q](https://stacks.math.columbia.edu/tag/0A7Q)
* [Stacks Project, Tag 0A7N](https://stacks.math.columbia.edu/tag/0A7N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated MonoidalCategory
open StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

universe u v w x

namespace Dualizing

/-- The `A`-linear maps out of the target of a ring homomorphism are the coextension of
scalars along it, read back as an `A`-module by restriction of scalars. -/
private noncomputable def coextendRestrictTermIso {A B : Type u}
    [CommRing A] [CommRing B] (q : A →+* B)
    (M : ModuleCat.{max v u} A) :
    ModuleCat.of A (((ModuleCat.restrictScalars q).obj (ModuleCat.of B B)) →ₗ[A] M) ≅
      (ModuleCat.restrictScalars q).obj ((ModuleCat.coextendScalars q).obj M) := by
  let e :
      (((ModuleCat.restrictScalars q).obj (ModuleCat.of B B)) →ₗ[A] M) ≃ₗ[A]
        (ModuleCat.restrictScalars q).obj ((ModuleCat.coextendScalars q).obj M) :=
    { toFun := id, invFun := id, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := by intros; rfl,
      map_smul' := by
        intro a g
        apply ModuleCat.CoextendScalars.ext
        apply LinearMap.ext
        intro b
        change B at b
        change a • g b = g (b * q a)
        rw [mul_comm, ← smul_eq_mul]
        exact (g.map_smul a b).symm }
  exact e.toModuleIso

attribute [local implicit_reducible] CochainComplex.HomComplexR
  cochainFromSingleLinearEquiv coextendRestrictTermIso

/-- The Hom complex out of the universe-lifted target of a ring homomorphism, placed in degree
zero, is the degreewise coextension of scalars read back over the source ring. -/
private noncomputable def homSingleCoextendIso {A B : Type u}
    [CommRing A] [CommRing B] (q : A →+* B)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    CochainComplex.HomComplexR A
      ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).obj
        ((ModuleCat.uliftFunctor.{v} A).obj
          ((ModuleCat.restrictScalars q).obj (ModuleCat.of B B)))) J ≅
      ((ModuleCat.coextendScalars q ⋙ ModuleCat.restrictScalars q).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n =>
    (cochainFromSingleLinearEquiv
      ((ModuleCat.uliftFunctor.{v} A).obj
        ((ModuleCat.restrictScalars q).obj (ModuleCat.of B B))) J n).toModuleIso ≪≫
    (LinearEquiv.congrLeft (J.X n) A
      (ULift.moduleEquiv (R := A)
        (M := (ModuleCat.restrictScalars q).obj (ModuleCat.of B B)))).toModuleIso ≪≫
    coextendRestrictTermIso q (J.X n)) ?_
  intro i j hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro b
  obtain ⟨f, rfl⟩ :=
    CochainComplex.HomComplex.Cochain.fromSingleMk_surjective z i (zero_add i)
  simp [cochainFromSingleLinearEquiv, coextendRestrictTermIso,
    CochainComplex.HomComplex.Cochain.δ_fromSingleMk]
  rfl

/-- Pulling a K-injective complex back along the universe-lift equivalence of module categories
preserves K-injectivity. -/
private lemma isKInjective_inverseUlift {A : Type u} [CommRing A]
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v}
        A).inverse.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) := by
  let e := StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v} A
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    e.inverse e.functor e.toAdjunction J

/-- Transporting cochains along the universe-lift equivalence of module categories is an
`A`-linear equivalence. -/
private noncomputable def cochainScalarLinearEquiv {A : Type u} [CommRing A]
    (K L : CochainComplex (ModuleCat.{max v u} (ULift.{v} A)) ℤ) (n : ℤ) :
    ((StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v} A).functor.obj
      (ModuleCat.of (ULift.{v} A) (CochainComplex.HomComplex.Cochain K L n))) ≃ₗ[A]
      CochainComplex.HomComplex.Cochain
        (((StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v}
          A).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)
        (((StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v}
          A).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) n := by
  let F := (StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v} A).functor
  refine { toFun := fun z => z.map F,
           invFun := fun z => CochainComplex.HomComplex.Cochain.mk
             (fun p q h => F.preimage (z.v p q h)),
           left_inv := ?_, right_inv := ?_, map_add' := ?_, map_smul' := ?_ }
  · intro z w
    exact CochainComplex.HomComplex.Cochain.map_add z w F
  · intro a z
    ext p q h
    rfl
  · intro z
    change CochainComplex.HomComplex.Cochain K L n at z
    change CochainComplex.HomComplex.Cochain.mk
      (fun p q h => F.preimage ((z.map F).v p q h)) = z
    ext p q h
    simp only [CochainComplex.HomComplex.Cochain.mk_v,
      CochainComplex.HomComplex.Cochain.map_v, F.preimage_map]
  · intro z
    ext p q h
    simp only [CochainComplex.HomComplex.Cochain.mk_v,
      CochainComplex.HomComplex.Cochain.map_v, F.map_preimage]

/-- The universe-lift equivalence of module categories commutes with forming Hom complexes. -/
private noncomputable def homComplexScalarIso {A : Type u} [CommRing A]
    (K L : CochainComplex (ModuleCat.{max v u} (ULift.{v} A)) ℤ) :
    (((StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v}
      A).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (CochainComplex.HomComplexR (ULift.{v} A) K L)) ≅
      CochainComplex.HomComplexR A
        (((StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v}
          A).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)
        (((StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v}
          A).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) := by
  let F := (StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v} A).functor
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (cochainScalarLinearEquiv K L n).toModuleIso) ?_
  intro i j hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (CochainComplex.HomComplex.δ i j z).map F =
    CochainComplex.HomComplex.δ i j (z.map F)
  exact (CochainComplex.HomComplex.δ_map i j z F).symm

/-- Derived Hom over a ring, evaluated on complexes transported from the lifted scalars and a
K-injective target, is computed by the ordinary Hom complex. -/
private noncomputable def derivedHomModelIsoLifted {A : Type u} [CommRing A]
    (L J : CochainComplex (ModuleCat.{max v u} (ULift.{v} A)) ℤ) [J.IsKInjective] :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u,v,max u v + 1} A).hom.obj
      (Opposite.op ((StacksDraft.DerivedHom.derivedScalarEquivalence.{u,v,max u v + 1}
        A).functor.obj
        (DerivedCategory.Q.obj L)),
        (StacksDraft.DerivedHom.derivedScalarEquivalence.{u,v,max u v + 1} A).functor.obj
          (DerivedCategory.Q.obj J)) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR A
        (((StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v}
          A).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)
        (((StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v}
          A).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J)) := by
  let e := StacksDraft.DerivedHom.derivedScalarEquivalence.{u,v,max u v + 1} A
  let m := StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v} A
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionULift.{u,v,max u v + 1} (R := A)
  exact (StacksDraft.DerivedHom.derivedHomULiftIso.{u,v,max u v + 1} A).app
      (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj J) ≪≫
    e.functor.mapIso (d.homIso L J) ≪≫
    m.functor.mapDerivedCategoryFactors.app (CochainComplex.HomComplexR (ULift.{v} A) L J) ≪≫
    DerivedCategory.Q.mapIso (homComplexScalarIso L J)

/-- Derived Hom over a ring, at a K-injective target, is computed by the ordinary Hom complex. -/
private noncomputable def derivedHomModelIsoOverRing {A : Type u} [CommRing A]
    (L J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective] :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u,v,max u v + 1} A).hom.obj
      (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj J) ≅
        DerivedCategory.Q.obj (CochainComplex.HomComplexR A L J) := by
  let m := StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max v u,v} A
  let e := StacksDraft.DerivedHom.derivedScalarEquivalence.{u,v,max u v + 1} A
  let mc := m.mapHomologicalComplex (ComplexShape.up ℤ)
  let L' := mc.inverse.obj L
  let J' := mc.inverse.obj J
  letI : CochainComplex.IsKInjective J' := isKInjective_inverseUlift J
  let bL : e.functor.obj (DerivedCategory.Q.obj L') ≅ DerivedCategory.Q.obj L :=
    m.functor.mapDerivedCategoryFactors.app L' ≪≫
      DerivedCategory.Q.mapIso (mc.counitIso.app L)
  let bJ : e.functor.obj (DerivedCategory.Q.obj J') ≅ DerivedCategory.Q.obj J :=
    m.functor.mapDerivedCategoryFactors.app J' ≪≫
      DerivedCategory.Q.mapIso (mc.counitIso.app J)
  exact (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u,v,max u v + 1} A).hom.mapIso
      (bL.op.prod bJ.symm) ≪≫ derivedHomModelIsoLifted L' J'

/-- Matlis duality of an ideal is insensitive to universe-lifting the ideal. -/
private def matlisDualULiftIso {A : Type u} [CommRing A]
    (I : Ideal A) (E : ModuleCat.{max v u} A) :
    ModuleCat.of A (ULift.{v} I →ₗ[A] E) ≅ ModuleCat.of A (I →ₗ[A] E) :=
  (LinearEquiv.congrLeft E A (ULift.moduleEquiv (R := A) (M := I))).toModuleIso

/-- Derived Hom out of the monoidal unit is the identity. -/
private noncomputable def homUnitIso {R : Type x} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{x} R)] (d : StacksDraft.DerivedHom.DerivedHomData R)
    (K : DerivedCategory (ModuleCat.{x} R)) :
    d.hom.obj
      (Opposite.op (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{x} R) ℤ))), K) ≅ K := by
  let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{x} R) ℤ))
  let H := d.hom.obj (Opposite.op U, K)
  let e := d.tensorRightUnitor
  let ev := d.evaluation U K
  let h : H ⟶ K := (e.app H).inv ≫ ev
  let g : K ⟶ H := (d.homEquiv K U K).symm (e.app K).hom
  refine ⟨h, g, ?_, ?_⟩
  · apply (d.homEquiv H U K).injective
    rw [d.homEquiv_naturality_left]
    simp only [g, AddEquiv.apply_symm_apply]
    have hn := d.tensorRightUnitor.hom.naturality h
    change d.tensor.map (h, 𝟙 U) ≫ (e.app K).hom = (e.app H).hom ≫ h at hn
    rw [hn]
    simp [h, ev, StacksDraft.DerivedHom.DerivedHomAdjunction.evaluation, H, U]
  · have hn := d.tensorRightUnitor.hom.naturality g
    change d.tensor.map (g, 𝟙 U) ≫ (e.app H).hom = (e.app K).hom ≫ g at hn
    have he := d.homEquiv_naturality_left g (𝟙 H)
    simp only [Category.comp_id] at he
    have hge : g ≫ (e.app H).inv = (e.app K).inv ≫ d.tensor.map (g, 𝟙 U) := by
      apply (Iso.comp_inv_eq (e.app H)).2
      rw [Category.assoc, hn, ← Category.assoc]
      simp
    change g ≫ ((e.app H).inv ≫ ev) = 𝟙 K
    rw [← Category.assoc, hge, Category.assoc]
    change (e.app K).inv ≫ d.tensor.map (g, 𝟙 U) ≫ (d.homEquiv H U K) (𝟙 H) = 𝟙 K
    rw [← he]
    simp [g]

/-- The universe-lifted regular module, read back over the lifted ring, is the monoidal unit. -/
private noncomputable def liftedRegularIso {A : Type u} [CommRing A] :
    (StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max u v,v} A).inverse.obj
      ((ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A A)) ≅
      (𝟙_ (ModuleCat.{max u v} (ULift.{v} A))) := Iso.refl _

/-- The universe-lifted regular module in degree zero, read back over the lifted ring, is the
monoidal unit of complexes. -/
private noncomputable def inverseRegularSingleIso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)] :
    (StacksDraft.DerivedHom.derivedScalarEquivalence.{u,v,w} A).inverse.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        ((ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A A))) ≅
      DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ)) := by
  let F := (StacksDraft.DerivedHom.uliftModuleEquivalence.{u,max u v,v} A).inverse
  exact (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (liftedRegularIso (A := A))

/-- Derived Hom over a ring out of the regular module in degree zero is the identity. -/
private noncomputable def derivedRegularHomIso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u,v,w} A).hom.obj
      (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        ((ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A A))), K) ≅ K := by
  let e := StacksDraft.DerivedHom.derivedScalarEquivalence.{u,v,w} A
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionULift.{u,v,max u v + 1} (R := A)
  let L := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
    ((ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A A))
  let L' := e.inverse.obj L
  let K' := e.inverse.obj K
  let j := inverseRegularSingleIso (A := A)
  exact (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u,v,w} A).hom.mapIso
      ((e.counitIso.app L).op.prod (e.counitIso.app K).symm) ≪≫
    (StacksDraft.DerivedHom.derivedHomULiftIso.{u,v,w} A).app (Opposite.op L', K') ≪≫
    e.functor.mapIso (d.hom.mapIso (j.symm.op.prod (Iso.refl K'))) ≪≫
    e.functor.mapIso (homUnitIso d K') ≪≫ e.counitIso.app K

/-- **Stacks Project, Tag 0A7S.** If `I` is a finite-length ideal contained in the
maximal ideal of a Noetherian local ring `A`, a normalized dualizing complex of `A / I`,
restricted to `A`, fits into a distinguished triangle with the normalized dualizing complex
of `A` and the degree-zero complex on `Hom_A(I, E)`, for any injective hull `E` of the
residue field. -/
@[stacks 0A7S]
theorem exists_distTriang_normalizedDualizing_quotient_finiteLengthIdeal
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (hIfl : IsFiniteLength A I)
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    letI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (lt_of_le_of_lt hI
        (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).lt_top).ne
    letI : IsLocalRing (A ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    ∃ (KB : DerivedCategory (ModuleCat.{max v u} (A ⧸ I))),
      IsNormalizedDualizingComplex KB ∧
        ∃ (f : ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapDerivedCategory).obj KB ⟶ K)
          (g : K ⟶ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
            (ModuleCat.of A (I →ₗ[A] E)))
          (δ : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
              (ModuleCat.of A (I →ₗ[A] E)) ⟶
            (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).obj
              (((ModuleCat.restrictScalars
                (Ideal.Quotient.mk I)).mapDerivedCategory).obj KB)),
          Triangle.mk f g δ ∈ distTriang (DerivedCategory (ModuleCat.{max v u} A)) := by
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (lt_of_le_of_lt hI
      (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).lt_top).ne
  let : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hq : q.Finite := RingHom.Finite.of_surjective q Ideal.Quotient.mk_surjective
  refine ⟨(derivedHom.{u, v, u} q).obj K,
    isNormalizedDualizingComplex_derivedHom q hq K hK, ?_⟩
  let MI : FiniteLengthModules.{u, v} A :=
    ⟨(ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A I),
      (ULift.moduleEquiv (R := A) (M := I)).symm.isFiniteLength hIfl⟩
  let i' : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E := i
  let : Mono i' := by change Mono i; infer_instance
  have hi' : Module.IsInjectiveHull i' := by
    change Module.IsInjectiveHull i
    exact hi
  obtain ⟨eI⟩ := derivedHomFiniteLengthIsoMatlisDual A K hK E i' hi'
  have hDualI := eI.app (Opposite.op MI)
  have hMatlis :
      (matlisDualFiniteLengthFunctor A E).obj (Opposite.op MI) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (I →ₗ[A] E)) := by
    apply (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).mapIso
    exact (ModuleCat.homLinearEquiv (S := A)
      (M := (ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A I))
      (N := E)).toModuleIso ≪≫ matlisDualULiftIso I E
  have hExact : Function.Exact I.subtype I.mkQ := LinearMap.exact_subtype_mkQ I
  let S : ShortComplex (ModuleCat.{max v u} A) := ModuleCat.shortComplexOfConj
    (ULift.moduleEquiv (R := A) (M := I))
    (ULift.moduleEquiv (R := A) (M := A))
    (ULift.moduleEquiv (R := A) (M := A ⧸ I))
    I.subtype I.mkQ hExact.linearMap_comp_eq_zero
  have hS : S.ShortExact :=
    ModuleCat.shortComplexOfConj_shortExact _ _ _ _ _ hExact
      I.subtype_injective I.mkQ_surjective
  have hTri := hS.singleTriangle_distinguished
  obtain ⟨δraw, hRaw⟩ := StacksDraft.Perfect.exists_distinguished_derivedHom_overRing A K _ hTri
  have hIterm :
      (StacksDraft.Perfect.homFunctorOverRing A K).obj
        (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj S.X₁)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (I →ₗ[A] E)) :=
    hDualI ≪≫ hMatlis
  have hA : (StacksDraft.Perfect.homFunctorOverRing A K).obj
      (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj S.X₂)) ≅ K := by
    change (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).hom.obj
      (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        ((ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A A))), K) ≅ K
    exact derivedRegularHomIso K
  have hB : (StacksDraft.Perfect.homFunctorOverRing A K).obj
      (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj S.X₃)) ≅
        ((ModuleCat.restrictScalars q).mapDerivedCategory).obj
          ((derivedHom.{u, v, u} q).obj K) := by
    let hmodel := StacksDraft.DerivedHom.exists_kInjective_model K
    let J := Classical.choose hmodel
    let : CochainComplex.IsKInjective J := (Classical.choose_spec hmodel).1
    let eJ := Classical.choice (Classical.choose_spec hmodel).2
    let L := (CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).obj S.X₃
    let C := ModuleCat.coextendScalars.{u,u,max v u} q
    let R := ModuleCat.restrictScalars.{max v u} q
    exact (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u,v,max u v + 1} A).hom.mapIso
        ((Iso.refl _).op.prod eJ.symm) ≪≫
      derivedHomModelIsoOverRing L J ≪≫
      DerivedCategory.Q.mapIso (homSingleCoextendIso q J) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (C ⋙ R))
          (ComplexShape.up ℤ)).app J) ≪≫
      (R.mapDerivedCategoryFactors.app
        ((C.mapHomologicalComplex (ComplexShape.up ℤ)).obj J)).symm ≪≫
      R.mapDerivedCategory.mapIso (derivedHomObjIsoCoextend.{u, v} q J inferInstance).symm ≪≫
      R.mapDerivedCategory.mapIso ((derivedHom.{u, v, u} q).mapIso eJ)
  let T := Triangle.mk ((StacksDraft.Perfect.homFunctorOverRing A K).map
      (hS.singleTriangle).mor₂.op)
      ((StacksDraft.Perfect.homFunctorOverRing A K).map
        (hS.singleTriangle).mor₁.op) δraw
  obtain ⟨δ, hδ⟩ := CategoryTheory.Pretriangulated.exists_distinguished_of_iso
    (hB.inv ≫ T.mor₁ ≫ hA.hom)
    (hA.inv ≫ T.mor₂ ≫ hIterm.hom)
    T hRaw hB.symm hA.symm hIterm.symm (by simp) (by simp)
  exact ⟨_, _, δ, hδ⟩

end Dualizing

end
