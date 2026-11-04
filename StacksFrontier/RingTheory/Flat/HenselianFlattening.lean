module

public import StacksFrontier.RingTheory.EssentialFiniteness.Composition
public import StacksFrontier.RingTheory.Flat.Stratification

/-!
# Flattening in the local case

This file sets up the situation of Stacks Tag 05MK — a local homomorphism of local rings
`A → B` together with a `B`-module `M`, tested against the category of local `A`-algebras with
local structure map — and reduces the local flattening theorem (Stacks Tag 05PG) to two
statements about ideals of `A`.

The flatness condition of Stacks Tag 05ML is the condition of Stacks Tag 05LQ for the ideals
`I' = m_{A'}` and `J = m_B`; it is already available as `Module.IsFlatAtPrimesOver`, so
`Module.FlatAtPointSituation.ConditionOn` is defined as that specialization and the stability of
the condition under a morphism of local `A`-algebras is read off from
`Module.IsFlatAtPrimesOver.baseChange`.

Say that an ideal `J ⊆ A` *flattens* the situation if the condition holds over `A ⧸ J`. Stacks
Tag 05PG asserts that the functor `F_lf` of Stacks Tag 05MK is corepresented by `A ⧸ I` for some
ideal `I`, i.e. that the condition over a local `A`-algebra `R` holds exactly when `I` dies in
`R`. Granting that the flattening ideals are closed under arbitrary intersections and that the
kernel of a local `A`-algebra satisfying the condition flattens the situation, the corepresenting
ideal is the smallest flattening ideal and the two assertions of Stacks Tag 05PG follow; this is
the content of `Module.FlatAtPointSituation.exists_ideal_conditionOn_iff_map_eq_bot` and
`Module.FlatAtPointSituation.exists_fg_ideal_conditionOn_iff_map_eq_bot`.

The first two of those three statements are a restatement of Stacks Tag 05PG rather than a
reduction of it: they are, together, logically equivalent to the conclusion, as
`Module.FlatAtPointSituation.flattensSInf_and_flattensKer_iff_exists_ideal` in
`StacksFrontier.RingTheory.Flat.FlatteningEquivalence` shows. So nothing in this file proves
Stacks Tag 05PG, and nothing here carries its tag. The third statement is genuine extra content
and is proved in `StacksFrontier.RingTheory.Flat.FlatteningFGApprox`. Stacks Tag 05PG itself is
proved, by the dévissage argument of the source, in
`StacksFrontier.RingTheory.Flat.HenselianFlatteningTheorem`.

## Main definitions

* `LocalAlgCat` is the category `C` of Stacks Tag 05MK: local `A`-algebras with local structure
  map.
* `Module.FlatAtPointSituation` bundles the rings, the map and the module of Stacks Tag 05MK.
* `Module.FlatAtPointSituation.ConditionOn` is the flatness condition of Stacks Tag 05ML, and
  `Module.FlatAtPointSituation.Condition` is its reading on an object of `LocalAlgCat`.
* `Module.FlatAtPointSituation.flatAtPointFunctor` is the functor `F_lf` of Stacks Tag 05MK.
* `Module.FlatAtPointSituation.Flattens` says that the condition holds over `A ⧸ J`, and
  `Module.FlatAtPointSituation.flatteningIdeal` is the smallest such `J`.
* `Module.FlatAtPointSituation.FlattensSInf`, `Module.FlatAtPointSituation.FlattensKer` and
  `Module.FlatAtPointSituation.FlattensFGApprox` are the three statements from which the
  flattening theorem is derived here.

## Main results

* `Module.FlatAtPointSituation.ConditionOn.of_isLocalHom` and
  `Module.FlatAtPointSituation.condition_of_hom`: the condition is stable under a local
  homomorphism of local `A`-algebras, in possibly different universes, and in particular under a
  morphism of the category `C` (Stacks Tag 05MK).
* `Module.FlatAtPointSituation.Flattens.conditionOn`: a flattening ideal which dies in `R`
  forces the condition over `R`; `Module.FlatAtPointSituation.Flattens.mono`: the flattening
  ideals are closed upwards.
* `Module.FlatAtPointSituation.flattens_maximalIdeal`: the maximal ideal flattens the situation,
  because every module over a field is flat; consequently
  `Module.FlatAtPointSituation.flatteningIdeal_ne_top`.
* `Module.FlatAtPointSituation.conditionOn_of_flat`: if `M` is already flat over `A` then the
  condition holds over every local `A`-algebra, so by
  `Module.FlatAtPointSituation.exists_fg_ideal_conditionOn_iff_map_eq_bot_of_flat` the zero ideal
  corepresents `F_lf`. This is the base case of the induction in the source.
* `Module.FlatAtPointSituation.exists_ideal_conditionOn_iff_map_eq_bot` and
  `Module.FlatAtPointSituation.exists_fg_ideal_conditionOn_iff_map_eq_bot`: the conclusion of
  Stacks Tag 05PG, granting `FlattensSInf`, `FlattensKer` and `FlattensFGApprox`.

## Implementation notes

`Flattens J` is phrased with the ideal `(m_A).map (Ideal.Quotient.mk J)` rather than with the
maximal ideal of `A ⧸ J`; the two agree for `J ≠ ⊤` (`maximalIdeal_quotient`), and the former
makes sense, and is the correct hypothesis for `Module.IsFlatAtPrimesOver.baseChange`, without
carrying the properness of `J` around.

The universe of the tested algebras is independent of the universe of `A`: an object of
`LocalAlgCat.{u, x} A` lives in `Type x`, while `A ⧸ J` lives in `Type u`. This is why
`ConditionOn` is stated for an unbundled carrier and why `FlattensKer` carries its own universe
parameter — the ideal produced by the flattening theorem does not depend on the universe in which
the test algebras are taken, but a single statement of the theorem does fix that universe.

## References

* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open CategoryTheory IsLocalRing

open scoped TensorProduct

universe u v w x y

/-- **Stacks Project, Tag 05MK.** An object of the category `C`: a local `A`-algebra whose
structure homomorphism is a local homomorphism of local rings. -/
@[stacks 05MK "objects"]
structure LocalAlgCat (A : Type u) [CommRing A] [IsLocalRing A] where
  /-- The underlying type of the algebra. -/
  carrier : Type v
  /-- The commutative ring structure on the algebra. -/
  [commRing : CommRing carrier]
  /-- The algebra is a local ring. -/
  [isLocalRing : IsLocalRing carrier]
  /-- The `A`-algebra structure. -/
  [algebra : Algebra A carrier]
  /-- The structure homomorphism is local. -/
  [isLocalHom : IsLocalHom (algebraMap A carrier)]

namespace LocalAlgCat

variable {A : Type u} [CommRing A] [IsLocalRing A]

attribute [instance] commRing isLocalRing algebra isLocalHom

/-- An object of the category of local `A`-algebras is read as its underlying type. -/
instance : CoeSort (LocalAlgCat.{u, v} A) (Type v) := ⟨carrier⟩

attribute [coe] carrier

/-- **Stacks Project, Tag 05MK.** A morphism of the category `C`: a local homomorphism of
`A`-algebras. -/
@[ext, stacks 05MK "morphisms"]
structure Hom (R S : LocalAlgCat.{u, v} A) where
  /-- The underlying `A`-algebra homomorphism. -/
  hom : R →ₐ[A] S
  /-- The underlying ring homomorphism is local. -/
  isLocal : IsLocalHom hom.toRingHom

/-- **Stacks Project, Tag 05MK.** Local `A`-algebras and local `A`-algebra homomorphisms form a
category. -/
@[stacks 05MK "the category"]
instance : Category (LocalAlgCat.{u, v} A) where
  Hom := Hom
  id R := { hom := AlgHom.id A R, isLocal := isLocalHom_id R }
  comp f g :=
    { hom := g.hom.comp f.hom
      isLocal := by
        let _ : IsLocalHom f.hom.toRingHom := f.isLocal
        let _ : IsLocalHom g.hom.toRingHom := g.isLocal
        exact RingHom.isLocalHom_comp g.hom.toRingHom f.hom.toRingHom }
  id_comp := by intro R S f; ext; rfl
  comp_id := by intro R S f; ext; rfl
  assoc := by intro R S T U f g h; ext; rfl

/-- The algebra homomorphism underlying a morphism of local `A`-algebras is local. -/
instance hom_isLocal {R S : LocalAlgCat.{u, v} A} (f : R ⟶ S) : IsLocalHom f.hom.toRingHom :=
  f.isLocal

end LocalAlgCat

namespace Module

/-- Every module over the quotient of a local ring by its maximal ideal is flat, that quotient
being a field. -/
theorem flat_of_quotient_maximalIdeal {A : Type u} [CommRing A] [IsLocalRing A] (X : Type x)
    [AddCommGroup X] [Module (A ⧸ maximalIdeal A) X] : Module.Flat (A ⧸ maximalIdeal A) X := by
  have hm : (maximalIdeal A).IsMaximal := maximalIdeal.isMaximal A
  let _ : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  have : Module.Free (A ⧸ maximalIdeal A) X := Module.Free.of_divisionRing (A ⧸ maximalIdeal A) X
  exact Module.Flat.of_free

/-- **Stacks Project, Tag 05MK.** The standing data of the local flattening problem: a local
homomorphism `A → B` of local rings and a `B`-module `M`. -/
@[stacks 05MK "the situation"]
structure FlatAtPointSituation where
  /-- The base local ring. -/
  A : Type u
  /-- The local algebra over the base. -/
  B : Type v
  /-- The module whose base changes are tested for flatness. -/
  M : Type w
  /-- The commutative ring structure on the base. -/
  [commRingA : CommRing A]
  /-- The commutative ring structure on the algebra. -/
  [commRingB : CommRing B]
  /-- The base is a local ring. -/
  [isLocalRingA : IsLocalRing A]
  /-- The algebra is a local ring. -/
  [isLocalRingB : IsLocalRing B]
  /-- The algebra structure on `B`. -/
  [algebraAB : Algebra A B]
  /-- The structure homomorphism `A → B` is local. -/
  [isLocalHomAB : IsLocalHom (algebraMap A B)]
  /-- The additive group structure on the module. -/
  [addCommGroupM : AddCommGroup M]
  /-- The `B`-module structure on the module. -/
  [moduleBM : Module B M]

namespace FlatAtPointSituation

attribute [instance] commRingA commRingB isLocalRingA isLocalRingB algebraAB isLocalHomAB
  addCommGroupM moduleBM

/-- The base ring acts on the module through the algebra. -/
instance moduleAM (S : FlatAtPointSituation.{u, v, w}) : Module S.A S.M :=
  Module.compHom _ (algebraMap S.A S.B)

/-- The action of the base ring on the module is the restriction of the action of the algebra. -/
instance isScalarTowerABM (S : FlatAtPointSituation.{u, v, w}) : IsScalarTower S.A S.B S.M :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- **Stacks Project, Tag 05ML.** The flatness condition on a local `A`-algebra `R`: the base
change of `M` is flat over `R` at every prime of `B ⊗[A] R` containing the extensions of the
maximal ideals of `R` and of `B`. This is the condition of Stacks Tag 05LQ for the ideals
`I' = m_R` and `J = m_B`. -/
@[stacks 05ML]
def ConditionOn (S : FlatAtPointSituation.{u, v, w}) (R : Type x) [CommRing R] [IsLocalRing R]
    [Algebra S.A R] : Prop :=
  Module.IsFlatAtPrimesOver (R := S.A) (S := S.B) (maximalIdeal S.B) (M := S.M) R
    (maximalIdeal R)

/-- **Stacks Project, Tag 05ML.** The flatness condition read on an object of the category `C`
of Stacks Tag 05MK. -/
@[stacks 05ML]
abbrev Condition (S : FlatAtPointSituation.{u, v, w}) (R : LocalAlgCat.{u, x} S.A) : Prop :=
  S.ConditionOn R

/-- The extension of the maximal ideal along a local homomorphism lands in the maximal ideal. -/
theorem map_maximalIdeal_le {R : Type x} {T : Type y} [CommRing R] [CommRing T] [IsLocalRing R]
    [IsLocalRing T] (f : R →+* T) [IsLocalHom f] :
    Ideal.map f (maximalIdeal R) ≤ maximalIdeal T :=
  Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
    rw [Ideal.mem_comap, mem_maximalIdeal]
    exact fun h ↦ (mem_maximalIdeal a).mp ha (IsLocalHom.map_nonunit a h)

/-- **Stacks Project, Tag 05MK.** The flatness condition is preserved by a local homomorphism of
local `A`-algebras. The source and the target may live in different universes. -/
@[stacks 05MK "base-change stability"]
theorem ConditionOn.of_isLocalHom {S : FlatAtPointSituation.{u, v, w}} (R : Type x) (T : Type y)
    [CommRing R] [IsLocalRing R] [Algebra S.A R] [CommRing T] [IsLocalRing T] [Algebra S.A T]
    [Algebra R T] [IsScalarTower S.A R T] [IsLocalHom (algebraMap R T)] (h : S.ConditionOn R) :
    S.ConditionOn T :=
  Module.IsFlatAtPrimesOver.baseChange _ R T _ _ (map_maximalIdeal_le (algebraMap R T)) h

/-- **Stacks Project, Tag 05MK.** The flatness condition is preserved by a morphism of the
category `C` of local `A`-algebras; this is what makes `F_lf` a functor. -/
@[stacks 05MK "base-change stability"]
theorem condition_of_hom (S : FlatAtPointSituation.{u, v, w}) {R T : LocalAlgCat.{u, x} S.A}
    (f : R ⟶ T) (h : S.Condition R) : S.Condition T := by
  let _ : Algebra R T := f.hom.toRingHom.toAlgebra
  have _ : IsScalarTower S.A R T := IsScalarTower.of_algebraMap_eq fun a ↦ (f.hom.commutes a).symm
  have _ : IsLocalHom (algebraMap (R : Type x) (T : Type x)) := f.isLocal
  exact ConditionOn.of_isLocalHom (S := S) R T h

/-- An ideal `J` of `A` *flattens* the situation if the flatness condition holds over `A ⧸ J`.
For `J ≠ ⊤` this is the condition of Stacks Tag 05ML for the local `A`-algebra `A ⧸ J`. -/
def Flattens (S : FlatAtPointSituation.{u, v, w}) (J : Ideal S.A) : Prop :=
  Module.IsFlatAtPrimesOver (R := S.A) (S := S.B) (maximalIdeal S.B) (M := S.M) (S.A ⧸ J)
    ((maximalIdeal S.A).map (Ideal.Quotient.mk J))

/-- A proper ideal of a local ring cuts out a local ring whose maximal ideal is the extension of
the maximal ideal. -/
theorem maximalIdeal_quotient {A : Type u} [CommRing A] [IsLocalRing A] {J : Ideal A}
    (hJ : J ≠ ⊤) :
    haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    haveI : IsLocalRing (A ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    (maximalIdeal A).map (Ideal.Quotient.mk J) = maximalIdeal (A ⧸ J) := by
  have _ : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have _ : IsLocalRing (A ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have _ : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  refine le_antisymm (map_maximalIdeal_le _) ?_
  intro a ha
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal b).mpr fun h ↦
    (mem_maximalIdeal _).mp ha (h.map (Ideal.Quotient.mk J)))

/-- If `J` flattens the situation and `A → R` factors through `A ⧸ J`, the condition holds over
`R` at any ideal containing the extension of the maximal ideal of `A`. -/
private theorem Flattens.isFlatAtPrimesOver_of_comp_eq {S : FlatAtPointSituation.{u, v, w}}
    {J : Ideal S.A} (hJ : S.Flattens J) (R : Type x) [CommRing R] [Algebra S.A R]
    (g : S.A ⧸ J →+* R) (hg : g.comp (Ideal.Quotient.mk J) = algebraMap S.A R) (I : Ideal R)
    (hI : (maximalIdeal S.A).map (algebraMap S.A R) ≤ I) :
    Module.IsFlatAtPrimesOver (R := S.A) (S := S.B) (maximalIdeal S.B) (M := S.M) R I := by
  let _ : Algebra (S.A ⧸ J) R := g.toAlgebra
  have _ : IsScalarTower S.A (S.A ⧸ J) R :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (congrArg (fun f ↦ f a) hg).symm
  refine Module.IsFlatAtPrimesOver.baseChange _ (S.A ⧸ J) R _ _ ?_ hJ
  rwa [Ideal.map_map, show (algebraMap (S.A ⧸ J) R).comp (Ideal.Quotient.mk J) = _ from hg]

/-- If `J` flattens the situation and dies in a local `A`-algebra `R`, then the flatness
condition holds over `R`: the structure map factors through `A ⧸ J`, and the condition is stable
under base change. -/
theorem Flattens.conditionOn {S : FlatAtPointSituation.{u, v, w}} {J : Ideal S.A}
    (hJ : S.Flattens J) (R : Type x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
    [IsLocalHom (algebraMap S.A R)] (hle : J ≤ RingHom.ker (algebraMap S.A R)) :
    S.ConditionOn R :=
  hJ.isFlatAtPrimesOver_of_comp_eq R (Ideal.Quotient.lift J (algebraMap S.A R) fun _ ha ↦ hle ha)
    (RingHom.ext fun _ ↦ rfl) _ (map_maximalIdeal_le _)

/-- The maximal ideal of `A` flattens the situation: the quotient `A ⧸ m_A` is a field, over
which every module is flat. -/
theorem flattens_maximalIdeal (S : FlatAtPointSituation.{u, v, w}) :
    S.Flattens (maximalIdeal S.A) := by
  intro q _ _
  let _ : Algebra (S.A ⧸ maximalIdeal S.A) (S.B ⊗[S.A] (S.A ⧸ maximalIdeal S.A)) :=
    Algebra.TensorProduct.rightAlgebra
  exact flat_of_quotient_maximalIdeal _

/-- **Stacks Project, Tag 05MK.** The functor `F_lf` on the category `C` of local `A`-algebras:
it takes the value a singleton where the flatness condition holds, and the empty set elsewhere.
Functoriality is `condition_of_hom`. -/
@[stacks 05MK "the functor"]
def flatAtPointFunctor (S : FlatAtPointSituation.{u, v, w}) :
    LocalAlgCat.{u, x} S.A ⥤ Type where
  obj R := PLift (S.Condition R)
  map {R T} f := ↾(fun h : PLift (S.Condition R) ↦
    (⟨S.condition_of_hom (R := R) (T := T) f h.down⟩ : PLift (S.Condition T)))
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- If `M` is already flat over `A`, the flatness condition holds over every local `A`-algebra:
the base change of `M` is flat over `R`, and a localization of a flat module stays flat. This is
the base case of the induction in the source's proof of Stacks Tag 05PG. -/
theorem conditionOn_of_flat (S : FlatAtPointSituation.{u, v, w}) [Module.Flat S.A S.M]
    (R : Type x) [CommRing R] [IsLocalRing R] [Algebra S.A R] : S.ConditionOn R := by
  intro q hq _
  have _ : q.IsPrime := hq
  let _ : Algebra R (S.B ⊗[S.A] R) := Algebra.TensorProduct.rightAlgebra
  have _ : IsLocalization (⊥ : Submonoid S.B) S.B := IsLocalization.self bot_le
  have _ : IsLocalizedModule (⊥ : Submonoid S.B) (LinearMap.id (R := S.B) (M := S.M)) :=
    isLocalizedModule_id (⊥ : Submonoid S.B) S.M S.B
  exact Module.Flat.localizedModule_baseChange (R := S.A) (A := S.B) (R₂ := R)
    (B := S.B ⊗[S.A] R) (N := S.M) (X := S.M) (P := (S.B ⊗[S.A] R) ⊗[S.B] S.M)
    ⊥ LinearMap.id (LinearEquiv.refl _ _) q (by
      rintro _ ⟨z, hz, rfl⟩
      obtain rfl := Submonoid.mem_bot.mp hz
      rw [map_one]
      exact q.primeCompl.one_mem)

/-- **Stacks Project, Tag 05PG** for a module which is already flat over the base: the zero
ideal, which is finitely generated, corepresents the flatness condition. -/
theorem exists_fg_ideal_conditionOn_iff_map_eq_bot_of_flat (S : FlatAtPointSituation.{u, v, w})
    [Module.Flat S.A S.M] :
    ∃ I : Ideal S.A, I.FG ∧ ∀ R : LocalAlgCat.{u, x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ :=
  ⟨⊥, Submodule.fg_bot, fun R ↦ ⟨fun _ ↦ Ideal.map_bot, fun _ ↦ S.conditionOn_of_flat R⟩⟩

/-- The flattening ideals are closed upwards: a larger ideal flattens the situation as well,
because `A ⧸ J → A ⧸ J'` is a morphism of local `A`-algebras. -/
theorem Flattens.mono {S : FlatAtPointSituation.{u, v, w}} {J J' : Ideal S.A} (hJ : S.Flattens J)
    (h : J ≤ J') : S.Flattens J' :=
  hJ.isFlatAtPrimesOver_of_comp_eq (S.A ⧸ J') (Ideal.Quotient.factor h) (RingHom.ext fun _ ↦ rfl) _
    le_rfl

/-- Every ideal flattens the situation over the zero ring, there being no primes to test. -/
theorem flattens_top (S : FlatAtPointSituation.{u, v, w}) : S.Flattens ⊤ :=
  S.flattens_maximalIdeal.mono le_top

/-- The smallest flattening ideal, if the flattening ideals are closed under intersections. -/
def flatteningIdeal (S : FlatAtPointSituation.{u, v, w}) : Ideal S.A :=
  sInf {J | S.Flattens J}

/-- The smallest flattening ideal is contained in the maximal ideal, so `A ⧸ I` is again an
object of the category `C`. -/
theorem flatteningIdeal_le_maximalIdeal (S : FlatAtPointSituation.{u, v, w}) :
    S.flatteningIdeal ≤ maximalIdeal S.A :=
  sInf_le S.flattens_maximalIdeal

/-- The smallest flattening ideal is a proper ideal. -/
theorem flatteningIdeal_ne_top (S : FlatAtPointSituation.{u, v, w}) : S.flatteningIdeal ≠ ⊤ :=
  fun h ↦ (maximalIdeal.isMaximal S.A).ne_top
    (top_le_iff.mp (h ▸ S.flatteningIdeal_le_maximalIdeal))

/-- **The first missing ingredient of Stacks Tag 05PG.** The flattening ideals are closed under
arbitrary nonempty intersections. Equivalently, the smallest flattening ideal flattens the
situation. -/
def FlattensSInf (S : FlatAtPointSituation.{u, v, w}) : Prop :=
  ∀ 𝒥 : Set (Ideal S.A), 𝒥.Nonempty → (∀ J ∈ 𝒥, S.Flattens J) → S.Flattens (sInf 𝒥)

/-- **The second missing ingredient of Stacks Tag 05PG.** If the flatness condition holds over a
local `A`-algebra `R`, then the kernel of `A → R` flattens the situation. -/
def FlattensKer (S : FlatAtPointSituation.{u, v, w}) : Prop :=
  ∀ (R : Type x) [CommRing R] [IsLocalRing R] [Algebra S.A R] [IsLocalHom (algebraMap S.A R)],
    S.ConditionOn R → S.Flattens (RingHom.ker (algebraMap S.A R))

/-- **The third missing ingredient of Stacks Tag 05PG**, needed only for the finite generation
of the flattening ideal: a flattening ideal contains a finitely generated flattening ideal. -/
def FlattensFGApprox (S : FlatAtPointSituation.{u, v, w}) : Prop :=
  ∀ I : Ideal S.A, S.Flattens I → ∃ J ≤ I, J.FG ∧ S.Flattens J

/-- The smallest flattening ideal flattens the situation, granting `FlattensSInf`. -/
theorem flattens_flatteningIdeal {S : FlatAtPointSituation.{u, v, w}} (h : S.FlattensSInf) :
    S.Flattens S.flatteningIdeal :=
  h _ ⟨maximalIdeal S.A, S.flattens_maximalIdeal⟩ fun _ hJ ↦ hJ

/-- Granting `FlattensSInf` and `FlattensKer`, the smallest flattening ideal corepresents the
flatness condition: the condition holds over a local `A`-algebra `R` exactly when the smallest
flattening ideal dies in `R`. -/
theorem conditionOn_iff_map_flatteningIdeal_eq_bot {S : FlatAtPointSituation.{u, v, w}}
    (h₁ : S.FlattensSInf) (h₂ : S.FlattensKer.{u, v, w, x}) (R : Type x) [CommRing R]
    [IsLocalRing R] [Algebra S.A R] [IsLocalHom (algebraMap S.A R)] :
    S.ConditionOn R ↔ Ideal.map (algebraMap S.A R) S.flatteningIdeal = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  refine ⟨fun h ↦ sInf_le (h₂ R h), fun h ↦ (flattens_flatteningIdeal h₁).conditionOn R h⟩

/-- **Stacks Project, Tag 05PG**, granting the two missing ingredients. There is an ideal
`I ⊆ A` such that for every local `A`-algebra `R` with local structure map, the flatness
condition over `R` holds exactly when `I` dies in `R`; that is, `A ⧸ I` corepresents `F_lf`. -/
theorem exists_ideal_conditionOn_iff_map_eq_bot (S : FlatAtPointSituation.{u, v, w})
    (h₁ : S.FlattensSInf) (h₂ : S.FlattensKer.{u, v, w, x}) :
    ∃ I : Ideal S.A, ∀ R : LocalAlgCat.{u, x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ :=
  ⟨S.flatteningIdeal, fun R ↦ conditionOn_iff_map_flatteningIdeal_eq_bot h₁ h₂ R⟩

/-- **Stacks Project, Tag 05PG**, finite generation, granting the three missing ingredients. The
corepresenting ideal may be taken finitely generated. -/
theorem exists_fg_ideal_conditionOn_iff_map_eq_bot (S : FlatAtPointSituation.{u, v, w})
    (h₁ : S.FlattensSInf) (h₂ : S.FlattensKer.{u, v, w, x}) (h₃ : S.FlattensFGApprox) :
    ∃ I : Ideal S.A, I.FG ∧ ∀ R : LocalAlgCat.{u, x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  obtain ⟨J, hJle, hJfg, hJ⟩ := h₃ _ (flattens_flatteningIdeal h₁)
  have : S.flatteningIdeal = J := le_antisymm (sInf_le hJ) hJle
  exact ⟨S.flatteningIdeal, this ▸ hJfg,
    fun R ↦ conditionOn_iff_map_flatteningIdeal_eq_bot h₁ h₂ R⟩

end FlatAtPointSituation

end Module

end
