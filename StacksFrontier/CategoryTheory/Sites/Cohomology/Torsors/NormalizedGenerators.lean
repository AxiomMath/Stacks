module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivializationUnit

/-!
# Normalized local generators of a pair on a ringed site

Let `(C, O)` be a ringed site, `L` an invertible `O`-module and `α : L^{⊗ n} ≅ O` a
trivialization of its `n`-th tensor power. The local generators `s` of `L` with
`α(s^{⊗ n}) = 1` — the *normalized* ones, the trivializations of the pair `(L, α)` in the
language of Tag 040Q — form a sheaf of sets. Both defining conditions are local: generating
locally is generating, and the structure sheaf is separated.

## Main definitions

* `Stacks.Cohomology.Torsors.Generators.trivValue` is `α(s^{⊗ n})` for an arbitrary section `s`,
  not only a local generator.
* `Stacks.Cohomology.Torsors.Generators.normalizedSubfunctor` is the subfunctor of the module
  cut out by "local generator with trivialization value one".
* `Stacks.Cohomology.Torsors.Generators.normalizedSheaf` is the resulting sheaf of sets.
* `Stacks.Cohomology.Torsors.Generators.LocalRoots` says that every unit has an `n`-th root of
  its inverse on a covering of every object.
* `Stacks.Cohomology.Torsors.Generators.generatorSieve` is the sieve of arrows whose source
  carries a local generator.
* `Stacks.Cohomology.Torsors.Generators.unitsAdd` and
  `Stacks.Cohomology.Torsors.Generators.unitsAddUnit` read a unit of the structure sheaf as a
  section of the sheaf of units written additively, and back.
* `Stacks.Cohomology.Torsors.Generators.normalizedToGenerator` is the inclusion of the
  normalized local generators into the local generators — the morphism of sheaves of sets that,
  read through Tag 03AJ, carries the class of the torsor of trivializations to the class of the
  torsor of local generators, and so to the class of the invertible module in the Picard group.

## Main results

* `Stacks.Cohomology.Torsors.Generators.trivUnit_val_eq_trivValue`: on a local generator the
  trivialization value is the trivialization unit.
* `Stacks.Cohomology.Torsors.Generators.trivValue_restrict`: the trivialization value commutes
  with restriction.
* `Stacks.Cohomology.Torsors.Generators.mem_normalizedSubfunctor_iff` spells out membership.
* `Stacks.Cohomology.Torsors.Generators.generatorSieve_mem`: on a locally ringed site the
  generator sieve of an invertible module covers, by Tag 0B8Q.
* `Stacks.Cohomology.Torsors.Generators.exists_cover_normalized`: **the normalized local
  generators exist locally**, given local `n`-th roots of units. This is the one place where
  the topology has to be fine enough: a normalized generator over `V` is a generator `s` scaled
  by an `n`-th root of `α(s^{⊗ n})⁻¹`, and such a root exists on a covering exactly because the
  `n`-th power map on the units is locally surjective there.
* `Stacks.Cohomology.Torsors.Generators.localRoots_of_isLocallySurjective`: **local `n`-th roots
  come from local surjectivity of the `n`-th power map on the sheaf of units**, so on a site
  over a scheme the hypothesis of `exists_cover_normalized` is exactly the surjectivity half of
  the Kummer sequence there (Tags 040N and 03PL).

## Implementation notes

The subfunctor is cut out of the module itself rather than out of the sheaf of local generators,
so that its defining condition is a conjunction of two predicates on an arbitrary section: this
is what lets `trivValue` be written before it is known that `s` generates, and so what lets the
two halves of the sheaf condition be proved separately — the first by
`Stacks.Cohomology.Torsors.Generators.generatorSections_of_locally_generator'`, Tag 040E's
statement that generating is local, the second by separatedness of the structure sheaf.

`exists_cover_normalized` builds its covering by `CategoryTheory.Sieve.bind`: first the sieve of
arrows whose source carries a generator, which covers by Tag 0B8Q, then over each of its arrows
the covering on which the trivialization unit of a chosen generator has an `n`-th root. Taking a
sieve rather than a family of arrows for the first step avoids having to transport a chosen
generator along a factorisation through a member of a covering family.

Separatedness is taken from `RingedSite.O` with `forget CommRingCat` rather than from
`Stacks.SheafOfModules.Tensor.ringSheaf` with `forget RingCat`: the composition with the
forgetful functor preserves the sheaf condition only through
`CategoryTheory.Limits.PreservesLimitsOfSize`, which is available at these universes for the
former and not for the latter.

## References

* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerSuccIso tensorProductIso)
open Stacks.SheafOfModules (IsInvertible)

universe u v w

namespace Stacks.Cohomology.Torsors.Generators

variable (X : RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]

/-- The value of a trivialization of the `n`-th tensor power on the `n`-th tensor power of a
section, read as a section of the structure sheaf. -/
noncomputable abbrev trivValue (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : L.val.obj (op U)) : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) :=
  unitVal X U ((al.hom.val.app (op U)).hom (powerSection X L U s n))

/-- The trivialization unit of a local generator is its trivialization value. -/
theorem trivUnit_val_eq_trivValue
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : GeneratorSections' X L U) :
    (trivUnit X L n al U s).val = trivValue X L n al U s.val :=
  trivUnit_val X L n al U s

/-- The trivialization value commutes with restriction. -/
theorem trivValue_restrict (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U V : X.C} (f : V ⟶ U)
    (s : L.val.obj (op U)) :
    trivValue X L n al V (L.val.restrictₛₗ f.op s) =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op (trivValue X L n al U s) := by
  rw [trivValue, ← powerSection_restrict]
  exact congrArg (unitVal X V)
    (PresheafOfModules.naturality_apply al.hom.val f.op (powerSection X L U s n))

/-- The local generators of an invertible module on which a trivialization of the `n`-th tensor
power takes the value one, as a subfunctor of the underlying presheaf of sets. -/
def normalizedSubfunctor (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Subfunctor (L.val.presheaf ⋙ forget AddCommGrpCat) where
  obj U := {s | (∀ (V : X.C) (f : V ⟶ U.unop), Function.Bijective
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • L.val.restrictₛₗ f.op s)) ∧
      trivValue X L n al U.unop s = 1}
  map := by
    intro U V f s hs
    refine ⟨?_, ?_⟩
    · change ∀ (W : X.C) (g : W ⟶ V.unop), Function.Bijective
        (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
          r • L.val.restrictₛₗ g.op (L.val.map f s))
      intro W g
      have heq : (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
            r • L.val.restrictₛₗ g.op (L.val.map f s)) =
          fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
            r • L.val.restrictₛₗ (g ≫ f.unop).op s := by
        funext r
        simp only [op_comp]
        exact congrArg (fun z => r • z) (L.val.map_comp_apply f g.op s).symm
      rw [heq]
      exact hs.1 W (g ≫ f.unop)
    · change trivValue X L n al V.unop (L.val.restrictₛₗ f.unop.op s) = 1
      rw [trivValue_restrict X L n al f.unop s, hs.2, map_one]

/-- A section lies in the normalized subfunctor exactly when it is a local generator and the
trivialization takes the value one on its tensor power. -/
theorem mem_normalizedSubfunctor_iff
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ)
    (s : L.val.obj U) :
    s ∈ (normalizedSubfunctor X L n al).obj U ↔
      (∀ (V : X.C) (f : V ⟶ U.unop), Function.Bijective
        (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
          r • L.val.restrictₛₗ f.op s)) ∧
        trivValue X L n al U.unop s = 1 := Iff.rfl

/-- The sheaf of normalized local generators: a section which is locally a normalized local
generator is one, because generating is local and the structure sheaf is separated. -/
def normalizedSheaf (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Sheaf X.J (Type w) := by
  let G := normalizedSubfunctor X L n al
  have hbase : Presieve.IsSheaf X.J (L.val.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type X.J _).1
      (Presheaf.isSheaf_comp_of_isSheaf X.J L.val.presheaf (forget AddCommGrpCat) L.isSheaf)
  have hring : Presieve.IsSheaf X.J (X.O.obj ⋙ forget CommRingCat.{w}) :=
    (isSheaf_iff_isSheaf_of_type X.J _).1
      (Presheaf.isSheaf_comp_of_isSheaf X.J X.O.obj (forget CommRingCat.{w}) X.O.property)
  have hG : Presieve.IsSheaf X.J G.toFunctor := by
    rw [Subfunctor.isSheaf_iff (G := G) hbase]
    intro U s hs
    have hgenloc : ∀ ⦃V : X.C⦄ (f : V ⟶ U.unop), (G.sieveOfSection s) f →
        ∀ (W : X.C) (g : W ⟶ V), Function.Bijective
          (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
            r • L.val.restrictₛₗ (g ≫ f).op s) := by
      intro V f hf W g
      have hmem : L.val.presheaf.map f.op s ∈ G.obj (op V) := hf
      have hbij := hmem.1 W g
      have hmap : (ConcreteCategory.hom (L.val.presheaf.map f.op)) s =
          L.val.restrictₛₗ f.op s := rfl
      rw [hmap] at hbij
      have heq : (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
            r • L.val.restrictₛₗ g.op (L.val.restrictₛₗ f.op s)) =
          fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
            r • L.val.restrictₛₗ (g ≫ f).op s := by
        funext r
        simp only [PresheafOfModules.restrictₛₗ_apply, op_comp]
        exact congrArg (fun z => r • z) (L.val.map_comp_apply f.op g.op s).symm
      rwa [← heq]
    refine ⟨(generatorSections_of_locally_generator' X L U.unop s
      (G.sieveOfSection s) hs hgenloc).property, ?_⟩
    refine (hring _ hs).isSeparatedFor.ext ?_
    intro V f hf
    have hmem : L.val.presheaf.map f.op s ∈ G.obj (op V) := hf
    have h2 : trivValue X L n al V (L.val.restrictₛₗ f.op s) = 1 := hmem.2
    rw [trivValue_restrict X L n al f s] at h2
    have hone : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op)
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U.unop)) = 1 := by
      rw [map_one]
    exact h2.trans hone.symm
  exact ⟨G.toFunctor, (isSheaf_iff_isSheaf_of_type X.J _).2 hG⟩

/-- Local extraction of `n`-th roots of units on a ringed site: every unit has, on a covering of
every object, an `n`-th root of its inverse. -/
def LocalRoots (n : ℕ) : Prop :=
  ∀ (U : X.C) (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ),
    ∃ S : Sieve U, S ∈ X.J U ∧ ∀ ⦃V : X.C⦄ (f : V ⟶ U), S.arrows f →
      ∃ b : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : Type w)ˣ,
        (b ^ n).val * (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op a.val = 1

/-- The sieve of arrows whose source carries a local generator of the module. -/
def generatorSieve (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) : Sieve U where
  arrows V _ := Nonempty (GeneratorSections' X L V)
  downward_closed := fun {_ _} {_} hf g => ⟨generatorSections_restrict' X L g hf.some⟩

omit [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify X.J AddCommGrpCat] in
/-- An arrow lies in the generator sieve exactly when its source carries a local generator. -/
theorem mem_generatorSieve_iff (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U V : X.C} (f : V ⟶ U) :
    (generatorSieve X L U).arrows f ↔ Nonempty (GeneratorSections' X L V) := Iff.rfl

/-- On a locally ringed site the generator sieve of an invertible module covers. -/
theorem generatorSieve_mem (hX : RingedSite.IsLocallyRinged X)
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L) (U : X.C) :
    generatorSieve X L U ∈ X.J U := by
  obtain ⟨I, W, w, hcov, hgen⟩ := exists_cover_generatorSections' X hX L hL U
  refine X.J.superset_covering ((Sieve.generate_le_iff _ _).2 ?_) hcov
  rintro V f ⟨i⟩
  exact hgen i

/-- **The normalized local generators exist locally.** Given local `n`-th roots of units, every
object of a locally ringed site is covered by objects over which the pair has a normalized local
generator. -/
theorem exists_cover_normalized (hX : RingedSite.IsLocallyRinged X)
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L) (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hroot : LocalRoots X n) (U : X.C) :
    ∃ S : Sieve U, S ∈ X.J U ∧ ∀ ⦃V : X.C⦄ ⦃f : V ⟶ U⦄, S.arrows f →
      Nonempty ((normalizedSubfunctor X L n al).obj (op V)) := by
  let := hL
  let R := fun (V : X.C) (hf : Nonempty (GeneratorSections' X L V)) =>
    hroot V (trivUnit X L n al V hf.some)
  refine ⟨Sieve.bind (generatorSieve X L U).arrows (fun {V} {_} hf => (R V hf).choose),
    X.J.bind_covering (generatorSieve_mem X hX L hL U) (fun {V} {f} hf => (R V hf).choose_spec.1),
    ?_⟩
  rintro W g ⟨V, h, f, hf, hh, rfl⟩
  obtain ⟨b, hb⟩ := (R V hf).choose_spec.2 h hh
  let s : GeneratorSections' X L W := generatorSections_restrict' X L h hf.some
  have hbu : b ^ n * trivUnit X L n al W s = 1 :=
    Units.ext (by rwa [Units.val_mul, trivUnit_restrict X L n al h hf.some])
  let t := generatorSections_smul_unit' X L W b s
  refine ⟨⟨t.val, t.property, ?_⟩⟩
  rw [← trivUnit_val_eq_trivValue X L n al W t, trivUnit_smul_eq_one X L n al W b s hbu]
  rfl

/-- A unit of the structure sheaf as a section of the sheaf of units written additively. -/
abbrev unitsAdd (U : X.C)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ) :
    (unitsAddSheaf X).obj.obj (op U) := Additive.ofMul a

/-- A section of the sheaf of units written additively as a unit of the structure sheaf. -/
abbrev unitsAddUnit (U : X.C) (y : (unitsAddSheaf X).obj.obj (op U)) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ := Additive.toMul y

omit [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify X.J AddCommGrpCat] in
/-- The two readings are mutually inverse. -/
theorem unitsAddUnit_unitsAdd (U : X.C)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ) :
    unitsAddUnit X U (unitsAdd X U a) = a := rfl

omit [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify X.J AddCommGrpCat] in
/-- The `n`-th multiple of a section of the sheaf of units written additively is the `n`-th
power of the corresponding unit. -/
theorem nsmul_unitsAdd (n : ℕ) (U : X.C) (t : (unitsAddSheaf X).obj.obj (op U)) :
    ((n • 𝟙 (unitsAddSheaf X).obj).app (op U)) t =
      unitsAdd X U ((unitsAddUnit X U t) ^ n) := rfl

omit [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify X.J AddCommGrpCat] in
/-- **Local `n`-th roots of units from local surjectivity of the `n`-th power map.** If the
`n`-th power map on the sheaf of units is locally surjective then every unit has an `n`-th root
of its inverse on a covering of every object. -/
theorem localRoots_of_isLocallySurjective (n : ℕ)
    (hsurj : Presheaf.IsLocallySurjective X.J (n • 𝟙 (unitsAddSheaf X).obj)) :
    LocalRoots X n := by
  intro U a
  refine ⟨Presheaf.imageSieve (n • 𝟙 (unitsAddSheaf X).obj) (unitsAdd X U a⁻¹),
    Presheaf.imageSieve_mem X.J _ _, ?_⟩
  rintro V f ⟨t, ht⟩
  refine ⟨unitsAddUnit X V t, ?_⟩
  have h1 : unitsAdd X V ((unitsAddUnit X V t) ^ n) =
      (unitsAddSheaf X).obj.map f.op (unitsAdd X U a⁻¹) := ht
  have h3 : ((unitsAddUnit X V t) ^ n).val =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op
        (a⁻¹ : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ).val :=
    congrArg (fun z => (unitsAddUnit X V z).val) h1
  rw [h3]
  show ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op) ((a⁻¹).val) *
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op) a.val = 1
  rw [← map_mul, Units.inv_mul, map_one]

/-- The inclusion of the normalized local generators into the local generators. -/
def normalizedToGenerator (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (normalizedSheaf X L n al).obj ⟶ (generatorSectionsSheaf' X L).obj where
  app U := ↾(fun s : (normalizedSubfunctor X L n al).obj U => ⟨s.1, s.2.1⟩)
  naturality _ _ _ := rfl

/-- The inclusion does not change the underlying section. -/
theorem normalizedToGenerator_val
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ)
    (s : (normalizedSheaf X L n al).obj.obj U) :
    ((normalizedToGenerator X L n al).app U s).1 = s.1 := rfl

end Stacks.Cohomology.Torsors.Generators

end
