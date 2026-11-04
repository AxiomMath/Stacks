module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact

/-!
# Local generators of a sheaf of modules

A section `s ∈ L(U)` of a sheaf of modules on a ringed space *generates* `L` on `U` when, for
every open `V ⊆ U`, multiplication by `s|_V` is a bijection `𝒪_X(V) → L(V)`. Equivalently
`s` is a trivialization of `L` over `U`. This file develops the elementary calculus of such
sections: two generators on the same open differ by a unique scalar, that scalar is a unit, it
is compatible with restriction, with isomorphisms of modules, and satisfies the cocycle
identity.

This is the bookkeeping that the norm construction of
[Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY) runs on: there the transition
units of a line bundle upstairs are pushed through a norm on functions and the result is glued.
It is also the data of the generator torsor of
[Stacks, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU).

## Main definitions

* `Stacks.SheafOfModules.GeneratorSections`: the sections of `L` trivializing it on an open.
* `Stacks.SheafOfModules.generatorRestrict`: a generator restricts to a generator.
* `Stacks.SheafOfModules.generatorOfIso`: a trivialization supplies a generator.
* `Stacks.SheafOfModules.generatorMapIso`: an isomorphism of modules carries generators to
  generators.
* `Stacks.SheafOfModules.generatorRatio` and `Stacks.SheafOfModules.generatorRatioUnit`: the
  scalar comparing two generators on the same open, and the same scalar remembered as a unit.

## Main results

* `Stacks.SheafOfModules.isUnit_of_smul_eq_generator`: the scalar comparing two generators is a
  unit.
* `Stacks.SheafOfModules.generatorRatio_spec` and
  `Stacks.SheafOfModules.generatorRatio_unique`: the comparison scalar is characterized by the
  equation it satisfies.
* `Stacks.SheafOfModules.generatorRatioUnit_comp`, `_self`, `_symm` and `_restrict`: the
  cocycle, normalization and restriction laws of the transition units.

## Implementation notes

`GeneratorSections` is phrased as bijectivity of multiplication on every smaller open rather
than as an isomorphism `𝒪_U ≅ L|_U`, because that is the form in which the sections are
produced (from a nonvanishing section, by
`Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen`) and consumed (as the local
frames in which a norm is computed). `generatorOfIso` converts an isomorphism into this form.

Both bijectivity statements of a pair of generators are used in
`isUnit_of_smul_eq_generator`: the surjectivity of the first produces a candidate inverse and
the injectivity of each of the two gives one of the two unit equations. This avoids having to
know that the section ring is commutative, which matters because the structure sheaf is
presented through `RingCat` here.

No local-ring hypothesis and no invertibility hypothesis appear anywhere in this file: a
generator is explicit data, and everything below is formal consequence of its defining
bijections.

## References

* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}}

/-- Sections of `L` which trivialize it on `U`: multiplication by the restricted section is
bijective on every smaller open. -/
abbrev GeneratorSections (X : RingedSpace.{u, u})
    (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)) (U : Opens X.carrier) :=
  {s : L.val.obj (op U) // ∀ (V : Opens X.carrier) (h : V ≤ U),
    Function.Bijective (fun r : (structureSheaf X.sheaf).obj.obj (op V) =>
      r • L.val.restrictₛₗ (homOfLE h).op s)}

variable (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))

/-- Restricting a section along the identity inclusion does nothing. -/
theorem generator_restrict_self (U : Opens X.carrier) (s : GeneratorSections X L U) :
    L.val.restrictₛₗ (homOfLE le_rfl).op s.val = s.val := by
  rw [PresheafOfModules.restrictₛₗ_apply,
    show homOfLE le_rfl = 𝟙 U from Subsingleton.elim _ _]
  simp

/-- The scalar relating two generators on the same open is a unit. Both generators are used:
surjectivity of multiplication by the first produces the inverse, and injectivity of the two
multiplications gives the two unit equations, with no appeal to commutativity. -/
theorem isUnit_of_smul_eq_generator (U : Opens X.carrier) (s t : GeneratorSections X L U)
    (a : (structureSheaf X.sheaf).obj.obj (op U)) (ha : t.val = a • s.val) : IsUnit a := by
  have key (x y : GeneratorSections X L U) (c d : (structureSheaf X.sheaf).obj.obj (op U))
      (hc : x.val = c • y.val) (hd : y.val = d • x.val) : d * c = 1 := by
    refine (y.property U le_rfl).injective ?_
    rw [generator_restrict_self]
    calc (d * c) • y.val = d • x.val := by rw [mul_smul, ← hc]
      _ = (1 : (structureSheaf X.sheaf).obj.obj (op U)) • y.val := by rw [← hd, one_smul]
  obtain ⟨b, hb⟩ := (t.property U le_rfl).surjective s.val
  rw [generator_restrict_self] at hb
  exact ⟨⟨a, b, key s t b a hb.symm ha, key t s a b ha hb.symm⟩, rfl⟩

/-- A generator restricts to a generator on a smaller open. -/
noncomputable def generatorRestrict {U V : Opens X.carrier} (h : V ≤ U)
    (s : GeneratorSections X L U) :
    GeneratorSections X L V := by
  refine ⟨L.val.restrictₛₗ (homOfLE h).op s.val, fun W k => ?_⟩
  convert s.property W (k.trans h) using 1
  funext r
  congr 1
  change L.val.map (homOfLE k).op (L.val.map (homOfLE h).op s.val) =
    L.val.map (homOfLE (k.trans h)).op s.val
  rw [← PresheafOfModules.map_comp_apply]
  congr 2

/-- The underlying section of a restricted generator is the restricted section. -/
@[simp]
theorem generatorRestrict_val {U V : Opens X.carrier} (h : V ≤ U)
    (s : GeneratorSections X L U) :
    (generatorRestrict L h s).val = L.val.restrictₛₗ (homOfLE h).op s.val :=
  rfl

/-- Restriction of generators is transitive. -/
theorem generatorRestrict_trans {U V W : Opens X.carrier} (h : V ≤ U) (k : W ≤ V)
    (s : GeneratorSections X L U) :
    generatorRestrict L k (generatorRestrict L h s) =
      generatorRestrict L (k.trans h) s := by
  refine Subtype.ext ?_
  show L.val.map (homOfLE k).op (L.val.map (homOfLE h).op s.val) =
    L.val.map (homOfLE (k.trans h)).op s.val
  rw [← PresheafOfModules.map_comp_apply]
  congr 2

/-- Restricting a generator to the open it already lives on does nothing. -/
@[simp]
theorem generatorRestrict_self (U : Opens X.carrier) (s : GeneratorSections X L U) :
    generatorRestrict L le_rfl s = s :=
  Subtype.ext (generator_restrict_self L U s)

/-- A trivialization of `L` supplies a generator on every open: the image of the unit
section. -/
noncomputable def generatorOfIso {U : Opens X.carrier}
    (e : L ≅ _root_.SheafOfModules.unit (structureSheaf X.sheaf)) :
    GeneratorSections X L U := by
  let oneU : (structureSheaf X.sheaf).obj.obj (op U) := 1
  refine ⟨e.inv.val.app (op U) oneU, fun V h => ?_⟩
  set i := (homOfLE h).op with hi
  let oneV : (structureSheaf X.sheaf).obj.obj (op V) := 1
  have hmap : (structureSheaf X.sheaf).obj.map i oneU = oneV :=
    ((structureSheaf X.sheaf).obj.map i).hom.map_one
  have hsV : L.val.map i (e.inv.val.app (op U) oneU) = e.inv.val.app (op V) oneV := by
    refine (PresheafOfModules.naturality_apply e.inv.val i oneU).symm.trans ?_
    change e.inv.val.app (op V) ((structureSheaf X.sheaf).obj.map i oneU) = _
    rw [hmap]
  have hcompinv : e.inv.val.app (op V) ≫ e.hom.val.app (op V) = 𝟙 _ :=
    congrArg (fun φ => φ.val.app (op V)) e.inv_hom_id
  have hone : e.hom.val.app (op V) (e.inv.val.app (op V) oneV) = oneV :=
    LinearMap.congr_fun (congrArg (fun k => k.hom) hcompinv) oneV
  have hlin (r : (structureSheaf X.sheaf).obj.obj (op V)) :
      e.hom.val.app (op V) (r • L.val.restrictₛₗ i (e.inv.val.app (op U) oneU)) = r := by
    rw [PresheafOfModules.restrictₛₗ_apply, hsV]
    change (e.hom.val.app (op V)).hom (r • e.inv.val.app (op V) oneV) = r
    rw [(e.hom.val.app (op V)).hom.map_smul, hone]
    exact mul_one r
  have hcomphom : e.hom.val.app (op V) ≫ e.inv.val.app (op V) = 𝟙 _ :=
    congrArg (fun φ => φ.val.app (op V)) e.hom_inv_id
  have hinj : Function.Injective (e.hom.val.app (op V)) := by
    have hcomp := congrArg (fun k => k.hom) hcomphom
    intro p q hpq
    have hp : e.inv.val.app (op V) (e.hom.val.app (op V) p) = p := by
      simpa using congrArg (fun k => k p) hcomp
    have hq : e.inv.val.app (op V) (e.hom.val.app (op V) q) = q := by
      simpa using congrArg (fun k => k q) hcomp
    rw [← hp, ← hq, hpq]
  refine ⟨fun p q hpq => ?_, fun m => ⟨e.hom.val.app (op V) m, hinj (hlin _)⟩⟩
  have h' : e.hom.val.app (op V) (p • L.val.restrictₛₗ i (e.inv.val.app (op U) oneU)) =
      e.hom.val.app (op V) (q • L.val.restrictₛₗ i (e.inv.val.app (op U) oneU)) :=
    congrArg (e.hom.val.app (op V)) hpq
  rwa [hlin p, hlin q] at h'

/-- An isomorphism of modules carries generators to generators. -/
noncomputable def generatorMapIso {L M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)}
    (e : L ≅ M) (U : Opens X.carrier) (s : GeneratorSections X L U) :
    GeneratorSections X M U := by
  refine ⟨e.hom.val.app (op U) s.val, fun V h => ?_⟩
  have hnat := PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op s.val
  have he : Function.Bijective (e.hom.val.app (op V)) :=
    ConcreteCategory.bijective_of_isIso
      ((_root_.SheafOfModules.forget (structureSheaf X.sheaf) ⋙
        PresheafOfModules.evaluation _ (op V)).mapIso e).hom
  convert he.comp (s.property V h) using 1
  funext r
  change r • M.val.map (homOfLE h).op (e.hom.val.app (op U) s.val) =
    e.hom.val.app (op V) (r • L.val.map (homOfLE h).op s.val)
  rw [← hnat]
  exact ((e.hom.val.app (op V)).hom.map_smul r _).symm

/-- The underlying section of the image of a generator under `e` is the image of the section. -/
@[simp]
theorem generatorMapIso_val {L M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)} (e : L ≅ M)
    (U : Opens X.carrier) (s : GeneratorSections X L U) :
    (generatorMapIso e U s).val = e.hom.val.app (op U) s.val :=
  rfl

/-- Carrying a generator along an isomorphism of modules commutes with restriction. -/
theorem generatorMapIso_restrict {L M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)}
    (e : L ≅ M) {U V : Opens X.carrier} (h : V ≤ U) (s : GeneratorSections X L U) :
    generatorMapIso e V (generatorRestrict L h s) =
      generatorRestrict M h (generatorMapIso e U s) :=
  Subtype.ext (PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op s.val)

/-- The scalar comparing two generators on the same open. -/
noncomputable def generatorRatio (U : Opens X.carrier) (s t : GeneratorSections X L U) :
    (structureSheaf X.sheaf).obj.obj (op U) :=
  Classical.choose ((s.property U le_rfl).surjective t.val)

/-- The generator `t` is the comparison scalar of `s` and `t` times the generator `s`. -/
theorem generatorRatio_spec (U : Opens X.carrier) (s t : GeneratorSections X L U) :
    t.val = generatorRatio L U s t • s.val := by
  have h : generatorRatio L U s t • L.val.restrictₛₗ (homOfLE le_rfl).op s.val = t.val :=
    Classical.choose_spec ((s.property U le_rfl).surjective t.val)
  rw [generator_restrict_self] at h
  exact h.symm

/-- Any scalar `a` with `t = a • s` is the comparison scalar of `s` and `t`. -/
theorem generatorRatio_unique (U : Opens X.carrier) (s t : GeneratorSections X L U)
    (a : (structureSheaf X.sheaf).obj.obj (op U)) (ha : t.val = a • s.val) :
    a = generatorRatio L U s t := by
  refine (s.property U le_rfl).injective ?_
  rw [generator_restrict_self]
  exact ha.symm.trans (generatorRatio_spec L U s t)

/-- The comparison scalar is unchanged by an isomorphism of modules. -/
theorem generatorRatio_mapIso {L M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)}
    (e : L ≅ M) (U : Opens X.carrier) (s t : GeneratorSections X L U) :
    generatorRatio M U (generatorMapIso e U s) (generatorMapIso e U t) =
      generatorRatio L U s t := by
  refine (generatorRatio_unique M U _ _ _ ?_).symm
  show e.hom.val.app (op U) t.val = _
  rw [generatorRatio_spec L U s t]
  exact (e.hom.val.app (op U)).hom.map_smul _ _

/-- Restricting generators restricts their comparison scalar. -/
theorem generatorRatio_restrict {U V : Opens X.carrier} (h : V ≤ U)
    (s t : GeneratorSections X L U) :
    generatorRatio L V (generatorRestrict L h s) (generatorRestrict L h t) =
      (structureSheaf X.sheaf).obj.map (homOfLE h).op (generatorRatio L U s t) := by
  refine (generatorRatio_unique L V _ _ _ ?_).symm
  show L.val.map (homOfLE h).op t.val =
    (structureSheaf X.sheaf).obj.map (homOfLE h).op (generatorRatio L U s t) •
      L.val.map (homOfLE h).op s.val
  rw [generatorRatio_spec L U s t]
  exact PresheafOfModules.map_smul L.val (homOfLE h).op _ _

/-- The comparison scalars of three generators compose. -/
theorem generatorRatio_comp (U : Opens X.carrier) (s t r : GeneratorSections X L U) :
    generatorRatio L U t r * generatorRatio L U s t = generatorRatio L U s r :=
  generatorRatio_unique L U s r _ <| by
    calc r.val = generatorRatio L U t r • t.val := generatorRatio_spec L U t r
      _ = generatorRatio L U t r • (generatorRatio L U s t • s.val) := by
          rw [generatorRatio_spec L U s t]
      _ = (generatorRatio L U t r * generatorRatio L U s t) • s.val := by rw [mul_smul]

/-- The comparison scalar from a generator to itself is one. -/
@[simp]
theorem generatorRatio_self (U : Opens X.carrier) (s : GeneratorSections X L U) :
    generatorRatio L U s s = 1 :=
  (generatorRatio_unique L U s s 1 (one_smul _ _).symm).symm

/-- Scaling a generator scales its comparison scalar against a fixed base generator. -/
theorem generatorRatio_smul (U : Opens X.carrier) (b s t : GeneratorSections X L U)
    (a : (structureSheaf X.sheaf).obj.obj (op U)) (ha : t.val = a • s.val) :
    generatorRatio L U b t = a * generatorRatio L U b s := by
  symm
  refine generatorRatio_unique L U b t _ ?_
  rw [ha, generatorRatio_spec L U b s, mul_smul]

/-- The comparison scalar of two generators, remembered as a unit. -/
noncomputable def generatorRatioUnit (U : Opens X.carrier) (s t : GeneratorSections X L U) :
    ((structureSheaf X.sheaf).obj.obj (op U))ˣ :=
  (isUnit_of_smul_eq_generator L U s t _ (generatorRatio_spec L U s t)).unit

/-- The underlying scalar of the transition unit is the comparison scalar. -/
@[simp]
theorem generatorRatioUnit_val (U : Opens X.carrier) (s t : GeneratorSections X L U) :
    (generatorRatioUnit L U s t).val = generatorRatio L U s t := by
  simp [generatorRatioUnit]

/-- A unit relating two generators is their transition unit. -/
theorem generatorRatioUnit_eq (U : Opens X.carrier) (s t : GeneratorSections X L U)
    (a : ((structureSheaf X.sheaf).obj.obj (op U))ˣ) (ha : t.val = a.val • s.val) :
    generatorRatioUnit L U s t = a :=
  Units.ext <| by
    rw [generatorRatioUnit_val]
    exact (generatorRatio_unique L U s t a.val ha).symm

/-- Transition units commute with restriction. -/
theorem generatorRatioUnit_restrict {U V : Opens X.carrier} (h : V ≤ U)
    (s t : GeneratorSections X L U) :
    generatorRatioUnit L V (generatorRestrict L h s) (generatorRestrict L h t) =
      Units.map ((structureSheaf X.sheaf).obj.map (homOfLE h).op).hom
        (generatorRatioUnit L U s t) :=
  Units.ext <| by
    show (generatorRatioUnit L V (generatorRestrict L h s) (generatorRestrict L h t)).val =
      ((structureSheaf X.sheaf).obj.map (homOfLE h).op).hom (generatorRatioUnit L U s t).val
    rw [generatorRatioUnit_val, generatorRatio_restrict, generatorRatioUnit_val]

/-- The transition units of three generators satisfy the cocycle identity. -/
theorem generatorRatioUnit_comp (U : Opens X.carrier) (s t r : GeneratorSections X L U) :
    generatorRatioUnit L U t r * generatorRatioUnit L U s t = generatorRatioUnit L U s r :=
  Units.ext <| by
    simp only [Units.val_mul, generatorRatioUnit_val]
    exact generatorRatio_comp L U s t r

/-- The transition unit from a generator to itself is one. -/
@[simp]
theorem generatorRatioUnit_self (U : Opens X.carrier) (s : GeneratorSections X L U) :
    generatorRatioUnit L U s s = 1 :=
  Units.ext <| by simp

/-- Reversing a transition inverts its unit. -/
theorem generatorRatioUnit_symm (U : Opens X.carrier) (s t : GeneratorSections X L U) :
    generatorRatioUnit L U t s = (generatorRatioUnit L U s t)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [generatorRatioUnit_comp, generatorRatioUnit_self]

/-- Transition units are unchanged by an isomorphism of modules. -/
theorem generatorRatioUnit_mapIso {L M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)}
    (e : L ≅ M) (U : Opens X.carrier) (s t : GeneratorSections X L U) :
    generatorRatioUnit M U (generatorMapIso e U s) (generatorMapIso e U t) =
      generatorRatioUnit L U s t :=
  Units.ext <| by rw [generatorRatioUnit_val, generatorRatioUnit_val, generatorRatio_mapIso]

end Stacks.SheafOfModules
