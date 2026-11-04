module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnitySections
public import StacksFrontier.AlgebraicGeometry.Picard.BaseSitesFirstCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.NormalizedGenerators

/-!
# The torsor of trivializations of a pair

Let `C` be a site and `F : C ⥤ Scheme` a functor whose global functions form a sheaf of
commutative rings, so that `(C, F.op ⋙ Scheme.Γ)` is a ringed site. Let `L` be an invertible
module on it and `α : L^{⊗ n} ≅ O` a trivialization of its `n`-th tensor power. The local
generators `s` of `L` with `α(s^{⊗ n}) = 1` — the trivializations of the pair `(L, α)` — form a
sheaf of sets on which the sheaf `μ_n` of `n`-th roots of unity acts by scaling, and that action
is simply transitive on every nonempty set of sections. This is the second construction of
Tag 040Q.

## Main definitions

* `AlgebraicGeometry.schemeFunctionsRingedSite` reads a site of schemes carrying the global
  functions as a ringed site.
* `AlgebraicGeometry.rootUnit` is the global unit underlying a section of `μ_n`.
* `AlgebraicGeometry.normalizedGenerator` reads a normalized local generator as a local
  generator, and `AlgebraicGeometry.normalizedSmul` scales one by an `n`-th root of unity.
* `AlgebraicGeometry.rootAct` is the action of `μ_n` on the normalized local generators.
* `AlgebraicGeometry.trivializationTorsor` is **the torsor of trivializations of the pair
  `(L, α)`**.

## Main results

* `AlgebraicGeometry.baseRingedSite_eq`: the big `τ`-site of a scheme is such a ringed site.
* `AlgebraicGeometry.rootUnit_rootSection`, `AlgebraicGeometry.rootUnit_zero`,
  `AlgebraicGeometry.rootUnit_add` and `AlgebraicGeometry.rootUnit_val_restrict`: the underlying
  unit of a section of `μ_n` determines it, is multiplicative, and commutes with restriction.
* `AlgebraicGeometry.rootAct_existsUnique`: **two trivializations of the pair differ by a unique
  `n`-th root of unity**, which is the simple transitivity of the action.
* `AlgebraicGeometry.trivializationTorsor_presheaf` and
  `AlgebraicGeometry.trivializationTorsor_act` identify the sections of the torsor with the
  normalized local generators and its action with scaling.

## Implementation notes

A section of `μ_n` over `U` is turned into an acting unit by the inclusion `μ_n ⟶ 𝐆_m`, not by
choosing a preimage under `AlgebraicGeometry.rootSection`: the inclusion is a function, so the
action it defines needs no choice, and `AlgebraicGeometry.pow_eq_one_rootUnit` says exactly that
the resulting unit has `n`-th power one, which is what makes the scaled generator normalized
again through `Stacks.Cohomology.Torsors.Generators.trivUnit_smul`. Only simple transitivity goes
the other way, through `AlgebraicGeometry.exists_rootSection`.

The sections of the structure sheaf of this ringed site over an object `U` are the global
functions on `F U` — the same type, reached through `Stacks.SheafOfModules.Tensor.ringSheaf` and
so through a different spelling. `AlgebraicGeometry.rootUnit` is therefore declared with the
ringed site's spelling of that type and no transport appears anywhere, the two being
definitionally equal. Its index is written `op U.unop` rather than `U` because a scalar action
is only found by instance search when the scalars and the module are indexed by the same
expression, and the module side comes from a local generator over `U.unop`.

The two sheafification hypotheses of
`Stacks.Cohomology.Torsors.Generators.normalizedSheaf` are instance binders stated for the
projection `(schemeFunctionsRingedSite J F hO).J`, which is the form in which instance search
needs them.

## References

* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 040N](https://stacks.math.columbia.edu/tag/040N)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.Torsors (AbelianTorsor)
open Stacks.Cohomology.Torsors.Generators
open Stacks.SheafOfModules (IsInvertible)

universe v u w

namespace AlgebraicGeometry

/-- A category of schemes with a topology for which the global functions form a sheaf of
commutative rings, read as a ringed site. -/
def schemeFunctionsRingedSite {C : Type v} [Category.{u} C] (J : GrothendieckTopology C)
    (F : C ⥤ Scheme.{u}) (hO : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ)) : RingedSite.{v, u, u} where
  C := C
  J := J
  O := ⟨F.op ⋙ Scheme.Γ, hO⟩

/-- The big `τ`-site of a scheme is this ringed site. -/
theorem baseRingedSite_eq (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (τ : SiteKind) :
    BigFppfOver.baseRingedSite B S hS τ =
      schemeFunctionsRingedSite (BigFppfOver.baseOverTopology B S hS τ)
        (BigFppfOver.toScheme B S hS) (FibredSite.baseStructureSheaf B S hS τ).property := rfl

section Normalized

variable (X : RingedSite.{v, u, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- A normalized local generator of a pair, read as a local generator of the module. -/
def normalizedGenerator (U : X.Cᵒᵖ) (s : (normalizedSubfunctor X L n al).obj U) :
    GeneratorSections' X L U.unop := ⟨s.val, s.property.1⟩

/-- The trivialization unit of a normalized local generator is one: that is what being
normalized says. -/
theorem trivUnit_normalizedGenerator (U : X.Cᵒᵖ) (s : (normalizedSubfunctor X L n al).obj U) :
    trivUnit X L n al U.unop (normalizedGenerator X L n al U s) = 1 :=
  Units.ext <| (trivUnit_val_eq_trivValue X L n al U.unop _).trans s.property.2

/-- Scaling a normalized local generator by an `n`-th root of unity gives a normalized local
generator: the trivialization unit is multiplied by the `n`-th power of the scalar. -/
def normalizedSmul (U : X.Cᵒᵖ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)ˣ) (ha : a ^ n = 1)
    (s : (normalizedSubfunctor X L n al).obj U) : (normalizedSubfunctor X L n al).obj U := by
  refine ⟨(generatorSections_smul_unit' X L U.unop a (normalizedGenerator X L n al U s)).val,
    (generatorSections_smul_unit' X L U.unop a (normalizedGenerator X L n al U s)).property, ?_⟩
  rw [← trivUnit_val_eq_trivValue X L n al U.unop
      (generatorSections_smul_unit' X L U.unop a (normalizedGenerator X L n al U s)),
    trivUnit_smul X L n al U.unop a (normalizedGenerator X L n al U s),
    trivUnit_normalizedGenerator X L n al U s, ha, one_mul]
  exact Units.val_one

/-- The section underlying a scaled normalized local generator. -/
theorem normalizedSmul_val (U : X.Cᵒᵖ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U : Type w)ˣ) (ha : a ^ n = 1)
    (s : (normalizedSubfunctor X L n al).obj U) :
    (normalizedSmul X L n al U a ha s).val =
      (generatorSections_smul_unit' X L U.unop a (normalizedGenerator X L n al U s)).val :=
  rfl

/-- Restriction of a normalized local generator restricts the underlying section. -/
theorem normalizedSheaf_map_val {U V : X.Cᵒᵖ} (f : U ⟶ V)
    (s : (normalizedSubfunctor X L n al).obj U) :
    ((normalizedSheaf X L n al).obj.map f s).val = L.val.restrictₛₗ f s.val :=
  rfl

end Normalized

section Torsor

variable {C : Type v} [Category.{u} C] (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (hO : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ))
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)

/-- The global unit underlying a section of the sheaf of `n`-th roots of unity, namely its image
under the inclusion `μ_n ⟶ 𝐆_m`, read as a unit of the sections of the structure sheaf of the
ringed site. -/
def rootUnit (U : Cᵒᵖ) (g : (rootsOfUnitySheaf J F h n).obj.obj U) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf
        (schemeFunctionsRingedSite J F hO).O).obj.obj (op U.unop) : Type u)ˣ :=
  Additive.toMul ((kernel.ι (powerSheaf J F h n)).hom.app U g)

/-- The unit underlying a section of the sheaf of `n`-th roots of unity has `n`-th power one. -/
theorem rootUnit_pow (U : Cᵒᵖ) (g : (rootsOfUnitySheaf J F h n).obj.obj U) :
    rootUnit J F hO h n U g ^ n = 1 :=
  pow_eq_one_rootUnit J F h n U.unop g

/-- The unit underlying the zero section is one. -/
theorem rootUnit_zero (U : Cᵒᵖ) : rootUnit J F hO h n U 0 = 1 :=
  congrArg Additive.toMul ((kernel.ι (powerSheaf J F h n)).hom.app U).hom.map_zero

/-- The unit underlying a sum of sections is the product of the units. -/
theorem rootUnit_add (U : Cᵒᵖ) (g g' : (rootsOfUnitySheaf J F h n).obj.obj U) :
    rootUnit J F hO h n U (g + g') = rootUnit J F hO h n U g * rootUnit J F hO h n U g' :=
  congrArg Additive.toMul (((kernel.ι (powerSheaf J F h n)).hom.app U).hom.map_add g g')

/-- The unit underlying `AlgebraicGeometry.rootSection` of a unit is that unit. -/
theorem rootUnit_rootSection (U : Cᵒᵖ) (a : (Scheme.Γ.obj (op (F.obj U.unop)))ˣ) (ha : a ^ n = 1) :
    rootUnit J F hO h n U (rootSection J F h n U.unop a ha) = a :=
  congrArg Additive.toMul (rootsOfUnityι_rootSection J F h n U.unop a ha)

/-- The unit underlying a section of the sheaf of `n`-th roots of unity determines the
section. -/
theorem rootUnit_injective (U : Cᵒᵖ) {g g' : (rootsOfUnitySheaf J F h n).obj.obj U}
    (hgg : rootUnit J F hO h n U g = rootUnit J F hO h n U g') : g = g' := by
  obtain ⟨a, ha, rfl⟩ := exists_rootSection J F h n U.unop g
  obtain ⟨b, hb, rfl⟩ := exists_rootSection J F h n U.unop g'
  rw [rootUnit_rootSection, rootUnit_rootSection] at hgg
  subst hgg
  rfl

/-- Restricting a section of the sheaf of `n`-th roots of unity restricts its unit. -/
theorem rootUnit_val_restrict {U V : Cᵒᵖ} (f : U ⟶ V)
    (g : (rootsOfUnitySheaf J F h n).obj.obj U) :
    (rootUnit J F hO h n V ((rootsOfUnitySheaf J F h n).obj.map f g)).val =
      (Stacks.SheafOfModules.Tensor.ringSheaf
          (schemeFunctionsRingedSite J F hO).O).obj.map f (rootUnit J F hO h n U g).val :=
  congrArg (fun y => (Additive.toMul y).val)
    (NatTrans.naturality_apply (kernel.ι (powerSheaf J F h n)).hom f g)

variable (L : SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
    [(schemeFunctionsRingedSite J F hO).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (schemeFunctionsRingedSite J F hO).J AddCommGrpCat.{u}]
    [IsInvertible (schemeFunctionsRingedSite J F hO).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O).2 L]
    (al : tpow (schemeFunctionsRingedSite J F hO) L n ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))

/-- The action of a section of the sheaf of `n`-th roots of unity on the trivializations of the
pair: it scales a normalized local generator by the underlying unit. -/
def rootAct (U : Cᵒᵖ) (g : (rootsOfUnitySheaf J F h n).obj.obj U)
    (s : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) L n al).obj U) :
    (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) L n al).obj U :=
  normalizedSmul (schemeFunctionsRingedSite J F hO) L n al U (rootUnit J F hO h n U g)
    (rootUnit_pow J F hO h n U g) s

/-- The action scales the underlying section by the underlying unit. -/
theorem rootAct_val (U : Cᵒᵖ) (g : (rootsOfUnitySheaf J F h n).obj.obj U)
    (s : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) L n al).obj U) :
    (rootAct J F hO h n L al U g s).val = (rootUnit J F hO h n U g).val •
      (normalizedGenerator (schemeFunctionsRingedSite J F hO) L n al U s).val :=
  rfl

/-- The section attached to a unit `a` with `aⁿ = 1` scales the underlying section by `a`. -/
private theorem rootAct_rootSection_val (U : Cᵒᵖ) (a : (Scheme.Γ.obj (op (F.obj U.unop)))ˣ)
    (ha : a ^ n = 1)
    (s : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) L n al).obj U) :
    (rootAct J F hO h n L al U (rootSection J F h n U.unop a ha) s).val =
      (generatorSections_smul_unit' (schemeFunctionsRingedSite J F hO) L U.unop a
        (normalizedGenerator (schemeFunctionsRingedSite J F hO) L n al U s)).val := by
  refine (rootAct_val J F hO h n L al U (rootSection J F h n U.unop a ha) s).trans ?_
  rw [rootUnit_rootSection]
  rfl

/-- The zero section acts trivially. -/
theorem rootAct_zero (U : Cᵒᵖ)
    (s : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) L n al).obj U) :
    rootAct J F hO h n L al U 0 s = s := by
  apply Subtype.ext
  rw [rootAct_val, rootUnit_zero, Units.val_one, one_smul]
  rfl

/-- The action is compatible with addition of sections. -/
theorem rootAct_add (U : Cᵒᵖ) (g g' : (rootsOfUnitySheaf J F h n).obj.obj U)
    (s : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) L n al).obj U) :
    rootAct J F hO h n L al U (g + g') s =
      rootAct J F hO h n L al U g (rootAct J F hO h n L al U g' s) := by
  apply Subtype.ext
  rw [rootAct_val J F hO h n L al U (g + g') s, rootUnit_add, Units.val_mul, mul_smul]
  rfl

/-- The action commutes with restriction. -/
theorem rootAct_restrict {U V : Cᵒᵖ} (f : U ⟶ V) (g : (rootsOfUnitySheaf J F h n).obj.obj U)
    (s : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) L n al).obj U) :
    (normalizedSheaf (schemeFunctionsRingedSite J F hO) L n al).obj.map f
        (rootAct J F hO h n L al U g s) =
      rootAct J F hO h n L al V ((rootsOfUnitySheaf J F h n).obj.map f g)
        ((normalizedSheaf (schemeFunctionsRingedSite J F hO) L n al).obj.map f s) := by
  apply Subtype.ext
  refine (normalizedSheaf_map_val (schemeFunctionsRingedSite J F hO) L n al f
    (rootAct J F hO h n L al U g s)).trans ?_
  refine Eq.trans (congrArg (fun z => L.val.restrictₛₗ f z)
    (rootAct_val J F hO h n L al U g s)) ?_
  refine Eq.trans ((L.val.restrictₛₗ f).map_smulₛₗ (rootUnit J F hO h n U g).val
    (normalizedGenerator (schemeFunctionsRingedSite J F hO) L n al U s).val) ?_
  refine Eq.trans (congrArg
    (fun z : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (schemeFunctionsRingedSite J F hO).O).obj.obj V : Type u) => z •
      L.val.restrictₛₗ f
        (normalizedGenerator (schemeFunctionsRingedSite J F hO) L n al U s).val)
    (rootUnit_val_restrict J F hO h n f g).symm) ?_
  exact (rootAct_val J F hO h n L al V ((rootsOfUnitySheaf J F h n).obj.map f g)
    ((normalizedSheaf (schemeFunctionsRingedSite J F hO) L n al).obj.map f s)).symm

/-- **Two trivializations of the pair differ by a unique `n`-th root of unity.** -/
theorem rootAct_existsUnique (U : Cᵒᵖ)
    (s t : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) L n al).obj U) :
    ∃! g : (rootsOfUnitySheaf J F h n).obj.obj U, rootAct J F hO h n L al U g s = t := by
  obtain ⟨a, ⟨ha, hat⟩, huniq⟩ :=
    existsUnique_rootOfUnity_smul_of_trivUnit_eq (schemeFunctionsRingedSite J F hO) L n al U.unop
      (normalizedGenerator (schemeFunctionsRingedSite J F hO) L n al U s)
      (normalizedGenerator (schemeFunctionsRingedSite J F hO) L n al U t)
      ((trivUnit_normalizedGenerator (schemeFunctionsRingedSite J F hO) L n al U s).trans
        (trivUnit_normalizedGenerator (schemeFunctionsRingedSite J F hO) L n al U t).symm)
  refine ⟨rootSection J F h n U.unop a ha, ?_, ?_⟩
  · exact Subtype.ext <| (rootAct_rootSection_val J F hO h n L al U a ha s).trans
      (congrArg Subtype.val hat)
  · intro g hg
    obtain ⟨b, hb, rfl⟩ := exists_rootSection J F h n U.unop g
    have hval := congrArg Subtype.val hg
    rw [rootAct_val, rootUnit_rootSection] at hval
    obtain rfl := huniq b ⟨hb, Subtype.ext hval⟩
    rfl

end Torsor

/-- **The torsor of trivializations of a pair** (Stacks 040Q, second construction). The local
generators of `L` on which the trivialization of its `n`-th tensor power takes the value one
form a torsor under the sheaf of `n`-th roots of unity. -/
def trivializationTorsor {C : Type v} [Category.{u} C] (J : GrothendieckTopology C)
    (F : C ⥤ Scheme.{u}) (hO : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ))
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)
    [(schemeFunctionsRingedSite J F hO).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (schemeFunctionsRingedSite J F hO).J AddCommGrpCat.{u}]
    (hX : RingedSite.IsLocallyRinged (schemeFunctionsRingedSite J F hO))
    (hroot : LocalRoots (schemeFunctionsRingedSite J F hO) n)
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
    (hL : IsInvertible (schemeFunctionsRingedSite J F hO).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O).2 L)
    (al : tpow (schemeFunctionsRingedSite J F hO) L n ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O)) :
    AbelianTorsor (rootsOfUnitySheaf J F h n) := by
  refine ⟨{ presheaf := (normalizedSheaf (schemeFunctionsRingedSite J F hO) L n al).obj
            isSheaf := (normalizedSheaf (schemeFunctionsRingedSite J F hO) L n al).property
            act := fun U g s => rootAct J F hO h n L al U (Multiplicative.toAdd g) s
            one_act := fun U s => rootAct_zero J F hO h n L al U s
            mul_act := fun U g g' s => rootAct_add J F hO h n L al U _ _ s
            naturality := fun f g s => rootAct_restrict J F hO h n L al f _ s
            simplyTransitive := fun U _ s t => rootAct_existsUnique J F hO h n L al U s t }, ?_⟩
  intro U
  exact exists_cover_normalized (schemeFunctionsRingedSite J F hO) hX L hL n al hroot U

/-- Its sections are the normalized local generators. -/
theorem trivializationTorsor_presheaf {C : Type v} [Category.{u} C]
    (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (hO : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ))
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)
    [(schemeFunctionsRingedSite J F hO).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (schemeFunctionsRingedSite J F hO).J AddCommGrpCat.{u}]
    (hX : RingedSite.IsLocallyRinged (schemeFunctionsRingedSite J F hO))
    (hroot : LocalRoots (schemeFunctionsRingedSite J F hO) n)
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
    (hL : IsInvertible (schemeFunctionsRingedSite J F hO).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O).2 L)
    (al : tpow (schemeFunctionsRingedSite J F hO) L n ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O)) :
    (trivializationTorsor J F hO h n hX hroot L hL al).1.presheaf =
      (normalizedSheaf (schemeFunctionsRingedSite J F hO) L n al).obj :=
  rfl

/-- A root of unity acts by scaling the normalized local generator: the section of the sheaf of
`n`-th roots of unity attached to a unit `a` with `aⁿ = 1` carries a trivialization `s` of the
pair to `a · s`. -/
theorem trivializationTorsor_act {C : Type v} [Category.{u} C]
    (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (hO : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ))
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)
    [(schemeFunctionsRingedSite J F hO).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (schemeFunctionsRingedSite J F hO).J AddCommGrpCat.{u}]
    (hX : RingedSite.IsLocallyRinged (schemeFunctionsRingedSite J F hO))
    (hroot : LocalRoots (schemeFunctionsRingedSite J F hO) n)
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
    (hL : IsInvertible (schemeFunctionsRingedSite J F hO).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O).2 L)
    (al : tpow (schemeFunctionsRingedSite J F hO) L n ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
    (U : Cᵒᵖ) (a : (Scheme.Γ.obj (op (F.obj U.unop)))ˣ) (ha : a ^ n = 1)
    (s : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) L n al).obj U) :
    (((trivializationTorsor J F hO h n hX hroot L hL al).1.act U
          (Multiplicative.ofAdd (rootSection J F h n U.unop a ha)) s).val : L.val.obj U) =
      (generatorSections_smul_unit' (schemeFunctionsRingedSite J F hO) L U.unop a
        (normalizedGenerator (schemeFunctionsRingedSite J F hO) L n al U s)).val :=
  rootAct_rootSection_val J F hO h n L al U a ha s

end AlgebraicGeometry

end
