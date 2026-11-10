module

public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentLiftingObstruction
public import StacksFrontier.Deformation.ToposThickening.ExtensionProblem
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Lifting a morphism between two square-zero extensions of ringed topoi

This file states the comparison diagram of [Stacks Project, Tag 08UG] and the two conclusions
of that lemma: the obstruction class controlling the existence of the missing comparison
morphism, and the principal homogeneous space structure on the set of such morphisms.

The source's diagram consists of two square-zero extension problems of ringed topoi, indexed by
`1` and `2`, joined by comparison morphisms of ringed topoi running from the index `2` layer to
the index `1` layer — so, on structure sheaves, by maps running from the index `1` layer to the
index `2` layer — with the comparison of the two *thickened* source ringed topoi deliberately
absent: its existence is the lifting problem. Following the source's own reduction ("we will
identify the underlying topoi for every thickening in sight", and then "we may assume we have a
diagram (08UI) of sheaves on a site `C`"), the diagram is presented here as a diagram of sheaves of
commutative rings on one site, so that the sought comparison is a homomorphism
`O'₁ ⟶ O'₂` of sheaves of rings. This is the same reduction under which the ringed-space twin
Tag 08U8 is formalized in
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentLiftingObstruction.lean`.

## Main definitions

* `Deformation.ToposThickening.LiftSquare`: one layer of the diagram — a first order thickening
  of a base, a first order thickening of the source over it, and the module identifying the
  upper ideal. This is the same datum as a solution of
  `Deformation.ToposThickening.RingedToposExtensionProblem` with the two underlying topoi
  identified.
* `Deformation.ToposThickening.LiftDiagram`: the diagram of the source, the two layers together
  with the comparison morphisms of the two bases, of the two thickened bases, of the two reduced
  sources, and the comparison `ν` of the two ideal modules.
* `Deformation.ToposThickening.LiftDiagram.Lift`: a morphism fitting into the diagram
  compatibly with `ν`, i.e. a homomorphism `O'₁ ⟶ O'₂` of sheaves of rings commuting with the
  two reductions, with the two maps from the thickened bases, and inducing `ν` on ideals.
* `Deformation.ToposThickening.LiftDiagram.Derivation`: the group acting on the lifts — a
  section-wise additive map `O'₁ ⟶ G₂` satisfying the Leibniz rule through the reduction, and
  vanishing on the ideal `G₁` and on the image of `O_{B'₁}`.

## Main results

* `Deformation.ToposThickening.LiftDiagram.liftingObstruction_eq_zero_iff`: **Stacks 08UG**,
  clause (1), on the `Ext` side — the class of Step 1 of the source's proof vanishes if and only
  if the difference homomorphism `ξ` factors through the degree `0` term of `NL(α)`, which by
  Steps 2 and 3 of the source's proof is the existence of a lift.
* `Deformation.ToposThickening.LiftDiagram.Lift.equivDerivation` and
  `Deformation.ToposThickening.factorizationEquivCokernelHom`: the two principal homogeneous
  space structures the bijection of Steps 2 and 3 compares, each trivialized at a chosen point,
  and `Deformation.ToposThickening.LiftDiagram.liftEquivFactorization`, that bijection built
  from them and an identification of the two acting groups.
* `Deformation.ToposThickening.LiftDiagram.liftTranslate_zero`,
  `LiftDiagram.liftTranslate_add` and `LiftDiagram.existsUnique_liftTranslate`:
  **Stacks 08UG**, clause (2), the lifts form a principal homogeneous space under
  `Hom(H⁰(NL(α)), G₂)`.
* `Deformation.ToposThickening.LiftDiagram.translate_existsUnique`: the same principal
  homogeneous space structure, proved outright for the concrete acting group
  `LiftDiagram.Derivation` — any lift is carried to any other by exactly one derivation, and
  translating a lift by a derivation is again a lift.

## Implementation notes

The two-term structure of `NL(α)` is supplied as the distinguished triangle of
`AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm`, as in the ringed-space twin
`AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff`
(`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentLiftingObstruction.lean:245`).

Clause (1) is proved here with nothing assumed: `liftingObstruction_eq_zero_iff` states the
vanishing criterion for the factorizations of `ξ` through the degree `0` term themselves,
rather than for a type assumed to be equivalent to them. The bijection of Steps 1 to 3 of the
source's proof between those factorizations and the lifts of the diagram is *not* available:
Step 1 reads it off the presentation `O_{B'₁}[ℰ] ↠ O₁` of the sheaf of sets
`ℰ = O'₁ ×_{O₂} O'₂`, and descends a map out of `ℐ'/(ℐ')²` along the surjection `ℐ' ↠ ℐ` with
kernel `𝒥₁·O_{B'₁}[ℰ]`; neither that presentation nor that surjection is in the library, as the
implementation notes of
`StacksFrontier/CategoryTheory/Sites/Modules/ConormalIdealRestriction.lean` and of
`StacksFrontier/Deformation/ToposThickening/SolutionIsomorphism.lean` record. What is constructed
instead is the pair of principal homogeneous space structures that bijection compares:
`Lift.equivDerivation` trivializes the lifts at a chosen lift over the concrete acting group
`LiftDiagram.Derivation`, `factorizationEquivCokernelHom` trivializes the factorizations at a
chosen factorization over `Hom(H⁰(NL(α)), G₂)`, and `LiftDiagram.liftEquivFactorization` glues
the two. Its one remaining input is an identification of those two groups — the source's own
`Hom_{O₁}(Ω_{O₁/O_{B₁}}, g_*G₂) = Ext⁰(Lg^*NL_{O₁/O_{B₁}}, G₂)` — which is proved neither here
nor in the ringed-space twin.

The clause (2) statements written with the naive cotangent complex, `liftTranslate_zero`,
`liftTranslate_add` and `existsUnique_liftTranslate`, still carry that bijection as the
hypothesis `e`, inherited from the ringed-space twin; the concrete `translate_existsUnique`
below carries nothing. What is new here throughout is that the type of lifts is the concrete
`LiftDiagram.Lift` of the source's diagram rather than an abstract parameter.

The concrete torsor statement `LiftDiagram.translate_existsUnique` carries no such hypothesis:
it is proved from the diagram, section by section. Its acting group is the section-wise
`LiftDiagram.Derivation`, written as a derivation out of `O'₁` rather than out of `O₁`, because
the reduction `O'₁ ⟶ O₁` is only *locally* surjective, so a map out of `O₁` is not determined
section by section by its pullback. Its identification with
`Hom_{O₁}(Ω_{O₁/O_{B₁}}, g_*G₂)` is not proved here; neither is the corresponding
identification in the ringed-space twin.

The ideal module `G` of a layer is carried as a sheaf of modules on the reduced structure sheaf
together with a section-wise identification of it with the kernel of the reduction, as in
`Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening`, rather
than as the kernel subobject: that is what makes the two prescribed maps `c` and `ν` statable.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u w v₂ u₂ v₃ u₃

namespace Deformation.ToposThickening

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- A section of a sheaf of commutative rings, read as a scalar for modules over the underlying
sheaf of rings. -/
public def toRingSection {O : Sheaf J CommRingCat.{w}} {U : Cᵒᵖ} (a : O.obj.obj U) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf (O))).obj.obj U := a

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Two morphisms of sheaves of commutative rings agreeing on all sections are equal. -/
public theorem sheafHom_ext {F G : Sheaf J CommRingCat.{w}} {f g : F ⟶ G}
    (h : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), f.hom.app U x = g.hom.app U x) : f = g :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext (h U))))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A morphism of sheaves of commutative rings commutes with the restriction maps of the
site. -/
public theorem sheafHom_naturality_apply {F G : Sheaf J CommRingCat.{w}} (f : F ⟶ G)
    {U V : Cᵒᵖ} (h : U ⟶ V) (x : F.obj.obj U) :
    f.hom.app V (F.obj.map h x) = G.obj.map h (f.hom.app U x) :=
  congrArg (fun k : F.obj.obj U ⟶ G.obj.obj V => k.hom x) (f.hom.naturality h)

/-- One layer of the diagram of [Stacks Project, Tag 08UG]: a first order thickening
`O_{B'} ⟶ O_B` of a base, a first order thickening `O' ⟶ O` of the source over it, and the
module identifying the ideal of the upper thickening. The underlying topoi are identified, as
in the source's convention, so both thickenings are rows of sheaves on the one site. -/
public structure LiftSquare where
  /-- The reduced structure sheaf of the base. -/
  OB : Sheaf J CommRingCat.{w}
  /-- The thickened structure sheaf of the base. -/
  OB' : Sheaf J CommRingCat.{w}
  /-- The reduced structure sheaf of the source. -/
  O : Sheaf J CommRingCat.{w}
  /-- The thickened structure sheaf of the source. -/
  O' : Sheaf J CommRingCat.{w}
  /-- The reduction of the base thickening. -/
  baseReduction : OB' ⟶ OB
  /-- The reduction of the source thickening. -/
  reduction : O' ⟶ O
  /-- The structure map of the reduced square. -/
  f : OB ⟶ O
  /-- The structure map of the thickened square. -/
  f' : OB' ⟶ O'
  /-- The square of ringed topoi commutes. -/
  comm : f' ≫ reduction = baseReduction ≫ f
  /-- The base reduction is locally surjective. -/
  baseLocallySurjective : Presheaf.IsLocallySurjective J baseReduction.hom
  /-- The ideal of the base thickening has square zero. -/
  baseSquareZero : ∀ U : Cᵒᵖ, (RingHom.ker (baseReduction.hom.app U).hom) ^ 2 = ⊥
  /-- The source reduction is locally surjective. -/
  locallySurjective : Presheaf.IsLocallySurjective J reduction.hom
  /-- The ideal of the source thickening has square zero. -/
  squareZero : ∀ U : Cᵒᵖ, (RingHom.ker (reduction.hom.app U).hom) ^ 2 = ⊥
  /-- The module identified with the ideal of the source thickening. -/
  G : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))
  /-- The identification of `G` with the ideal of the source thickening. -/
  kernelInclusion :
    (SheafOfModules.restrictScalars
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O')
      (R' := Stacks.SheafOfModules.Tensor.ringSheaf O)
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map reduction)).obj G ⟶
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (O')))
  /-- The chosen inclusion lands in the ideal. -/
  kernelZero : ∀ (U : Cᵒᵖ) (m : G.val.obj U),
    reduction.hom.app U (show O'.obj.obj U from kernelInclusion.val.app U m) = 0
  /-- The chosen inclusion identifies `G` with the whole ideal, section by section. -/
  kernelUniversal : ∀ (U : Cᵒᵖ) (a : O'.obj.obj U), reduction.hom.app U a = 0 →
    ∃! m : G.val.obj U, (show O'.obj.obj U from kernelInclusion.val.app U m) = a

namespace LiftSquare

variable {J}

/-- The section of the thickened structure sheaf attached to a section of the ideal module. -/
public noncomputable def incl (S : LiftSquare J) {U : Cᵒᵖ} (m : S.G.val.obj U) :
    S.O'.obj.obj U :=
  S.kernelInclusion.val.app U m

/-- The inclusion of the ideal module is additive on sections. -/
public theorem incl_add (S : LiftSquare J) {U : Cᵒᵖ} (m n : S.G.val.obj U) :
    S.incl (m + n) = S.incl m + S.incl n :=
  map_add (S.kernelInclusion.val.app U).hom m n

/-- The inclusion of the ideal module sends `0` to `0`. -/
public theorem incl_zero (S : LiftSquare J) {U : Cᵒᵖ} :
    S.incl (0 : S.G.val.obj U) = 0 :=
  map_zero (S.kernelInclusion.val.app U).hom

/-- The inclusion of the ideal module is injective on sections. -/
public theorem incl_injective (S : LiftSquare J) {U : Cᵒᵖ} :
    Function.Injective (S.incl (U := U)) := by
  intro m n h
  obtain ⟨p, -, hp⟩ := S.kernelUniversal U (S.incl m) (S.kernelZero U m)
  exact (hp m rfl).trans (hp n h.symm).symm

/-- A section of the thickened structure sheaf killed by the reduction comes from the ideal
module. -/
public theorem exists_incl (S : LiftSquare J) {U : Cᵒᵖ} (a : S.O'.obj.obj U)
    (ha : S.reduction.hom.app U a = 0) : ∃ m : S.G.val.obj U, S.incl m = a := by
  obtain ⟨m, hm, -⟩ := S.kernelUniversal U a ha
  exact ⟨m, hm⟩

/-- The reduction kills the image of the ideal module. -/
public theorem reduction_incl (S : LiftSquare J) {U : Cᵒᵖ} (m : S.G.val.obj U) :
    S.reduction.hom.app U (S.incl m) = 0 :=
  S.kernelZero U m

/-- The inclusion of the ideal module commutes with the restriction maps of the site. -/
public theorem incl_naturality (S : LiftSquare J) {U V : Cᵒᵖ} (h : U ⟶ V)
    (m : S.G.val.obj U) :
    S.incl (show S.G.val.obj V from S.G.val.map h m) = S.O'.obj.map h (S.incl m) :=
  PresheafOfModules.naturality_apply S.kernelInclusion.val h m

/-- The inclusion of the ideal module is compatible with differences of sections. -/
public theorem incl_sub (S : LiftSquare J) {U : Cᵒᵖ} (m n : S.G.val.obj U) :
    S.incl (m - n) = S.incl m - S.incl n :=
  map_sub (S.kernelInclusion.val.app U).hom m n

/-- Scalars act on the ideal through the reduction: the product of a section of the thickened
structure sheaf with a section of the ideal is the image of the action of its reduction. -/
public theorem mul_incl (S : LiftSquare J) {U : Cᵒᵖ} (a : S.O'.obj.obj U) (m : S.G.val.obj U) :
    a * S.incl m = S.incl (toRingSection J (S.reduction.hom.app U a) • m) :=
  ((S.kernelInclusion.val.app U).hom.map_smul' (toRingSection J a) m).symm

/-- The product of two sections of the ideal vanishes: the ideal has square zero. -/
public theorem incl_mul_incl (S : LiftSquare J) {U : Cᵒᵖ} (m n : S.G.val.obj U) :
    S.incl m * S.incl n = 0 := by
  have hmem : S.incl m * S.incl n ∈
      (RingHom.ker (S.reduction.hom.app U).hom) * (RingHom.ker (S.reduction.hom.app U).hom) :=
    Ideal.mul_mem_mul (RingHom.mem_ker.2 (S.reduction_incl m))
      (RingHom.mem_ker.2 (S.reduction_incl n))
  rw [← pow_two, S.squareZero U] at hmem
  simpa using hmem

end LiftSquare

/-- **Stacks Project, Tag 08UH and Tag 08UI.** The displayed commutative diagram of morphisms of
ringed topoi of [Stacks Project, Tag 08UG] together with its diagram of exact ideal rows: two
layers, the comparison morphisms `g`, `gB`, `gB'` running from the index `1` layer to the index
`2` layer (the direction of `g^{-1}` in the source, the underlying topoi being identified), and
the comparison `ν` of the two ideal modules. The comparison of the two *thickened* sources is
absent: producing it is the lifting problem of Tag 08UG. -/
@[stacks 08UH "the displayed commutative diagram of morphisms of ringed topoi, with the \
underlying topoi identified as in the source's convention and its own reduction",
  stacks 08UI "the displayed diagram of exact ideal rows: the two exact rows of each layer are \
the ideal sequences of its two first order thickenings, and the comparison ν of the two upper \
ideals is `nu`, compatible by `nu_base` with the two maps from the base ideals"]
public structure LiftDiagram where
  /-- The front layer, index `1` in the source. -/
  front : LiftSquare J
  /-- The back layer, index `2` in the source. -/
  back : LiftSquare J
  /-- The comparison of the reduced source structure sheaves. -/
  g : front.O ⟶ back.O
  /-- The comparison of the reduced base structure sheaves. -/
  gB : front.OB ⟶ back.OB
  /-- The comparison of the thickened base structure sheaves. -/
  gB' : front.OB' ⟶ back.OB'
  /-- The comparison of sources lies over the comparison of bases. -/
  g_comm : gB ≫ back.f = front.f ≫ g
  /-- The square of bases commutes. -/
  gB_comm : gB' ≫ back.baseReduction = front.baseReduction ≫ gB
  /-- The comparison of the two ideal modules, linear over the front structure sheaf. -/
  nu : front.G ⟶ (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map g)).obj back.G
  /-- The comparison of ideals is compatible with the two maps from the base ideals. -/
  nu_base : ∀ (U : Cᵒᵖ) (a : front.OB'.obj.obj U) (m : front.G.val.obj U),
    front.f'.hom.app U a = front.incl m →
      back.f'.hom.app U (gB'.hom.app U a) =
        back.incl (show back.G.val.obj U from nu.val.app U m)

/-- The data a derivation of a first order thickening is a derivation *of*: a thickened
structure sheaf with its reduction, the thickened base mapping into it, the module identified
with its ideal, and the module the derivation takes values in, over a possibly different
reduced structure sheaf reached by the comparison `g`.

Both a `LiftDiagram` and a solution of a ringed-topos extension problem give one, which is why
the additive group of derivations below is stated at this generality and not twice. -/
public structure DerivationSituation where
  /-- The reduced structure sheaf of the source. -/
  O : Sheaf J CommRingCat.{w}
  /-- The thickened structure sheaf of the source. -/
  O' : Sheaf J CommRingCat.{w}
  /-- The thickened structure sheaf of the base. -/
  OB' : Sheaf J CommRingCat.{w}
  /-- The reduction of the source thickening. -/
  reduction : O' ⟶ O
  /-- The structure map of the thickened square. -/
  f' : OB' ⟶ O'
  /-- The module identified with the ideal of the source thickening. -/
  I : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))
  /-- The identification of `I` with that ideal. -/
  inclusion :
    (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map reduction)).obj I ⟶
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (O')))
  /-- The reduced structure sheaf the values of a derivation are taken over. -/
  Otarget : Sheaf J CommRingCat.{w}
  /-- The comparison to it. -/
  g : O ⟶ Otarget
  /-- The module a derivation takes its values in. -/
  G : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (Otarget)))

namespace DerivationSituation

variable {J}

/-- The section of the thickened structure sheaf attached to a section of the ideal module. -/
public noncomputable def incl (T : DerivationSituation J) {U : Cᵒᵖ} (m : T.I.val.obj U) :
    T.O'.obj.obj U :=
  T.inclusion.val.app U m

end DerivationSituation

section

variable {J}

/-- A *derivation* of such a situation: a section-wise additive map `O' ⟶ G`, natural in the
object of the site, satisfying the Leibniz rule with scalars acting through the reduction and
the comparison `g`, and vanishing both on the ideal and on the image of the thickened base. -/
@[ext]
public structure Derivation (T : DerivationSituation J) where
  /-- The underlying section-wise map. -/
  toFun : ∀ U : Cᵒᵖ, T.O'.obj.obj U → T.G.val.obj U
  /-- The map is additive on sections. -/
  map_add' : ∀ (U : Cᵒᵖ) (x y : T.O'.obj.obj U),
    toFun U (x + y) = toFun U x + toFun U y
  /-- The map commutes with the restriction maps of the site. -/
  naturality : ∀ {U V : Cᵒᵖ} (h : U ⟶ V) (x : T.O'.obj.obj U),
    toFun V (T.O'.obj.map h x) = show T.G.val.obj V from T.G.val.map h (toFun U x)
  /-- The Leibniz rule, the scalars acting through the reduction and the comparison `g`. -/
  leibniz : ∀ (U : Cᵒᵖ) (x y : T.O'.obj.obj U),
    toFun U (x * y) =
      toRingSection J (T.g.hom.app U (T.reduction.hom.app U x)) • toFun U y +
        toRingSection J (T.g.hom.app U (T.reduction.hom.app U y)) • toFun U x
  /-- The map vanishes on the ideal of the thickening. -/
  map_kernel : ∀ (U : Cᵒᵖ) (m : T.I.val.obj U), toFun U (T.incl m) = 0
  /-- The map vanishes on the image of the thickened base. -/
  map_base : ∀ (U : Cᵒᵖ) (a : T.OB'.obj.obj U), toFun U (T.f'.hom.app U a) = 0

namespace Derivation

variable {T : DerivationSituation J}

/-- Two derivations agreeing on every section are equal. -/
public theorem ext_apply {δ ε : Derivation T}
    (h : ∀ (U : Cᵒᵖ) (x : T.O'.obj.obj U), δ.toFun U x = ε.toFun U x) : δ = ε :=
  Derivation.ext (funext fun U => funext fun x => h U x)

/-- A derivation kills the zero section. -/
public theorem map_zero (δ : Derivation T) (U : Cᵒᵖ) : δ.toFun U 0 = 0 := by
  have h := δ.map_add' U 0 0
  rw [add_zero] at h
  have h' : δ.toFun U 0 + 0 = δ.toFun U 0 + δ.toFun U 0 := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h').symm

/-- A derivation kills the unit section: the unit is in the image of the thickened base. -/
public theorem map_one (δ : Derivation T) (U : Cᵒᵖ) : δ.toFun U 1 = 0 := by
  have h1 : T.f'.hom.app U (1 : T.OB'.obj.obj U) = 1 := by simp
  rw [← h1]
  exact δ.map_base U 1

/-- The zero derivation. -/
public instance : Zero (Derivation T) where
  zero :=
    { toFun := fun _ _ => 0
      map_add' := fun _ _ _ => (add_zero (0 : _)).symm
      naturality := fun h _ => ((T.G.val.map h).hom.map_zero).symm
      leibniz := fun _ _ _ => by simp
      map_kernel := fun _ _ => rfl
      map_base := fun _ _ => rfl }

/-- The value of the zero derivation. -/
@[simp]
public theorem zero_toFun (U : Cᵒᵖ) (x : T.O'.obj.obj U) :
    (0 : Derivation T).toFun U x = 0 := rfl

/-- The sum of two derivations. -/
public instance : Add (Derivation T) where
  add δ ε :=
    { toFun := fun U x => δ.toFun U x + ε.toFun U x
      map_add' := fun U x y => by simp only [δ.map_add', ε.map_add']; abel
      naturality := fun h x => by
        simp only [δ.naturality, ε.naturality]
        exact (_root_.map_add _ _ _).symm
      leibniz := fun U x y => by simp only [δ.leibniz, ε.leibniz, smul_add]; abel
      map_kernel := fun U m => by rw [δ.map_kernel, ε.map_kernel, add_zero]
      map_base := fun U a => by rw [δ.map_base, ε.map_base, add_zero] }

/-- The value of a sum of derivations. -/
@[simp]
public theorem add_toFun (δ ε : Derivation T) (U : Cᵒᵖ) (x : T.O'.obj.obj U) :
    (δ + ε).toFun U x = δ.toFun U x + ε.toFun U x := rfl

end Derivation

end

namespace LiftDiagram

variable {J}

/-- The comparison of the two ideal modules, on sections. -/
public noncomputable def nuSection (D : LiftDiagram J) {U : Cᵒᵖ} (m : D.front.G.val.obj U) :
    D.back.G.val.obj U :=
  D.nu.val.app U m

/-- The comparison of ideal modules is additive on sections. -/
public theorem nuSection_add (D : LiftDiagram J) {U : Cᵒᵖ} (m n : D.front.G.val.obj U) :
    D.nuSection (m + n) = D.nuSection m + D.nuSection n :=
  map_add (D.nu.val.app U).hom m n

/-- A morphism fitting into the diagram of [Stacks Project, Tag 08UG] compatibly with `ν`: with
the underlying topoi identified, a homomorphism `O'₁ ⟶ O'₂` of sheaves of commutative rings
commuting with the two reductions, with the two structure maps from the thickened bases, and
inducing `ν` on the two ideals. -/
public structure Lift (D : LiftDiagram J) where
  /-- The homomorphism of the two thickened structure sheaves. -/
  hom : D.front.O' ⟶ D.back.O'
  /-- It is over the comparison of the reduced structure sheaves. -/
  reduction_comm : hom ≫ D.back.reduction = D.front.reduction ≫ D.g
  /-- It is under the comparison of the thickened base structure sheaves. -/
  base_comm : D.front.f' ≫ hom = D.gB' ≫ D.back.f'
  /-- It induces `ν` on the two ideals. -/
  kernel_comm : ∀ (U : Cᵒᵖ) (m : D.front.G.val.obj U),
    hom.hom.app U (D.front.incl m) = D.back.incl (D.nuSection m)

namespace Lift

variable {D : LiftDiagram J}

/-- A lift is determined by the underlying homomorphism of sheaves of rings. -/
@[ext]
public theorem ext {p q : Lift D} (h : p.hom = q.hom) : p = q := by
  cases p; cases q; cases h; rfl

/-- The reduction of a lift of a section is the comparison of its reduction. -/
public theorem reduction_apply (p : Lift D) {U : Cᵒᵖ} (a : D.front.O'.obj.obj U) :
    D.back.reduction.hom.app U (p.hom.hom.app U a) =
      D.g.hom.app U (D.front.reduction.hom.app U a) :=
  congrArg (fun k : D.front.O' ⟶ D.back.O => k.hom.app U a) p.reduction_comm

/-- A lift agrees with the comparison of thickened bases on the image of the base. -/
public theorem base_apply (p : Lift D) {U : Cᵒᵖ} (a : D.front.OB'.obj.obj U) :
    p.hom.hom.app U (D.front.f'.hom.app U a) =
      D.back.f'.hom.app U (D.gB'.hom.app U a) :=
  congrArg (fun k : D.front.OB' ⟶ D.back.O' => k.hom.app U a) p.base_comm

end Lift

/-! ### The principal homogeneous space structure, proved for the concrete acting group -/

/-- The derivation situation of the diagram: its front square, with values in the ideal module
of the back square through the comparison `g`. The derivations of the diagram are exactly the
derivations of this situation, so they carry the additive group of
`Deformation.ToposThickening.Derivation`. -/
public noncomputable abbrev toSituation (D : LiftDiagram J) : DerivationSituation J where
  O := D.front.O
  O' := D.front.O'
  OB' := D.front.OB'
  reduction := D.front.reduction
  f' := D.front.f'
  I := D.front.G
  inclusion := D.front.kernelInclusion
  Otarget := D.back.O
  g := D.g
  G := D.back.G

/-- The ideal inclusion of the situation of a diagram is the one of its front square. -/
@[simp]
public theorem toSituation_incl (D : LiftDiagram J) {U : Cᵒᵖ} (m : D.front.G.val.obj U) :
    D.toSituation.incl m = D.front.incl m := rfl

/-- The base structure map of the situation of a diagram is the one of its front square. -/
@[simp]
public theorem toSituation_f' (D : LiftDiagram J) : D.toSituation.f' = D.front.f' := rfl

/-- Translating a lift of the diagram by a derivation: the homomorphism
`x ↦ φ(x) + δ(x)`. -/
public noncomputable def translate {D : LiftDiagram J} (p : Lift D) (δ : Derivation D.toSituation) :
    Lift D where
  hom := ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom
        { toFun := fun x => p.hom.hom.app U x + D.back.incl (δ.toFun U x)
          map_one' := by
            rw [δ.map_one U, D.back.incl_zero, add_zero]
            simp
          map_mul' := fun x y => by
            have hqx : p.hom.hom.app U x * D.back.incl (δ.toFun U y) =
                D.back.incl (toRingSection J
                  (D.g.hom.app U (D.front.reduction.hom.app U x)) • δ.toFun U y) := by
              rw [D.back.mul_incl, p.reduction_apply]
            have hpy : p.hom.hom.app U y * D.back.incl (δ.toFun U x) =
                D.back.incl (toRingSection J
                  (D.g.hom.app U (D.front.reduction.hom.app U y)) • δ.toFun U x) := by
              rw [D.back.mul_incl, p.reduction_apply]
            have h0 : D.back.incl (δ.toFun U x) * D.back.incl (δ.toFun U y) = 0 :=
              D.back.incl_mul_incl _ _
            have hp : p.hom.hom.app U (x * y) =
                p.hom.hom.app U x * p.hom.hom.app U y := by simp
            rw [hp, δ.leibniz U x y, D.back.incl_add, ← hqx, ← hpy]
            linear_combination -h0
          map_zero' := by rw [δ.map_zero U, D.back.incl_zero, add_zero]; simp
          map_add' := fun x y => by
            have hp : p.hom.hom.app U (x + y) =
                p.hom.hom.app U x + p.hom.hom.app U y := by simp
            rw [hp, δ.map_add' U x y, D.back.incl_add]
            abel }
      naturality := fun {U V} h => by
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change p.hom.hom.app V (D.front.O'.obj.map h x) +
            D.back.incl (δ.toFun V (D.front.O'.obj.map h x)) =
          D.back.O'.obj.map h (p.hom.hom.app U x + D.back.incl (δ.toFun U x))
        rw [δ.naturality h x, D.back.incl_naturality, sheafHom_naturality_apply]
        exact (map_add _ _ _).symm }
  reduction_comm := by
    refine sheafHom_ext J fun U x => ?_
    change D.back.reduction.hom.app U
        (p.hom.hom.app U x + D.back.incl (δ.toFun U x)) =
      D.g.hom.app U (D.front.reduction.hom.app U x)
    rw [map_add, D.back.reduction_incl, add_zero, p.reduction_apply]
  base_comm := by
    refine sheafHom_ext J fun U a => ?_
    change p.hom.hom.app U (D.toSituation.f'.hom.app U a) +
        D.back.incl (δ.toFun U (D.toSituation.f'.hom.app U a)) =
      D.back.f'.hom.app U (D.gB'.hom.app U a)
    rw [δ.map_base U a, D.back.incl_zero, add_zero]
    simp only
    exact p.base_apply a
  kernel_comm := fun U m => by
    change p.hom.hom.app U (D.toSituation.incl m) +
      D.back.incl (δ.toFun U (D.toSituation.incl m)) = D.back.incl (D.nuSection m)
    rw [δ.map_kernel U m, D.back.incl_zero, add_zero]
    simp only [toSituation_incl]
    exact p.kernel_comm U m

/-- The formula determining a translate. -/
@[simp]
public theorem translate_apply {D : LiftDiagram J} (p : Lift D) (δ : Derivation D.toSituation)
    (U : Cᵒᵖ) (x : D.front.O'.obj.obj U) :
    (translate p δ).hom.hom.app U x = p.hom.hom.app U x + D.back.incl (δ.toFun U x) := rfl

/-- The zero derivation acts trivially. -/
public theorem translate_zero {D : LiftDiagram J} (p : Lift D) : translate p 0 = p := by
  refine Lift.ext (sheafHom_ext J fun U x => ?_)
  rw [translate_apply, Derivation.zero_toFun, D.back.incl_zero, add_zero]

/-- The action of derivations on lifts is additive. -/
public theorem translate_add {D : LiftDiagram J} (p : Lift D) (δ ε : Derivation D.toSituation) :
    translate (translate p δ) ε = translate p (δ + ε) := by
  refine Lift.ext (sheafHom_ext J fun U x => ?_)
  rw [translate_apply, translate_apply, translate_apply, Derivation.add_toFun,
    D.back.incl_add]
  abel

section Difference

variable {D : LiftDiagram J}

/-- The difference of two lifts lies in the ideal of the back layer. -/
public theorem exists_diff (p q : Lift D) (U : Cᵒᵖ) (x : D.front.O'.obj.obj U) :
    ∃ m : D.back.G.val.obj U,
      D.back.incl m = q.hom.hom.app U x - p.hom.hom.app U x := by
  refine D.back.exists_incl _ ?_
  rw [map_sub, q.reduction_apply, p.reduction_apply, sub_self]

/-- The section of the ideal by which two lifts differ. -/
public noncomputable def diff (p q : Lift D) (U : Cᵒᵖ) (x : D.front.O'.obj.obj U) :
    D.back.G.val.obj U :=
  (exists_diff p q U x).choose

/-- The defining property of the difference of two lifts. -/
public theorem incl_diff (p q : Lift D) (U : Cᵒᵖ) (x : D.front.O'.obj.obj U) :
    D.back.incl (diff p q U x) = q.hom.hom.app U x - p.hom.hom.app U x :=
  (exists_diff p q U x).choose_spec

/-- The difference of two lifts of the diagram is a derivation. -/
public noncomputable def derivationOfLifts (p q : Lift D) : Derivation D.toSituation where
  toFun := diff p q
  map_add' U x y := by
    refine D.back.incl_injective ?_
    rw [incl_diff, D.back.incl_add, incl_diff, incl_diff, map_add, map_add]
    abel
  naturality {U V} h x := by
    refine D.back.incl_injective ?_
    rw [incl_diff, D.back.incl_naturality, incl_diff, sheafHom_naturality_apply,
      sheafHom_naturality_apply]
    exact (map_sub _ _ _).symm
  leibniz U x y := by
    refine D.back.incl_injective ?_
    have hqx := q.reduction_apply (U := U) x
    have hpy := p.reduction_apply (U := U) y
    rw [D.back.incl_add, ← hqx, ← hpy, ← D.back.mul_incl, ← D.back.mul_incl,
      incl_diff, incl_diff, incl_diff, map_mul, map_mul]
    ring
  map_kernel U m := by
    refine D.back.incl_injective ?_
    simp only [toSituation_incl]
    rw [incl_diff, q.kernel_comm, p.kernel_comm, sub_self, D.back.incl_zero]
  map_base U a := by
    refine D.back.incl_injective ?_
    rw [incl_diff, q.base_apply, p.base_apply, sub_self, D.back.incl_zero]

/-- The difference derivation of two lifts, on sections. -/
@[simp]
public theorem derivationOfLifts_toFun (p q : Lift D) (U : Cᵒᵖ)
    (x : D.front.O'.obj.obj U) : (derivationOfLifts p q).toFun U x = diff p q U x := rfl

/-- Translating a lift by the difference derivation produces the other lift. -/
public theorem translate_derivationOfLifts (p q : Lift D) :
    translate p (derivationOfLifts p q) = q := by
  refine Lift.ext (sheafHom_ext J fun U x => ?_)
  change p.hom.hom.app U x + D.back.incl (diff p q U x) = q.hom.hom.app U x
  rw [incl_diff]
  abel

/-- **Stacks Project, Tag 08UG**, clause (2). The morphisms
`(Sh(C'₂), O'₂) ⟶ (Sh(C'₁), O'₁)` fitting into the source's diagram compatibly with `ν` form a
principal homogeneous space: any one of them is carried to any other by exactly one derivation
of the diagram. Together with `translate_zero` and `translate_add` this is the free and
transitive action of the source's clause (2), with the acting group written as the group of
section-wise derivations out of `O'₁` rather than as
`Hom_{O₁}(Ω_{O₁/O_{B₁}}, g_*G₂)`. -/
@[stacks 08UG "clause (2): the lifts are a principal homogeneous space under Derivation"]
public theorem translate_existsUnique (p q : Lift D) :
    ∃! δ : Derivation D.toSituation, translate p δ = q := by
  refine ⟨derivationOfLifts p q, translate_derivationOfLifts p q, fun ε hε => ?_⟩
  refine Derivation.ext_apply fun U x => ?_
  refine D.back.incl_injective ?_
  have h : p.hom.hom.app U x + D.back.incl (ε.toFun U x) = q.hom.hom.app U x :=
    congrArg (fun r : Lift D => r.hom.hom.app U x) hε
  rw [derivationOfLifts_toFun, incl_diff, ← h]
  abel

/-- Trivialization of the morphisms fitting into the source's diagram at a chosen one: a lift
`p` identifies them with the derivations of the diagram, a lift `q` corresponding to the unique
derivation carrying `p` to `q`. This is the bijection underlying clause (2) of
[Stacks Project, Tag 08UG] for the concrete acting group `LiftDiagram.Derivation`, and it is
the half of the bijection of Steps 2 and 3 of the source's proof that the diagram alone
provides. -/
public noncomputable def Lift.equivDerivation (p : Lift D) : Lift D ≃ Derivation D.toSituation where
  toFun q := derivationOfLifts p q
  invFun δ := translate p δ
  left_inv q := translate_derivationOfLifts p q
  right_inv δ :=
    (translate_existsUnique p (translate p δ)).unique
      (translate_derivationOfLifts p (translate p δ)) rfl

/-- The derivation attached to a lift by the trivialization at `p` is the difference
derivation. -/
@[simp]
public theorem Lift.equivDerivation_apply (p q : Lift D) :
    p.equivDerivation q = derivationOfLifts p q := rfl

/-- The lift attached to a derivation by the trivialization at `p` is the translate of `p`. -/
@[simp]
public theorem Lift.equivDerivation_symm_apply (p : Lift D) (δ : Derivation D.toSituation) :
    p.equivDerivation.symm δ = translate p δ := rfl

end Difference

end LiftDiagram

/-! ### Stacks 08UG through the naive cotangent complex -/

section NaiveCotangent

open AlgebraicGeometry.RingedSpaceThickening

variable {M : Type u₂} [Category.{v₂} M] [Abelian M] {T : Type u₃} [Category.{v₃} T]
  [HasZeroObject T] [HasShift T ℤ] [Preadditive T] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T]

/-- Trivialization of the factorizations of `ξ : ℐ/ℐ² ⟶ 𝒢` through the degree `0` term of
`NL(α)` at a chosen factorization `θ₀`: a homomorphism `a : H⁰(NL(α)) ⟶ 𝒢` out of the cokernel
of the differential moves `θ₀` to `θ₀ + π ≫ a`, and every factorization arises from exactly one
such `a`. This is the principal homogeneous space structure of clause (2) of
[Stacks Project, Tag 08UG] on the `Ext` side. -/
public noncomputable def factorizationEquivCokernelHom {single : M ⥤ T}
    (P : NaiveCotangentTwoTerm single) (G : M) (ξ : P.conormal ⟶ G)
    (θ₀ : {θ : P.base ⟶ G // P.d ≫ θ = ξ}) :
    {θ : P.base ⟶ G // P.d ≫ θ = ξ} ≃ (cokernel P.d ⟶ G) where
  toFun θ := cokernel.desc P.d (θ.1 - θ₀.1) (by
    rw [Preadditive.comp_sub, θ.2, θ₀.2, sub_self])
  invFun a := ⟨θ₀.1 + cokernel.π P.d ≫ a, by
    rw [Preadditive.comp_add, θ₀.2, ← Category.assoc, cokernel.condition, Limits.zero_comp,
      add_zero]⟩
  left_inv θ := by
    refine Subtype.ext ?_
    change θ₀.1 + cokernel.π P.d ≫ cokernel.desc P.d (θ.1 - θ₀.1) _ = θ.1
    rw [cokernel.π_desc]
    abel
  right_inv a := by
    refine (cancel_epi (cokernel.π P.d)).1 ?_
    rw [cokernel.π_desc, add_sub_cancel_left]

namespace LiftDiagram

variable {J}

/-- The bijection of Steps 2 and 3 of the proof of [Stacks Project, Tag 08UG] between the
morphisms fitting into the source's diagram and the factorizations of the difference
homomorphism `ξ` through the degree `0` term of `NL(α)`, built from the two principal
homogeneous space structures it compares: `Lift.equivDerivation` trivializes the lifts at a
chosen lift `p` over the derivations of the diagram, `factorizationEquivCokernelHom`
trivializes the factorizations at a chosen factorization `θ₀` over `Hom(H⁰(NL(α)), G₂)`, and
`κ` identifies the two acting groups — the source's own
`Hom_{O₁}(Ω_{O₁/O_{B₁}}, g_*G₂) = Ext⁰(Lg^*NL_{O₁/O_{B₁}}, G₂)`. -/
public noncomputable def liftEquivFactorization (D : LiftDiagram J) {single : M ⥤ T}
    (P : NaiveCotangentTwoTerm single) (G : M) (ξ : P.conormal ⟶ G) (p : D.Lift)
    (θ₀ : {θ : P.base ⟶ G // P.d ≫ θ = ξ}) (κ : Derivation D.toSituation ≃ (cokernel P.d ⟶ G)) :
    D.Lift ≃ {θ : P.base ⟶ G // P.d ≫ θ = ξ} :=
  (p.equivDerivation.trans κ).trans (factorizationEquivCokernelHom P G ξ θ₀).symm

/-- The `Ext`-side half of clause (1) of [Stacks Project, Tag 08UG]. This does NOT carry that
clause, and the tag attribute is deliberately absent: the clause asserts that the
class vanishes exactly when a morphism of ringed topoi fitting the source's diagram exists,
whereas this asserts only that it vanishes exactly when `ξ` factors. The two are equivalent
through `liftEquivFactorization`, whose input `κ` is not proved here, so this statement alone is
strictly weaker than the clause. In the situation of the
source's diagram, reduced as in its proof to sheaves of rings on one site, the class in
`Ext¹(NL(α), G₂)` of the difference homomorphism `ξ` of Step 1 of the source's proof vanishes if
and only if `ξ` factors through the degree `0` term of `NL(α)` — the condition which, by Steps 2
and 3 of the source's proof, is the existence of a morphism
`(Sh(C'₂), O'₂) ⟶ (Sh(C'₁), O'₁)` fitting into the source's diagram compatibly with `ν`.

Nothing is assumed: the factorization set is the statement's own right hand side, rather than a
type assumed to be equivalent to it. Its identification with the lifts of the diagram is
`liftEquivFactorization`, built from the two principal homogeneous space structures that
identification compares; the one input that construction still needs is the identification of
the two acting groups, and the implementation notes of this file record why the source's own
route to it — the presentation of Step 1 of its proof — is not available in the library. -/
public theorem liftingObstruction_eq_zero_iff
    {single : M ⥤ T} [single.Full] [single.Faithful] [single.Additive]
    (P : NaiveCotangentTwoTerm single) (G : M) (ξ : P.conormal ⟶ G) :
    liftingObstruction P G ξ = 0 ↔ Nonempty {θ : P.base ⟶ G // P.d ≫ θ = ξ} :=
  AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff P G ξ (Equiv.refl _)

variable {single : M ⥤ T}

/-- Towards clause (2) of [Stacks Project, Tag 08UG], on the hypothesis `e`; untagged, since `e`
is assumed rather than constructed. The zero homomorphism acts trivially on the
morphisms fitting into the source's diagram. -/
public theorem liftTranslate_zero (D : LiftDiagram J) (P : NaiveCotangentTwoTerm single) (G : M)
    (ξ : P.conormal ⟶ G) (e : D.Lift ≃ {θ : P.base ⟶ G // P.d ≫ θ = ξ}) (p : D.Lift) :
    liftTranslate P G ξ e 0 p = p :=
  AlgebraicGeometry.RingedSpaceThickening.liftTranslate_zero P G ξ e p

/-- Towards clause (2) of [Stacks Project, Tag 08UG], on the hypothesis `e`; untagged, since `e`
is assumed rather than constructed. Translation of the morphisms fitting into the
source's diagram is additive in the translating homomorphism. -/
public theorem liftTranslate_add (D : LiftDiagram J) (P : NaiveCotangentTwoTerm single) (G : M)
    (ξ : P.conormal ⟶ G) (e : D.Lift ≃ {θ : P.base ⟶ G // P.d ≫ θ = ξ})
    (a b : cokernel P.d ⟶ G) (p : D.Lift) :
    liftTranslate P G ξ e a (liftTranslate P G ξ e b p) = liftTranslate P G ξ e (a + b) p :=
  AlgebraicGeometry.RingedSpaceThickening.liftTranslate_add P G ξ e a b p

/-- Clause (2) of [Stacks Project, Tag 08UG] on the hypothesis `e`; untagged, since `e` is
assumed rather than constructed. The unconditional carrier of that clause in this file is
`LiftDiagram.translate_existsUnique`, which gives the torsor structure for the concrete acting
group `LiftDiagram.Derivation`. The morphisms
`(Sh(C'₂), O'₂) ⟶ (Sh(C'₁), O'₁)` fitting into the source's diagram compatibly with `ν` form a
principal homogeneous space under `Hom(H⁰(NL(α)), G₂) = Hom(Ω_{O₁/O_{B₁}}, g_*G₂)`: any one of
them is carried to any other by exactly one homomorphism. -/
public theorem existsUnique_liftTranslate (D : LiftDiagram J) (P : NaiveCotangentTwoTerm single)
    (G : M) (ξ : P.conormal ⟶ G) (e : D.Lift ≃ {θ : P.base ⟶ G // P.d ≫ θ = ξ})
    (p q : D.Lift) : ∃! a : cokernel P.d ⟶ G, liftTranslate P G ξ e a p = q :=
  AlgebraicGeometry.RingedSpaceThickening.existsUnique_liftTranslate P G ξ e p q

end LiftDiagram

end NaiveCotangent

end Deformation.ToposThickening

end
