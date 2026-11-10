module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Chart

/-!
# The group of tangent vectors over a framed algebra

Over an algebra carrying a chart of the lifting problem, the tangent vectors of
`StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Action` are identified with the
coordinate derivations of `StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Chart`,
and this file transports the module structure of the latter.  The transported structure does
not depend on the chart where it matters: the scalar multiplication is the intrinsic one
(`Framing.smul_eq`), the action is additive (`Framing.act_add`), and pulling back along an
arbitrary algebra map between framed algebras is additive as soon as a lift exists
(`Framing.pull_add`), because both sides are characterised by the action.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.SmoothLift

open Stacks.SmoothLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : Base B S hS}
  {𝔓 : Problem D} {F : Frame 𝔓} {R : Alg D} (Fr : Framing F R)

/-- The tangent vectors over a framed algebra, as a type carrying the transported module
structure. -/
def Framing.G (_ : Framing F R) : Type u := 𝔓.Tangents R

/-- A tangent vector over a framed algebra, read as an element of the transported group. -/
def Framing.ofT (t : 𝔓.Tangents R) : Fr.G := t

/-- An element of the transported group, read as a tangent vector. -/
def Framing.toT (t : Fr.G) : 𝔓.Tangents R := t

/-- Reading a tangent vector in the transported group and back returns the tangent vector. -/
@[simp] theorem Framing.toT_ofT (t : 𝔓.Tangents R) : Fr.toT (Fr.ofT t) = t := rfl

/-- Reading an element of the transported group as a tangent vector and back gives the element. -/
@[simp] theorem Framing.ofT_toT (t : Fr.G) : Fr.ofT (Fr.toT t) = t := rfl

/-- The additive group structure on the tangent vectors transported from the coordinate
derivations along `Framing.tangentEquiv`. -/
noncomputable instance Framing.instAddCommGroupG : AddCommGroup Fr.G :=
  Fr.tangentEquiv.addCommGroup

/-- The identification of the tangent vectors with the coordinate derivations, as an
isomorphism of groups. -/
noncomputable def Framing.gAddEquiv : Fr.G ≃+ Fr.Der :=
  { Fr.tangentEquiv with
    map_add' := fun t t' =>
      Fr.tangentEquiv.apply_symm_apply (Fr.tangentEquiv t + Fr.tangentEquiv t') }

/-- The module structure on the tangent vectors transported from the coordinate derivations
along `Framing.gAddEquiv`. -/
noncomputable instance Framing.instModuleG : Module (Q D.C R.R) Fr.G :=
  AddEquiv.module (Q D.C R.R) Fr.gAddEquiv

/-- The tangent vectors as a module over the base ring, by restriction of scalars along its
algebra map. -/
noncomputable instance Framing.instModuleBaseG : Module D.A Fr.G :=
  Module.compHom Fr.G (algebraMap D.A (Q D.C R.R))

/-- The scalar multiplications of the base ring and of `Q D.C R.R` on the tangent vectors form a
scalar tower. -/
instance Framing.instIsScalarTowerG : IsScalarTower D.A (Q D.C R.R) Fr.G where
  smul_assoc a q t := by
    change (a • q) • t = algebraMap D.A (Q D.C R.R) a • q • t
    rw [Algebra.smul_def, mul_smul]

/-- The identification of the tangent vectors with the coordinate derivations, as an
isomorphism of modules. -/
noncomputable def Framing.gEquiv : Fr.G ≃ₗ[Q D.C R.R] Fr.Der :=
  AddEquiv.linearEquiv (Q D.C R.R) Fr.gAddEquiv

/-- `Framing.gEquiv` sends a tangent vector to its image under `Framing.tangentEquiv`. -/
theorem Framing.gEquiv_apply (t : Fr.G) : Fr.gEquiv t = Fr.tangentEquiv t := rfl

/-- The inverse of `Framing.gEquiv` is the inverse of `Framing.tangentEquiv`. -/
theorem Framing.gEquiv_symm_apply (δ : Fr.Der) : Fr.gEquiv.symm δ = Fr.tangentEquiv.symm δ := rfl

/-- `Framing.tangentEquiv` is additive. -/
theorem Framing.tangentEquiv_add (t t' : Fr.G) :
    Fr.tangentEquiv (t + t') = Fr.tangentEquiv t + Fr.tangentEquiv t' :=
  map_add Fr.gEquiv t t'

/-- `Framing.tangentEquiv` sends zero to zero. -/
theorem Framing.tangentEquiv_zero : Fr.tangentEquiv (0 : Fr.G) = 0 :=
  map_zero Fr.gEquiv

/-- **The transported scalar multiplication is the intrinsic one.** -/
theorem Framing.smul_eq (a : Q D.C R.R) (t : Fr.G) : Fr.toT (a • t) = (Fr.toT t).smul a := by
  apply Fr.tangentEquiv.injective
  rw [Fr.tangentEquiv_smul]
  exact map_smul Fr.gEquiv a t

/-- **The action is additive.** -/
theorem Framing.act_add (t t' : Fr.G) (z : 𝔓.Lifts R) :
    act (Fr.toT (t + t')) z = act (Fr.toT t) (act (Fr.toT t') z) := by
  apply Fr.liftEquiv.injective
  rw [Fr.liftEquiv_act, Fr.liftEquiv_act, Fr.liftEquiv_act]
  change Fr.translate _ (Fr.tangentEquiv (t + t')) = _
  rw [Fr.tangentEquiv_add, Fr.translate_add]
  rfl

/-- **The zero tangent vector acts trivially.** -/
theorem Framing.act_zero (z : 𝔓.Lifts R) : act (Fr.toT (0 : Fr.G)) z = z := by
  apply Fr.liftEquiv.injective
  rw [Fr.liftEquiv_act]
  change Fr.translate _ (Fr.tangentEquiv (0 : Fr.G)) = _
  rw [Fr.tangentEquiv_zero, Fr.translate_zero]

/-- Two tangent vectors acting in the same way on one lift are equal. -/
theorem Framing.toT_injective_act (z : 𝔓.Lifts R) {t t' : Fr.G}
    (h : act (Fr.toT t) z = act (Fr.toT t') z) : t = t' :=
  Fr.act_injective z h

/-- **Pulling back is additive** along an arbitrary algebra map between framed algebras, as
soon as a lift exists over the source. -/
theorem Framing.pull_add {F' : Frame 𝔓} {R' : Alg D} (Fr' : Framing F' R') (h : R.R →ₐ[D.A] R'.R)
    (z : 𝔓.Lifts R) (t t' : Fr.G) :
    Fr'.ofT ((Fr.toT (t + t')).pull h) =
      Fr'.ofT ((Fr.toT t).pull h) + Fr'.ofT ((Fr.toT t').pull h) := by
  apply Fr'.toT_injective_act (z.pull h)
  rw [Fr'.act_add, Fr'.toT_ofT, Fr'.toT_ofT, Fr'.toT_ofT, act_pull, Fr.act_add, act_pull,
    act_pull]

/-- Pulling back along an arbitrary algebra map between framed algebras commutes with scalar
multiplication, the scalars being mapped by `qMap`. -/
theorem Framing.pull_smul {F' : Frame 𝔓} {R' : Alg D} (Fr' : Framing F' R') (h : R.R →ₐ[D.A] R'.R)
    (a : Q D.C R.R) (t : Fr.G) :
    Fr'.ofT ((Fr.toT (a • t)).pull h) = qMap D.C h a • Fr'.ofT ((Fr.toT t).pull h) := by
  apply congrArg Fr'.ofT
  change _ = Fr'.toT (qMap D.C h a • Fr'.ofT ((Fr.toT t).pull h))
  rw [Fr'.smul_eq, Fr.smul_eq, Fr'.toT_ofT, Problem.Tangents.smul_pull]

end AlgebraicGeometry.Space.SmoothLift
