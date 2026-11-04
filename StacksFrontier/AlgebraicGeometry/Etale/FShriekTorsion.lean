module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksCore.Tactic.StacksAttribute

/-!
# The direct image with compact support of a torsion abelian sheaf is torsion

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site. The direct image with
compact support `f_!` of Stacks 0F6R sends a torsion abelian sheaf on the small étale site of `X`
to a torsion abelian sheaf on the small étale site of `Y`. This is the abelian-sheaf content of
Stacks 0GJX.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_nsmul_eq_zero_etaleStalk` — the stalk of a torsion abelian
  étale sheaf at a geometric point is a torsion abelian group.
* `AlgebraicGeometry.SmallEtale.torsionSheafProperty_of_forall_etaleStalk` — an abelian étale sheaf
  whose stalks at all geometric points are torsion is a torsion abelian sheaf.
* `AlgebraicGeometry.SmallEtale.torsionSheafProperty_fShriekFunctor_obj` — the direct image with
  compact support of a torsion abelian sheaf is a torsion abelian sheaf.

## Implementation notes

The coefficient universe is the cutoff `max (u + 1) v` at which `f_!` is defined, `u` being the
universe of the schemes.

## References

* [Stacks Project, Tag 0GJX](https://stacks.math.columbia.edu/tag/0GJX)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Torsion
open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section DirectSums

/-- A direct sum of torsion abelian monoids is torsion. -/
private theorem exists_nsmul_eq_zero_directSum {ι : Type*} {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)]
    (hM : ∀ (i : ι) (y : M i), ∃ n : ℕ, 0 < n ∧ n • y = 0) (x : ⨁ i, M i) :
    ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  classical
  refine DirectSum.induction_on x ⟨1, Nat.one_pos, smul_zero 1⟩ (fun i y => ?_)
    (fun a b ha hb => ?_)
  · obtain ⟨n, hn, hy⟩ := hM i y
    exact ⟨n, hn, by rw [← map_nsmul, hy, map_zero]⟩
  · obtain ⟨n, hn, ha⟩ := ha
    obtain ⟨m, hm, hb⟩ := hb
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add, mul_comm, mul_smul, ha, smul_zero, zero_add, mul_comm, mul_smul, hb, smul_zero]

end DirectSums

section Stalks

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The germ at a geometric point of a multiple of a section is that multiple of its germ. -/
public theorem etaleGerm_nsmul (t : GeometricPoint S)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) (W : SmallEtale B S hS)
    (q : (geometricPointFiber B S hS t).obj W) (n : ℕ) (a : P.obj (op W)) :
    etaleGerm B S hS t P W q (n • a) = n • etaleGerm B S hS t P W q a := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, etaleGerm_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, etaleGerm_add, ih]

/-- The stalk of a torsion abelian étale sheaf at a geometric point is a torsion abelian group. -/
@[stacks 0GJX "an input to the proof: the stalk of a torsion abelian étale sheaf at a \
geometric point is a torsion abelian group"]
public theorem exists_nsmul_eq_zero_etaleStalk (t : GeometricPoint S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v})
    (hF : torsionSheafProperty (SmallEtale.topology B S hS) F)
    (g : ↑(etaleStalk B S hS t F.obj)) :
    ∃ n : ℕ, 0 < n ∧ n • g = 0 := by
  obtain ⟨W, q, a, rfl⟩ := exists_etaleGerm_eq B S hS t F.obj g
  obtain ⟨R, hR, hkill⟩ := hF W a
  obtain ⟨W', j, hj, q', hq'⟩ := geometricPointFiber_jointly_surjective B S hS t R hR q
  obtain ⟨n, hn, hz⟩ := hkill W' j hj
  refine ⟨n, hn, ?_⟩
  rw [← etaleGerm_map B S hS t F.obj j q q' hq' a,
    ← etaleGerm_nsmul B S hS t F.obj W' q' n (F.obj.map j.op a), hz]
  exact etaleGerm_zero B S hS t F.obj W' q'

/-- An abelian étale sheaf whose stalks at all geometric points are torsion abelian groups is a
torsion abelian sheaf. -/
@[stacks 0GJX "the stalk criterion used by the proof: an abelian étale sheaf whose stalks at \
all geometric points are torsion is a torsion abelian sheaf"]
public theorem torsionSheafProperty_of_forall_etaleStalk
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ (t : GeometricPoint S) (g : ↑(etaleStalk B S hS t F.obj)),
      ∃ n : ℕ, 0 < n ∧ n • g = 0) :
    torsionSheafProperty (SmallEtale.topology B S hS) F := by
  rw [torsionSheafProperty_iff_isLocallyTorsion, isLocallyTorsion_iff_torsionSieve_mem]
  intro V y
  refine SmallEtale.mem_topology_of_jointlySurjective fun x => ?_
  set t := geometricPointOfEtalePoint B S hS V x
  set p := geometricPointOfEtalePointLift B S hS V x
  obtain ⟨n, hn, hz⟩ := hF t (etaleGerm B S hS t F.obj V p y)
  obtain ⟨W, j, q, hq, hzero⟩ :=
    (etaleGerm_eq_zero_iff B S hS t F.obj V p (n • y)).1
      ((etaleGerm_nsmul B S hS t F.obj V p n y).trans hz)
  refine ⟨W, j, ⟨n, hn, ?_⟩, q.1.base default, ?_⟩
  · rwa [← _root_.map_nsmul]
  · have h2 : ((SmallEtale.toScheme B S hS).map j).base (q.1.base default) =
        p.1.base default :=
      congrArg (fun m : t.source ⟶ _ => m.base (default : ↥t.source)) (congrArg Subtype.val hq)
    exact h2.trans (geometricPointOfEtalePointLift_base B S hS V x)

end Stalks

section FShriek

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The direct image with compact support `f_!` of a locally quasi-finite morphism sends a torsion
abelian sheaf on the small étale site of `X` to a torsion abelian sheaf on the small étale site of
`Y`. -/
@[stacks 0GJX "the abelian-sheaf case: `f_!` of a locally quasi-finite morphism sends a \
torsion abelian sheaf to a torsion abelian sheaf. The statement for a general coefficient \
ring is `AlgebraicGeometry.SmallEtale.moduleTorsionCohomologyProperty_moduleFShriekDerivedFunctor`"]
public theorem torsionSheafProperty_fShriekFunctor_obj (F : AbelianSheaf.{u, v} B X)
    (hF : torsionSheafProperty (SmallEtale.topology B X.obj X.property) F) :
    torsionSheafProperty (SmallEtale.topology B Y.obj Y.property)
      ((fShriekFunctor.{u, v} B f).obj F) := by
  refine torsionSheafProperty_of_forall_etaleStalk.{u, v} B Y.obj Y.property _ fun s g => ?_
  refine exists_nsmul_eq_zero_of_iso (fShriekStalkIso.{u, v} B f s F).symm (fun z => ?_) g
  exact exists_nsmul_eq_zero_directSum
    (fun x w => exists_nsmul_eq_zero_etaleStalk.{u, v} B X.obj X.property
      (x.toGeometricPoint B f s) F hF w) z

end FShriek

end AlgebraicGeometry.SmallEtale

end
