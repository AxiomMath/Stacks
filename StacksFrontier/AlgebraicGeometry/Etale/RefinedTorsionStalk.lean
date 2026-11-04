module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.RefinedTorsionLocal

/-!
# The stalk criterion for the refined torsion conditions on an abelian étale sheaf

Let `B` be a big étale site containing a scheme `S`. An abelian sheaf on the small étale site of
`S` cut out by `B` is torsion exactly when its stalks at the geometric points of `S` are torsion
abelian groups; that is `AlgebraicGeometry.SmallEtale.exists_nsmul_eq_zero_etaleStalk` together
with `AlgebraicGeometry.SmallEtale.torsionSheafProperty_of_forall_etaleStalk`. The vanishing and
finiteness theorems for étale cohomology need the same criterion for the two refinements of
torsion in which the annihilator of a local section is constrained relative to a fixed natural
number: a positive power of `l`, or a positive integer coprime to `p`.

Both refinements are instances of `Stacks.Torsion.IsLocallyAnnihilatedBy`, local annihilation by
a prescribed set `N ⊆ ℕ` of admissible annihilators, and the criterion is proved once for that
condition. Neither direction is formal, local annihilation being a condition on a covering sieve
rather than on a section: a germ of a locally annihilated section is annihilated because a
covering sieve acts surjectively on the lifts of a geometric point to the étale neighbourhoods,
which is `AlgebraicGeometry.geometricPointFiber_jointly_surjective`; and conversely the sieve of
arrows along which a section becomes annihilated by a member of `N` is covering because every
point of an étale neighbourhood carries a geometric point lifting to it, so that sieve is jointly
surjective in the sense of `AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective`. The
argument is the one the library's torsion criterion makes; only the set of admissible annihilators
is carried through it unchanged, which is all either refinement asks.

The coefficient universe is the cutoff `max (u + 1) v` of the rest of this development, `u` being
the universe of the schemes.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_mem_nsmul_eq_zero_etaleStalk` and
  `AlgebraicGeometry.SmallEtale.isLocallyAnnihilatedBy_of_forall_etaleStalk` — the two directions
  of the criterion for local annihilation by a prescribed set of integers, packaged as
  `AlgebraicGeometry.SmallEtale.isLocallyAnnihilatedBy_iff_forall_etaleStalk`.
* `AlgebraicGeometry.SmallEtale.isPrimePowerTorsion_iff_forall_etaleStalk` — an abelian étale
  sheaf is `l`-power torsion exactly when every one of its stalks at a geometric point is
  annihilated by a positive power of `l`.
* `AlgebraicGeometry.SmallEtale.isPrimeToCharacteristicTorsion_iff_forall_etaleStalk` — an
  abelian étale sheaf is torsion prime to `p` exactly when every one of its stalks at a geometric
  point is annihilated by a positive integer coprime to `p`.

## References

* [Stacks Project, Tag 0DV7](https://stacks.math.columbia.edu/tag/0DV7)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Torsion

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Generic

/-- **The stalk of a locally `N`-annihilated abelian étale sheaf is annihilated by a member of
`N`.** An element of the stalk is the germ of a section over an étale neighbourhood, a covering
sieve annihilates that section by members of `N`, and the covering sieve acts surjectively on the
lifts of the geometric point, so one of those members annihilates the germ. -/
public theorem exists_mem_nsmul_eq_zero_etaleStalk (N : Set ℕ) (t : GeometricPoint S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v})
    (hF : IsLocallyAnnihilatedBy (SmallEtale.topology B S hS) N F.obj)
    (g : ↑(etaleStalk B S hS t F.obj)) :
    ∃ n ∈ N, n • g = 0 := by
  obtain ⟨W, q, a, rfl⟩ := exists_etaleGerm_eq B S hS t F.obj g
  obtain ⟨R, hR, hkill⟩ := hF W a
  obtain ⟨W', j, hj, q', hq'⟩ := geometricPointFiber_jointly_surjective B S hS t R hR q
  obtain ⟨n, hn, hz⟩ := hkill W' j hj
  refine ⟨n, hn, ?_⟩
  rw [← etaleGerm_map B S hS t F.obj j q q' hq' a,
    ← etaleGerm_nsmul_of_hasColimit B S hS t F.obj W' q' n (F.obj.map j.op a), hz]
  exact etaleGerm_zero B S hS t F.obj W' q'

/-- **Local annihilation by a prescribed set of integers is detected on the stalks at geometric
points.** For a section over an object of the small étale site, the sieve of arrows along which
it becomes annihilated by a member of `N` contains, for every point of the object, an arrow whose
image meets that point: the germ of the section at the geometric point there is annihilated by
some member of `N`. So that sieve is covering. -/
public theorem isLocallyAnnihilatedBy_of_forall_etaleStalk (N : Set ℕ)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ (t : GeometricPoint S) (g : ↑(etaleStalk B S hS t F.obj)), ∃ n ∈ N, n • g = 0) :
    IsLocallyAnnihilatedBy (SmallEtale.topology B S hS) N F.obj := by
  rw [isLocallyAnnihilatedBy_iff_annihilatorSieve_mem]
  intro V y
  refine SmallEtale.mem_topology_of_jointlySurjective fun x ↦ ?_
  set t := geometricPointOfEtalePoint B S hS V x
  set e := geometricPointOfEtalePointLift B S hS V x
  obtain ⟨n, hn, hz⟩ := hF t (etaleGerm B S hS t F.obj V e y)
  obtain ⟨W, j, q, hq, hzero⟩ := (etaleGerm_eq_zero_iff B S hS t F.obj V e (n • y)).1
    ((etaleGerm_nsmul_of_hasColimit B S hS t F.obj V e n y).trans hz)
  refine ⟨W, j, ⟨n, hn, ?_⟩, q.1.base default, ?_⟩
  · rwa [← _root_.map_nsmul]
  · have h1 : q.1 ≫ (SmallEtale.toScheme B S hS).map j = e.1 := congrArg Subtype.val hq
    have h2 : ((SmallEtale.toScheme B S hS).map j).base (q.1.base default) =
        e.1.base default :=
      congrArg (fun m : t.source ⟶ _ ↦ m.base (default : ↥t.source)) h1
    exact h2.trans (geometricPointOfEtalePointLift_base B S hS V x)

/-- **The stalk criterion for local annihilation by a prescribed set of integers.** An abelian
étale sheaf is locally annihilated by `N` exactly when every one of its stalks at a geometric
point is annihilated by a member of `N`. -/
public theorem isLocallyAnnihilatedBy_iff_forall_etaleStalk (N : Set ℕ)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}) :
    IsLocallyAnnihilatedBy (SmallEtale.topology B S hS) N F.obj ↔
      ∀ (t : GeometricPoint S) (g : ↑(etaleStalk B S hS t F.obj)), ∃ n ∈ N, n • g = 0 :=
  ⟨fun hF t g ↦ exists_mem_nsmul_eq_zero_etaleStalk.{u, v} B S hS N t F hF g,
    isLocallyAnnihilatedBy_of_forall_etaleStalk.{u, v} B S hS N F⟩

end Generic

section PrimePower

variable (l : ℕ) (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v})

/-- **The stalk of an `l`-power torsion abelian étale sheaf is annihilated by a positive power of
`l`.** This is `AlgebraicGeometry.SmallEtale.exists_mem_nsmul_eq_zero_etaleStalk` at the positive
powers of `l`. -/
public theorem exists_pow_nsmul_eq_zero_etaleStalk (t : GeometricPoint S)
    (hF : IsPrimePowerTorsion (SmallEtale.topology B S hS) l F)
    (g : ↑(etaleStalk B S hS t F.obj)) :
    ∃ r : ℕ, 0 < r ∧ l ^ r • g = 0 := by
  obtain ⟨n, ⟨r, hr, rfl⟩, hz⟩ := exists_mem_nsmul_eq_zero_etaleStalk.{u, v} B S hS
    (primePowerAnnihilators l) t F
    ((isPrimePowerTorsion_iff_isLocallyAnnihilatedBy l F).1 hF) g
  exact ⟨r, hr, hz⟩

/-- **An abelian étale sheaf whose stalks at all geometric points are annihilated by positive
powers of `l` is `l`-power torsion.** This is
`AlgebraicGeometry.SmallEtale.isLocallyAnnihilatedBy_of_forall_etaleStalk` at the positive powers
of `l`. -/
public theorem isPrimePowerTorsion_of_forall_etaleStalk
    (hF : ∀ (t : GeometricPoint S) (g : ↑(etaleStalk B S hS t F.obj)),
      ∃ r : ℕ, 0 < r ∧ l ^ r • g = 0) :
    IsPrimePowerTorsion (SmallEtale.topology B S hS) l F :=
  (isPrimePowerTorsion_iff_isLocallyAnnihilatedBy l F).2
    (isLocallyAnnihilatedBy_of_forall_etaleStalk.{u, v} B S hS (primePowerAnnihilators l) F
      fun t g ↦ by
        obtain ⟨r, hr, hz⟩ := hF t g
        exact ⟨l ^ r, pow_mem_primePowerAnnihilators hr, hz⟩)

/-- **The stalk criterion for `l`-power torsion.** An abelian étale sheaf is `l`-power torsion
exactly when every one of its stalks at a geometric point is annihilated by a positive power of
`l`. -/
public theorem isPrimePowerTorsion_iff_forall_etaleStalk :
    IsPrimePowerTorsion (SmallEtale.topology B S hS) l F ↔
      ∀ (t : GeometricPoint S) (g : ↑(etaleStalk B S hS t F.obj)),
        ∃ r : ℕ, 0 < r ∧ l ^ r • g = 0 :=
  ⟨fun hF t g ↦ exists_pow_nsmul_eq_zero_etaleStalk.{u, v} B S hS l F t hF g,
    isPrimePowerTorsion_of_forall_etaleStalk.{u, v} B S hS l F⟩

end PrimePower

section PrimeToCharacteristic

variable (p : ℕ) (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v})

/-- **The stalk of an abelian étale sheaf of torsion prime to `p` is annihilated by a positive
integer coprime to `p`.** This is
`AlgebraicGeometry.SmallEtale.exists_mem_nsmul_eq_zero_etaleStalk` at the positive integers
coprime to `p`. -/
public theorem exists_coprime_nsmul_eq_zero_etaleStalk (t : GeometricPoint S)
    (hF : IsPrimeToCharacteristicTorsion (SmallEtale.topology B S hS) p F)
    (g : ↑(etaleStalk B S hS t F.obj)) :
    ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ n • g = 0 := by
  obtain ⟨n, ⟨hn, hcop⟩, hz⟩ := exists_mem_nsmul_eq_zero_etaleStalk.{u, v} B S hS
    (coprimeAnnihilators p) t F
    ((isPrimeToCharacteristicTorsion_iff_isLocallyAnnihilatedBy p F).1 hF) g
  exact ⟨n, hn, hcop, hz⟩

/-- **An abelian étale sheaf whose stalks at all geometric points are annihilated by positive
integers coprime to `p` is of torsion prime to `p`.** This is
`AlgebraicGeometry.SmallEtale.isLocallyAnnihilatedBy_of_forall_etaleStalk` at the positive
integers coprime to `p`. -/
public theorem isPrimeToCharacteristicTorsion_of_forall_etaleStalk
    (hF : ∀ (t : GeometricPoint S) (g : ↑(etaleStalk B S hS t F.obj)),
      ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ n • g = 0) :
    IsPrimeToCharacteristicTorsion (SmallEtale.topology B S hS) p F :=
  (isPrimeToCharacteristicTorsion_iff_isLocallyAnnihilatedBy p F).2
    (isLocallyAnnihilatedBy_of_forall_etaleStalk.{u, v} B S hS (coprimeAnnihilators p) F
      fun t g ↦ by
        obtain ⟨n, hn, hcop, hz⟩ := hF t g
        exact ⟨n, ⟨hn, hcop⟩, hz⟩)

/-- **The stalk criterion for torsion prime to `p`.** An abelian étale sheaf is of torsion prime
to `p` exactly when every one of its stalks at a geometric point is annihilated by a positive
integer coprime to `p`. -/
public theorem isPrimeToCharacteristicTorsion_iff_forall_etaleStalk :
    IsPrimeToCharacteristicTorsion (SmallEtale.topology B S hS) p F ↔
      ∀ (t : GeometricPoint S) (g : ↑(etaleStalk B S hS t F.obj)),
        ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ n • g = 0 :=
  ⟨fun hF t g ↦ exists_coprime_nsmul_eq_zero_etaleStalk.{u, v} B S hS p F t hF g,
    isPrimeToCharacteristicTorsion_of_forall_etaleStalk.{u, v} B S hS p F⟩

end PrimeToCharacteristic

end AlgebraicGeometry.SmallEtale

end
