module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage

/-!
# Local annihilation by a prescribed set of integers

`Stacks.Torsion.torsionSheafProperty` and its two refinements
`Stacks.Torsion.IsPrimePowerTorsion` and `Stacks.Torsion.IsPrimeToCharacteristicTorsion` are the
same statement about an abelian presheaf, differing only in which positive integers are allowed
to annihilate a local section: any one, a positive power of `l`, or one coprime to `p`. This
module factors that common shape out as `Stacks.Torsion.IsLocallyAnnihilatedBy`, a condition
parameterised by the set `N ⊆ ℕ` of admissible annihilators, and identifies each of the three
predicates with an instance of it.

Every argument that moves one of the three conditions from one site, presheaf or stalk to
another moves the set `N` unchanged, so it is this parameterised condition that such arguments
should be proved for; the three named predicates then follow by rewriting. The two refinements
had no stalk criterion and no transfer between the two spellings of the small étale site for
exactly this reason: the arguments in the library are written for `torsionSheafProperty` alone.

## Main definitions

* `Stacks.Torsion.IsLocallyAnnihilatedBy` — every local section of an abelian presheaf is, on
  some covering sieve, annihilated by a member of `N`.
* `Stacks.Torsion.annihilatorSieve` — the largest sieve on which a section is annihilated by a
  member of `N`.
* `Stacks.Torsion.primePowerAnnihilators`, `Stacks.Torsion.coprimeAnnihilators` and
  `Stacks.Torsion.positiveAnnihilators` — the three sets of admissible annihilators.

## Main results

* `Stacks.Torsion.isPrimePowerTorsion_iff_isLocallyAnnihilatedBy`,
  `Stacks.Torsion.isPrimeToCharacteristicTorsion_iff_isLocallyAnnihilatedBy` and
  `Stacks.Torsion.torsionSheafProperty_iff_isLocallyAnnihilatedBy` — the three predicates are
  instances of the parameterised one.
* `Stacks.Torsion.isLocallyAnnihilatedBy_iff_annihilatorSieve_mem` — the condition says that the
  annihilator sieve of every section is covering.
* `Stacks.Torsion.IsLocallyAnnihilatedBy.of_iso`, `Stacks.Torsion.IsPrimePowerTorsion.of_iso` and
  `Stacks.Torsion.IsPrimeToCharacteristicTorsion.of_iso` — all three conditions are invariant
  under isomorphism.
* `Stacks.Torsion.exists_mem_nsmul_eq_zero_of_retraction` — annihilation by a member of `N`
  passes from an abelian group to a retract of it, which is how a condition on the stalk of a
  finite direct image is read off on the summands of its decomposition over the fibre.

## References

* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
* [Stacks Project, Tag 0DV7](https://stacks.math.columbia.edu/tag/0DV7)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace Stacks.Torsion

section Annihilators

/-- The admissible annihilators for `l`-power torsion: the positive powers of `l`. -/
public def primePowerAnnihilators (l : ℕ) : Set ℕ := {n | ∃ r : ℕ, 0 < r ∧ n = l ^ r}

/-- The admissible annihilators for torsion prime to `p`: the positive integers coprime to
`p`. -/
public def coprimeAnnihilators (p : ℕ) : Set ℕ := {n | 0 < n ∧ Nat.Coprime n p}

/-- The admissible annihilators for plain torsion: the positive integers. -/
public def positiveAnnihilators : Set ℕ := {n | 0 < n}

/-- A positive power of `l` is a member of `primePowerAnnihilators l`. -/
public theorem pow_mem_primePowerAnnihilators {l r : ℕ} (hr : 0 < r) :
    l ^ r ∈ primePowerAnnihilators l :=
  ⟨r, hr, rfl⟩

/-- **Annihilation by a member of `N` passes to a retract.** If every element of `A'` is
annihilated by a member of `N` and `A` is a retract of `A'`, then so is every element of `A`: the
image of `n • x` is `n` times the image of `x`, hence zero, and the retraction takes it back to
`n • x`.

This is the step by which a torsion condition on the stalk of a finite direct image, which
decomposes as a direct sum over the fibre by Tag 03QP part (1), is read off on each summand: a
coproduct injection into a finite biproduct is split. -/
public theorem exists_mem_nsmul_eq_zero_of_retraction {N : Set ℕ} {A A' : AddCommGrpCat.{w}}
    (i : A ⟶ A') (r : A' ⟶ A) (hir : i ≫ r = 𝟙 A)
    (h : ∀ y : A', ∃ n ∈ N, n • y = 0) (x : A) :
    ∃ n ∈ N, n • x = 0 := by
  obtain ⟨n, hn, hz⟩ := h (i x)
  refine ⟨n, hn, ?_⟩
  have hret : r (i (n • x)) = n • x := by
    rw [← CategoryTheory.comp_apply, hir]
    rfl
  rw [← hret, _root_.map_nsmul, hz, map_zero]

end Annihilators

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The sieve of those arrows `g : V ⟶ U` along which the restriction of a section `y` of an
abelian presheaf is annihilated by a member of `N`. It is a sieve because an integer that
annihilates a restriction annihilates every further restriction of it. -/
public def annihilatorSieve (N : Set ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {U : C}
    (y : P.obj (op U)) : Sieve U where
  arrows V g := ∃ n ∈ N, n • P.map g.op y = 0
  downward_closed := by
    rintro V W g ⟨n, hn, hg⟩ h
    refine ⟨n, hn, ?_⟩
    rw [op_comp, P.map_comp, CategoryTheory.comp_apply, ← _root_.map_nsmul, hg, map_zero]

/-- An abelian presheaf on a site is **locally annihilated by `N`** when every section over
every object is, on some covering sieve, annihilated by a member of `N` — the member being
allowed to vary over the arrows of the sieve.

At `N = Stacks.Torsion.positiveAnnihilators` this is `Stacks.Torsion.IsLocallyTorsion`, and at
the other two sets of admissible annihilators it is the two refinements of torsion of Tags 0DV7
and 0A5C. -/
public def IsLocallyAnnihilatedBy (N : Set ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (x : P.obj (op U)), ∃ R : Sieve U, R ∈ J U ∧
    ∀ (V : C) (f : V ⟶ U), R f → ∃ n ∈ N, n • P.map f.op x = 0

/-- Being locally annihilated by `N` says that the annihilator sieve of every section is a
covering sieve: the annihilator sieve is the largest sieve on which the section is pointwise
annihilated by a member of `N`. -/
public theorem isLocallyAnnihilatedBy_iff_annihilatorSieve_mem (N : Set ℕ)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    IsLocallyAnnihilatedBy J N P ↔
      ∀ (U : C) (y : P.obj (op U)), annihilatorSieve N P y ∈ J U := by
  refine ⟨fun h U y => ?_, fun h U y => ⟨_, h U y, fun _ _ hg => hg⟩⟩
  obtain ⟨R, hR, hkill⟩ := h U y
  exact J.superset_covering (fun V g hg => hkill V g hg) hR

/-- Local annihilation by `N` is invariant under an isomorphism of abelian presheaves. -/
public theorem IsLocallyAnnihilatedBy.of_iso {N : Set ℕ} {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (e : P ≅ Q) (hP : IsLocallyAnnihilatedBy J N P) : IsLocallyAnnihilatedBy J N Q := by
  intro U x
  obtain ⟨R, hR, hkill⟩ := hP U (e.inv.app (op U) x)
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨n, hn, hz⟩ := hkill V f hf
  refine ⟨n, hn, ?_⟩
  have hnat : P.map f.op (e.inv.app (op U) x) = e.inv.app (op V) (Q.map f.op x) := by
    rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, e.inv.naturality f.op]
  have h1 : e.inv.app (op V) (n • Q.map f.op x) = 0 := by
    rwa [_root_.map_nsmul, ← hnat]
  have h2 : e.hom.app (op V) (e.inv.app (op V) (n • Q.map f.op x)) =
      n • Q.map f.op x := by
    rw [← CategoryTheory.comp_apply, e.inv_hom_id_app]
    rfl
  rw [← h2, h1, map_zero]

section Refinements

variable {J}

/-- Weakening the pointwise condition on a covering sieve keeps the sieve covering. -/
private theorem exists_covering_sieve_imp {U : C} {p q : ∀ V : C, (V ⟶ U) → Prop}
    (h : ∀ V f, p V f → q V f) (hp : ∃ R : Sieve U, R ∈ J U ∧ ∀ V f, R f → p V f) :
    ∃ R : Sieve U, R ∈ J U ∧ ∀ V f, R f → q V f :=
  hp.imp fun _ => And.imp_right fun hk V f hf => h V f (hk V f hf)

/-- `l`-power torsion is local annihilation by the positive powers of `l`. -/
public theorem isPrimePowerTorsion_iff_isLocallyAnnihilatedBy (l : ℕ)
    (F : Sheaf J AddCommGrpCat.{w}) :
    IsPrimePowerTorsion J l F ↔
      IsLocallyAnnihilatedBy J (primePowerAnnihilators l) F.obj :=
  ⟨fun h U x => exists_covering_sieve_imp (fun _ _ ⟨r, hr, hz⟩ =>
    ⟨l ^ r, pow_mem_primePowerAnnihilators hr, hz⟩) (h U x),
  fun h U x => exists_covering_sieve_imp (fun _ _ ⟨_, ⟨r, hr, hn⟩, hz⟩ =>
    ⟨r, hr, hn ▸ hz⟩) (h U x)⟩

/-- Torsion prime to `p` is local annihilation by the positive integers coprime to `p`. -/
public theorem isPrimeToCharacteristicTorsion_iff_isLocallyAnnihilatedBy (p : ℕ)
    (F : Sheaf J AddCommGrpCat.{w}) :
    IsPrimeToCharacteristicTorsion J p F ↔
      IsLocallyAnnihilatedBy J (coprimeAnnihilators p) F.obj :=
  ⟨fun h U x => exists_covering_sieve_imp (fun _ _ ⟨n, hn, hcop, hz⟩ =>
    ⟨n, ⟨hn, hcop⟩, hz⟩) (h U x),
  fun h U x => exists_covering_sieve_imp (fun _ _ ⟨n, ⟨hn, hcop⟩, hz⟩ =>
    ⟨n, hn, hcop, hz⟩) (h U x)⟩

/-- Torsion is local annihilation by the positive integers. -/
public theorem torsionSheafProperty_iff_isLocallyAnnihilatedBy (F : Sheaf J AddCommGrpCat.{w}) :
    torsionSheafProperty J F ↔ IsLocallyAnnihilatedBy J positiveAnnihilators F.obj :=
  Iff.rfl

/-- `l`-power torsion is invariant under an isomorphism of abelian sheaves. -/
public theorem IsPrimePowerTorsion.of_iso {l : ℕ} {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G)
    (hF : IsPrimePowerTorsion J l F) : IsPrimePowerTorsion J l G :=
  (isPrimePowerTorsion_iff_isLocallyAnnihilatedBy l G).2
    (IsLocallyAnnihilatedBy.of_iso J ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso e)
      ((isPrimePowerTorsion_iff_isLocallyAnnihilatedBy l F).1 hF))

/-- Torsion prime to `p` is invariant under an isomorphism of abelian sheaves. -/
public theorem IsPrimeToCharacteristicTorsion.of_iso {p : ℕ} {F G : Sheaf J AddCommGrpCat.{w}}
    (e : F ≅ G) (hF : IsPrimeToCharacteristicTorsion J p F) :
    IsPrimeToCharacteristicTorsion J p G :=
  (isPrimeToCharacteristicTorsion_iff_isLocallyAnnihilatedBy p G).2
    (IsLocallyAnnihilatedBy.of_iso J ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso e)
      ((isPrimeToCharacteristicTorsion_iff_isLocallyAnnihilatedBy p F).1 hF))

end Refinements

end Stacks.Torsion

end
