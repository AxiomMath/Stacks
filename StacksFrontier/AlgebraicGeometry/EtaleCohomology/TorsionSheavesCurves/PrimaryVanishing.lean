module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleLocallyBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Extensions of locally annihilated sheaves and the vanishing of their cohomology

Let `J` be a Grothendieck topology on a category `C` and let
`0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of abelian sheaves on `(C, J)`.

Two independent facts are proved. First, the long exact sequence of `Ext`-groups makes the
cohomology of the middle sheaf vanish, resp. be finite, as soon as the cohomology of the two
outer sheaves does. Second, if every local section of the middle sheaf is locally annihilated
by an integer satisfying a predicate `P`, then the same holds for the sub- and the quotient
sheaf; this is the descent of torsion conditions along a short exact sequence.

Combining the two gives the vanishing statement for `p`-power torsion sheaves: the assertion
"`Hq(F) = 0` for `q > 1` whenever `F` is `p`-power torsion" passes from the two outer terms of a
short exact sequence to the middle one. For a scheme over a field of characteristic `p` this is
the characteristic-primary part of the étale-cohomology extension lemma for curves.

## Main definitions

* `Stacks.EtaleCohomology.LocallyAnnihilated` is the property that every local section of an
  abelian sheaf is, locally on a covering sieve, annihilated by an integer satisfying a given
  predicate.

## Main results

* `Stacks.EtaleCohomology.subsingleton_ext_X₂_of_shortExact` and
  `Stacks.EtaleCohomology.finite_ext_X₂_of_shortExact`: vanishing and finiteness of `Ext`-groups
  pass from the outer terms of a short exact sequence to the middle one.
* `Stacks.EtaleCohomology.subsingleton_sheafCohomology_X₂_of_shortExact` and
  `Stacks.EtaleCohomology.finite_sheafCohomology_X₂_of_shortExact`: the same for sheaf
  cohomology.
* `Stacks.EtaleCohomology.locallyAnnihilated_of_shortExact`: local annihilation descends from the
  middle term of a short exact sequence to the sub- and the quotient sheaf, and hence so do
  `Stacks.Torsion.IsPrimePowerTorsion` and `Stacks.Torsion.IsPrimeToCharacteristicTorsion`.
* `Stacks.EtaleCohomology.subsingleton_sheafCohomology_of_shortExact_of_isPrimePowerTorsion`:
  the characteristic-primary vanishing assertion passes to extensions.
* `Stacks.EtaleCohomology.subsingleton_etaleCohomology_of_shortExact_of_isPrimePowerTorsion`:
  the same statement on the small étale site of a scheme, with coefficients in
  `AddCommGrpCat.{u}`, and
  `Stacks.EtaleCohomology.subsingleton_etaleCohomology_of_shortExact_of_isPrimePowerTorsion'`:
  with coefficients in `AddCommGrpCat.{max (u + 1) v}`, the universe in which étale cohomology
  of a scheme `X : Scheme.{u}` is computed.

## Implementation notes

Vanishing of a cohomology group is spelled `Subsingleton`, matching Mathlib's `Sheaf.H`, which is
an `Ext`-group from the constant sheaf `ℤ` and therefore has no canonical zero element to compare
against.

The vanishing assertions are hypotheses of the form "if `F₁` is `p`-power torsion then its
cohomology vanishes above degree one", rather than bare vanishing statements. This is what the
extension lemma actually asserts: a numbered assertion about an arbitrary sheaf is assumed for
the two outer terms and deduced for the middle one, so the torsion side condition has to travel
with it. The degree bound plays no role in the argument and is not built into the statements;
the general middle-term lemma is applied degree by degree.

`LocallyAnnihilated` generalises `Stacks.Torsion.torsionSheafProperty` by the predicate cutting
out the admissible annihilators; `locallyAnnihilated_pos_iff_torsionSheafProperty` records that
the predicate `0 < ·` recovers it.

## References

* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 0A55](https://stacks.math.columbia.edu/tag/0A55)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w' w v u

namespace Stacks.EtaleCohomology

section Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (hS : S.ShortExact) (X : C) (q : ℕ)

include hS

/-- If `Extq(X, -)` vanishes on the two outer terms of a short exact sequence, it vanishes on
the middle term. -/
theorem subsingleton_ext_X₂_of_shortExact
    [Subsingleton (Ext.{w} X S.X₁ q)] [Subsingleton (Ext.{w} X S.X₃ q)] :
    Subsingleton (Ext.{w} X S.X₂ q) := by
  refine ⟨fun x y => ?_⟩
  rw [← sub_eq_zero]
  have hright : (x - y).comp (Ext.mk₀ S.g) (add_zero q) = 0 := Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₂ X hS (x - y) hright
  rw [Subsingleton.elim a 0] at ha
  simpa using ha.symm

/-- If `Extq(X, -)` is finite on the two outer terms of a short exact sequence, it is finite on
the middle term. -/
theorem finite_ext_X₂_of_shortExact
    [Finite (Ext.{w} X S.X₁ q)] [Finite (Ext.{w} X S.X₃ q)] :
    Finite (Ext.{w} X S.X₂ q) :=
  (Ext.covariant_sequence_exact₂' X hS q).ab_finite

end Ext

section Cohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) (q : ℕ)

include hS

/-- If the degree-`q` sheaf cohomology of the two outer terms of a short exact sequence of
abelian sheaves vanishes, so does that of the middle term. -/
theorem subsingleton_sheafCohomology_X₂_of_shortExact
    [Subsingleton (Sheaf.H.{w', w} S.X₁ q)] [Subsingleton (Sheaf.H.{w', w} S.X₃ q)] :
    Subsingleton (Sheaf.H.{w', w} S.X₂ q) :=
  subsingleton_ext_X₂_of_shortExact hS _ q

/-- If the degree-`q` sheaf cohomology of the two outer terms of a short exact sequence of
abelian sheaves is finite, so is that of the middle term. -/
theorem finite_sheafCohomology_X₂_of_shortExact
    [Finite (Sheaf.H.{w', w} S.X₁ q)] [Finite (Sheaf.H.{w', w} S.X₃ q)] :
    Finite (Sheaf.H.{w', w} S.X₂ q) :=
  finite_ext_X₂_of_shortExact hS _ q

end Cohomology

section LocallyAnnihilated

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- An abelian sheaf is locally annihilated along `P` if every local section becomes, after
restriction along the arrows of some covering sieve, annihilated by an integer satisfying `P`.
The integer is allowed to depend on the arrow. -/
def LocallyAnnihilated (P : ℕ → Prop) (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (x : F.obj.obj (op U)), ∃ R : Sieve U, R ∈ J U ∧
    ∀ (V : C) (f : V ⟶ U), R f → ∃ n : ℕ, P n ∧ n • F.obj.map f.op x = 0

variable {J}

variable [HasSheafify J AddCommGrpCat.{w}]

omit [HasSheafify J AddCommGrpCat.{w}] in
/-- The predicate `0 < ·` recovers the torsion sheaves of `Stacks.Torsion`. -/
theorem locallyAnnihilated_pos_iff_torsionSheafProperty (F : Sheaf J AddCommGrpCat.{w}) :
    LocallyAnnihilated J (0 < ·) F ↔ Stacks.Torsion.torsionSheafProperty J F :=
  Iff.rfl

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}

/-- Local annihilation descends from the middle term of a short exact sequence of abelian
sheaves to the sub-sheaf. -/
theorem locallyAnnihilated_X₁_of_shortExact (P : ℕ → Prop) (hS : S.ShortExact)
    (h₂ : LocallyAnnihilated J P S.X₂) : LocallyAnnihilated J P S.X₁ := by
  intro U x
  obtain ⟨R, hR, hkill⟩ := h₂ U (S.f.hom.app (op U) x)
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨n, hn, hzero⟩ := hkill V f hf
  refine ⟨n, hn, ?_⟩
  have hmap : S.f.hom.app (op V) (n • S.X₁.obj.map f.op x) = 0 := by
    rw [map_nsmul, NatTrans.naturality_apply]
    simp [hzero]
  have hmono : Mono (S.f.hom.app (op V)) := by
    have : Mono S.f := hS.mono_f
    exact (NatTrans.mono_iff_mono_app S.f.hom).mp
      ((sheafToPresheaf J AddCommGrpCat).map_mono S.f) _
  exact (AddCommGrpCat.mono_iff_injective _).1 hmono (by simpa using hmap)

/-- Local annihilation descends from the middle term of a short exact sequence of abelian
sheaves to the quotient sheaf. -/
theorem locallyAnnihilated_X₃_of_shortExact (P : ℕ → Prop) (hS : S.ShortExact)
    (h₂ : LocallyAnnihilated J P S.X₂) : LocallyAnnihilated J P S.X₃ := by
  intro U y
  let _ : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' (J := J) AddCommGrpCat S.g).2 hS.epi_g
  set φ := S.g.hom
  let T : ∀ ⦃V : C⦄ (f : V ⟶ U), Presheaf.imageSieve φ y f → Sieve V :=
    fun V f hf => (h₂ V (Presheaf.localPreimage φ y f hf)).choose
  refine ⟨Sieve.bind (Presheaf.imageSieve φ y).1 T, ?_, ?_⟩
  · refine J.transitive (Presheaf.imageSieve_mem J φ y) _ fun V f hf => ?_
    refine J.superset_covering (Sieve.le_pullback_bind _ T _ hf) ?_
    exact (h₂ V (Presheaf.localPreimage φ y f hf)).choose_spec.1
  · rintro W g ⟨V, g', f, hf, hR, rfl⟩
    set x := Presheaf.localPreimage φ y f hf
    obtain ⟨n, hn, hnzero⟩ := (h₂ V x).choose_spec.2 W g' hR
    refine ⟨n, hn, ?_⟩
    have hmap : φ.app (op W) (n • S.X₂.obj.map g'.op x) = 0 := by
      simpa using congrArg (φ.app (op W)) hnzero
    have hdesc : φ.app (op W) (n • S.X₂.obj.map g'.op x) =
        n • S.X₃.obj.map (g' ≫ f).op y := by
      calc φ.app (op W) (n • S.X₂.obj.map g'.op x)
          = n • φ.app (op W) (S.X₂.obj.map g'.op x) := by rw [map_nsmul]
        _ = n • S.X₃.obj.map g'.op (φ.app (op V) x) := by rw [NatTrans.naturality_apply]
        _ = n • S.X₃.obj.map g'.op (S.X₃.obj.map f.op y) := by
          rw [Presheaf.app_localPreimage φ y f hf]
        _ = n • S.X₃.obj.map (g' ≫ f).op y := by simp [op_comp, Functor.map_comp]
    rwa [hdesc] at hmap

/-- Local annihilation descends from the middle term of a short exact sequence of abelian
sheaves to the sub- and the quotient sheaf. -/
theorem locallyAnnihilated_of_shortExact (P : ℕ → Prop) (hS : S.ShortExact)
    (h₂ : LocallyAnnihilated J P S.X₂) :
    LocallyAnnihilated J P S.X₁ ∧ LocallyAnnihilated J P S.X₃ :=
  ⟨locallyAnnihilated_X₁_of_shortExact P hS h₂, locallyAnnihilated_X₃_of_shortExact P hS h₂⟩

/-- Local annihilation along `P` descends to the sub- and the quotient sheaf for any property of
sheaves equivalent to it. -/
private theorem and_of_shortExact_of_iff (Q : Sheaf J AddCommGrpCat.{w} → Prop) (P : ℕ → Prop)
    (hQ : ∀ G, Q G ↔ LocallyAnnihilated J P G) (hS : S.ShortExact) (h₂ : Q S.X₂) :
    Q S.X₁ ∧ Q S.X₃ :=
  (locallyAnnihilated_of_shortExact P hS ((hQ _).1 h₂)).imp (hQ _).2 (hQ _).2

/-- Being `l`-power torsion descends from the middle term of a short exact sequence of abelian
sheaves to the sub- and the quotient sheaf. -/
theorem isPrimePowerTorsion_of_shortExact (l : ℕ) (hS : S.ShortExact)
    (h₂ : Stacks.Torsion.IsPrimePowerTorsion J l S.X₂) :
    Stacks.Torsion.IsPrimePowerTorsion J l S.X₁ ∧
      Stacks.Torsion.IsPrimePowerTorsion J l S.X₃ := by
  have hpow : ∀ G : Sheaf J AddCommGrpCat.{w},
      Stacks.Torsion.IsPrimePowerTorsion J l G ↔
        LocallyAnnihilated J (fun n => ∃ r : ℕ, 0 < r ∧ n = l ^ r) G := fun G =>
    forall₂_congr fun U x => exists_congr fun R => and_congr_right fun _ =>
      forall₃_congr fun V f _ =>
        ⟨fun ⟨r, hr, hn⟩ => ⟨l ^ r, ⟨r, hr, rfl⟩, hn⟩,
          fun ⟨_, ⟨r, hr, rfl⟩, hn⟩ => ⟨r, hr, hn⟩⟩
  exact and_of_shortExact_of_iff _ _ hpow hS h₂

/-- Being torsion prime to `p` descends from the middle term of a short exact sequence of
abelian sheaves to the sub- and the quotient sheaf. -/
theorem isPrimeToCharacteristicTorsion_of_shortExact (p : ℕ) (hS : S.ShortExact)
    (h₂ : Stacks.Torsion.IsPrimeToCharacteristicTorsion J p S.X₂) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion J p S.X₁ ∧
      Stacks.Torsion.IsPrimeToCharacteristicTorsion J p S.X₃ := by
  have hcop : ∀ G : Sheaf J AddCommGrpCat.{w},
      Stacks.Torsion.IsPrimeToCharacteristicTorsion J p G ↔
        LocallyAnnihilated J (fun n => 0 < n ∧ n.Coprime p) G := fun G =>
    forall₂_congr fun U x => exists_congr fun R => and_congr_right fun _ =>
      forall₃_congr fun V f _ => exists_congr fun _ => and_assoc.symm
  exact and_of_shortExact_of_iff _ _ hcop hS h₂

/-- Torsion descends from the middle term of a short exact sequence of abelian sheaves to the
sub- and the quotient sheaf. -/
theorem torsionSheafProperty_of_shortExact (hS : S.ShortExact)
    (h₂ : Stacks.Torsion.torsionSheafProperty J S.X₂) :
    Stacks.Torsion.torsionSheafProperty J S.X₁ ∧
      Stacks.Torsion.torsionSheafProperty J S.X₃ :=
  locallyAnnihilated_of_shortExact (0 < ·) hS h₂

end LocallyAnnihilated

section PrimaryVanishing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}

/-- The characteristic-primary vanishing assertion passes to extensions: if the degree-`q`
cohomology of an `l`-power torsion sheaf vanishes for the sub- and the quotient sheaf of a short
exact sequence, then it vanishes for an `l`-power torsion middle sheaf as well. -/
theorem subsingleton_sheafCohomology_of_shortExact_of_isPrimePowerTorsion
    (l q : ℕ) (hS : S.ShortExact)
    (hleft : Stacks.Torsion.IsPrimePowerTorsion J l S.X₁ → Subsingleton (Sheaf.H.{w', w} S.X₁ q))
    (hright : Stacks.Torsion.IsPrimePowerTorsion J l S.X₃ → Subsingleton (Sheaf.H.{w', w} S.X₃ q))
    (h₂ : Stacks.Torsion.IsPrimePowerTorsion J l S.X₂) :
    Subsingleton (Sheaf.H.{w', w} S.X₂ q) := by
  obtain ⟨h₁, h₃⟩ := isPrimePowerTorsion_of_shortExact l hS h₂
  have := hleft h₁
  have := hright h₃
  exact subsingleton_sheafCohomology_X₂_of_shortExact hS q

/-- The characteristic-primary vanishing assertion, in the degree range above one in which it
is stated for curves, passes to extensions. -/
theorem subsingleton_sheafCohomology_of_shortExact_of_isPrimePowerTorsion_one_lt
    (l : ℕ) (hS : S.ShortExact)
    (hleft : Stacks.Torsion.IsPrimePowerTorsion J l S.X₁ →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w', w} S.X₁ q))
    (hright : Stacks.Torsion.IsPrimePowerTorsion J l S.X₃ →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w', w} S.X₃ q))
    (h₂ : Stacks.Torsion.IsPrimePowerTorsion J l S.X₂) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H.{w', w} S.X₂ q) :=
  subsingleton_sheafCohomology_of_shortExact_of_isPrimePowerTorsion l q hS
    (fun h => hleft h q hq) (fun h => hright h q hq) h₂

end PrimaryVanishing

section SmallEtaleSite

variable {X : Scheme.{u}}
  [HasExt.{w'} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})}

/-- On the small étale site of a scheme, the characteristic-primary vanishing assertion for
`l`-power torsion sheaves in degrees above one passes to extensions. -/
theorem subsingleton_etaleCohomology_of_shortExact_of_isPrimePowerTorsion
    (l : ℕ) (hS : S.ShortExact)
    (hleft : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₁ →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w', u} S.X₁ q))
    (hright : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₃ →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w', u} S.X₃ q))
    (h₂ : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₂) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H.{w', u} S.X₂ q) :=
  subsingleton_sheafCohomology_of_shortExact_of_isPrimePowerTorsion_one_lt l hS
    hleft hright h₂ q hq

end SmallEtaleSite

section SmallEtaleSiteLargeCoefficients

variable {X : Scheme.{u}}
  [HasExt.{w'} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}

/-- On the small étale site of a scheme, the characteristic-primary vanishing assertion for
`l`-power torsion sheaves in degrees above one passes to extensions, for coefficients in
`AddCommGrpCat.{max (u + 1) v}`.

This is `subsingleton_etaleCohomology_of_shortExact_of_isPrimePowerTorsion` at the coefficient
universe in which étale cohomology of `X : Scheme.{u}` is actually computed: a sheaf of abelian
groups on `X.Etale`, a category with objects in `Type (u + 1)`, has sections large enough to
contain its own matching families, so the coefficients cannot be taken in `AddCommGrpCat.{u}`.
The two coefficient-universe side conditions of the site-generic statement are discharged by
`AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology` and
`AlgebraicGeometry.Scheme.wEqualsLocallyBijective_smallEtaleTopology`. Both are supplied by name
rather than by instance search: Mathlib's instance at `AddCommGrpCat.{u}` is tried first and the
universe unifier gets stuck on `u =?= max (u + 1) v` instead of rejecting it. -/
theorem subsingleton_etaleCohomology_of_shortExact_of_isPrimePowerTorsion'
    (l : ℕ) (hS : S.ShortExact)
    (hleft : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₁ →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w', max (u + 1) v} S.X₁ q))
    (hright : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₃ →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w', max (u + 1) v} S.X₃ q))
    (h₂ : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₂) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H.{w', max (u + 1) v} S.X₂ q) :=
  let : HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
    Scheme.hasSheafify_smallEtaleTopology X
  let : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v} :=
    Scheme.wEqualsLocallyBijective_smallEtaleTopology X
  subsingleton_sheafCohomology_of_shortExact_of_isPrimePowerTorsion_one_lt l hS
    hleft hright h₂ q hq

end SmallEtaleSiteLargeCoefficients

end Stacks.EtaleCohomology
