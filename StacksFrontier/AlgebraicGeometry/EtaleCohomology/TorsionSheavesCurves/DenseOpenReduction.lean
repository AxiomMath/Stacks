module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ExtensionByZeroRestrictionConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AlgClosedCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClosedPartFiniteSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FinitePointsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionDegreeZero
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering

/-!
# The eight statements of Situation 0A52 across a dense open: the closed part and both transfers

Let `k` be a separably closed field, `X` a quasi-compact scheme locally of finite type over `k`
of Krull dimension at most one, `j : X' ⟶ X` the inclusion of a dense open subscheme and `F` an
abelian sheaf on the small étale site of `X`. Stacks Tag 0GJA compares "statements (1) -- (8)
hold" (`Stacks.EtaleCohomology.CurveStatements`) for `F` and for `j_! j^{-1} F` through the short
exact sequence `0 → j_! j^{-1} F → F → i_* i^{-1} F → 0` of Tag 095L, `i` the inclusion of the
closed complement. This file supplies every ingredient of that comparison and both transfers.

The closed complement `Z = X ∖ X'` is a finite set of closed points
(`Stacks.EtaleCohomology.finite_closedComplement`), so the cohomology of `i_* i^{-1} F` vanishes in
positive degrees — over `X`, over every open `U ⊆ X` and over every scalar extension `X_{k'}`
(`FinitePointsCohomology.lean`) — is finite in degree zero when `F` is constructible
(`ClosedPartFiniteSections.lean`), and is unchanged in degree zero by extension of the separably
closed ground field (`ScalarExtensionDegreeZero.lean`, Tag 0A3I). The sheaf `j_! j^{-1} F` is
constructible when `F` is (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/ExtensionByZeroRestrictionConstructible.lean`, remark (b) of the
source).

## Main results

* `Stacks.EtaleCohomology.curveStatements_of_curveStatements_extensionByZero_of_dense` — if the
  eight statements hold for `j_! j^{-1} F` they hold for `F`. No hypothesis on `F` is needed.
* `Stacks.EtaleCohomology.curveStatements_extensionByZero_of_curveStatements_of_dense` — if the
  eight statements hold for a constructible `F` whose torsion is primary to, or prime to, the
  characteristic, they hold for `j_! j^{-1} F`.
* `Stacks.EtaleCohomology.curveStatements_iff_extensionByZero_of_dense` — the two together.

## Implementation notes

**Why the forward direction carries the torsion dichotomy.** For `F` whose torsion mixes the
characteristic `p > 0` with primes different from `p`, the implication from the statements for `F`
to those for `j_! j^{-1} F` is not a consequence of the long exact sequence: if
`F = Z/p ⊕ i_*(Z/ℓ)` on `X = P¹` with `Z = {0}`, then `j_! j^{-1} F = j_!(Z/p)` is `p`-power
torsion, so statement (3) for it asks `H²(P¹, Z/p) = 0`, while among the statements for `F` only
(1), (5), (7) and (8) apply (`F` is neither `p`-power torsion nor prime to `p`) and none of them
gives that vanishing. The source's remark (a) covers exactly the other direction. The source's
statement remains true — Theorem 03SC makes both sides hold — but its forward half in the mixed
case is an instance of Theorem 03SC, not of the sequence. The dichotomy is satisfied by every sheaf
to which the section applies Tag 0GJA (an `F_ℓ`-sheaf in Theorem 03SC, an `ℓ`-torsion sheaf in
Lemma 0A3Q).

**Constructibility in the forward direction** is asked with respect to every ambient big étale
site, matching the quantification of statements (4) and (5) in
`Stacks.EtaleCohomology.CurveStatements`.

## References

* [Stacks Project, Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

section ClosedComplement

variable {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]

/-- The ideal sheaf of the reduced closed subscheme supported on the complement of the image of
an open immersion `j`. -/
noncomputable def closedComplementIdeal : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩

/-- The reduced closed subscheme on the complement of the image of an open immersion `j`. -/
noncomputable abbrev closedComplement : Scheme.{u} := (closedComplementIdeal j).subscheme

/-- The inclusion of the reduced closed complement of an open immersion `j`. -/
noncomputable abbrev closedComplementι : closedComplement j ⟶ X :=
  (closedComplementIdeal j).subschemeι

/-- The image of `j` is the complement of the image of its closed complement. -/
theorem range_eq_compl_range_closedComplementι :
    Set.range j.base = (Set.range (closedComplementι j).base)ᶜ := by
  show _ = (Set.range (closedComplementIdeal j).subschemeι)ᶜ
  rw [Scheme.IdealSheafData.range_subschemeι, closedComplementIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  simp

/-- **The complement of a dense open in a curve is a finite set of points.** For `X`
quasi-compact, locally of finite type over a field and of Krull dimension at most one, every point
outside a dense open is closed, and a closed set of closed points of a Noetherian scheme is
finite. -/
theorem finite_closedComplement {k : Type u} [Field k] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] [QuasiCompact π] (hdim : topologicalKrullDim X ≤ 1)
    (hd : Dense (Set.range j.base)) : Finite (closedComplement j) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have : IsNoetherian X := { toIsLocallyNoetherian := inferInstance }
  have hT : (Set.range (closedComplementι j).base).Finite := by
    rw [← compl_compl (Set.range _), ← range_eq_compl_range_closedComplementι j]
    refine finite_of_isClosed_of_forall_isClosed_singleton
      j.isOpenEmbedding.isOpen_range.isClosed_compl fun x hx => ?_
    exact TopologicalSpace.NoetherianSpace.isClosed_singleton_of_not_mem_of_dense hdim
      j.isOpenEmbedding.isOpen_range hd hx
  have := hT.to_subtype
  exact Finite.of_injective (fun z => (⟨_, z, rfl⟩ : Set.range (closedComplementι j).base))
    fun a b h => by
      have h' := Subtype.mk.inj h
      exact (closedComplementι j).isClosedEmbedding.injective h'

/-- A finite closed complement is finite over the base field: the morphism has finite fibres, so
it is locally quasi-finite, and it is quasi-compact. -/
theorem isFinite_closedComplementι_comp {k : Type u} [Field k] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] [QuasiCompact π] [Finite (closedComplement j)] :
    IsFinite (closedComplementι j ≫ π) := by
  have : LocallyQuasiFinite (closedComplementι j ≫ π) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _
  exact IsFinite.of_locallyQuasiFinite _

end ClosedComplement

section ClosedPart

variable {k : Type u} [Field k] [IsSepClosed k] {X X' : Scheme.{u}} (π : X ⟶ Spec (.of k))
  [LocallyOfFiniteType π] [QuasiCompact π] (j : X' ⟶ X) [IsOpenImmersion j]
  [Finite (closedComplement j)]

include π

/-- The direct image of a sheaf on the finite closed complement has no positive-degree étale
cohomology. -/
theorem closedPart_subsingleton
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (G : Sheaf (closedComplement j).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (q : ℕ) (hq : 0 < q) :
    Subsingleton
      (Sheaf.H.{w} ((etaleAbelianDirectImage.{u, v} (closedComplementι j)).obj G) q) := by
  obtain ⟨_, hcl, hsep⟩ := isAffine_and_isClosed_and_isSepClosed_of_finite (closedComplementι j ≫ π)
  exact subsingleton_sheafH_of_isZero_etaleRestriction.{u, v, w} (closedComplementι j) j
    (range_eq_compl_range_closedComplementι j) hcl hsep _
    (isZero_etaleRestriction_etaleAbelianDirectImage _ j
      (range_eq_compl_range_closedComplementι j) G) q hq

/-- The restriction to an open `U ⊆ X` of a direct image from the finite closed complement has no
positive-degree étale cohomology. -/
theorem closedPart_subsingleton_open (U : X.Opens)
    [HasExt.{w} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (G : Sheaf (closedComplement j).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} U.ι).obj
      ((etaleAbelianDirectImage.{u, v} (closedComplementι j)).obj G)) q) := by
  have : Finite ↥(pullback (closedComplementι j) U.ι) :=
    Finite.of_injective (pullback.fst (closedComplementι j) U.ι).base
      (pullback.fst (closedComplementι j) U.ι).isOpenEmbedding.injective
  obtain ⟨_, hcl, hsep⟩ := isAffine_and_isClosed_and_isSepClosed_of_finite
    (pullback.snd (closedComplementι j) U.ι ≫ U.ι ≫ π)
  exact subsingleton_sheafH_inverseImage_etaleAbelianDirectImage.{u, v, w} (closedComplementι j) j
    (range_eq_compl_range_closedComplementι j) U.ι hcl hsep G q hq

/-- The pullback to a scalar extension `X_{k'}` of a direct image from the finite closed
complement has no positive-degree étale cohomology. -/
theorem closedPart_subsingleton_scalarExtension (k' : Type u) [Field k'] [Algebra k k']
    [IsSepClosed k']
    [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (G : Sheaf (closedComplement j).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} (scalarExtensionFst k k' π)).obj
      ((etaleAbelianDirectImage.{u, v} (closedComplementι j)).obj G)) q) := by
  have := isFinite_closedComplementι_comp j π
  let g : Spec (.of k') ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hfin : Finite ↥(pullback (closedComplementι j ≫ π) g) := by
    have h := (pullback.snd (closedComplementι j ≫ π) g).finite_preimage_singleton
      (default : Spec (.of k'))
    have hu : (pullback.snd (closedComplementι j ≫ π) g) ⁻¹' {default} = Set.univ := by
      ext z
      simp [Subsingleton.elim ((pullback.snd (closedComplementι j ≫ π) g) z) default]
    rwa [hu, Set.finite_univ_iff] at h
  have : Finite ↥(pullback (closedComplementι j) (scalarExtensionFst k k' π)) :=
    Finite.of_injective (pullbackRightPullbackFstIso π g (closedComplementι j)).hom.base
      (pullbackRightPullbackFstIso π g (closedComplementι j)).hom.isOpenEmbedding.injective
  obtain ⟨_, hcl, hsep⟩ := isAffine_and_isClosed_and_isSepClosed_of_finite
    (pullback.snd (closedComplementι j) (scalarExtensionFst k k' π) ≫ pullback.snd π g)
  exact subsingleton_sheafH_inverseImage_etaleAbelianDirectImage.{u, v, w} (closedComplementι j) j
    (range_eq_compl_range_closedComplementι j) _ hcl hsep G q hq

end ClosedPart

section Torsion

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}

/-- A sheaf which is both `p`-power torsion and torsion prime to `p` is zero: each section is
killed, locally, by a power of `p` and by an integer prime to `p`, hence by `1`. -/
theorem isZero_of_isPrimePowerTorsion_of_isPrimeToCharacteristicTorsion {p : ℕ}
    {G : Sheaf J AddCommGrpCat.{w}} (h₁ : Stacks.Torsion.IsPrimePowerTorsion J p G)
    (h₂ : Stacks.Torsion.IsPrimeToCharacteristicTorsion J p G) : IsZero G := by
  refine CategoryTheory.Sheaf.isZero_of_forall_isZero_sections G fun U => ?_
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  refine ⟨fun x y => ?_⟩
  suffices hx : ∀ x : G.obj.obj (Opposite.op U), x = 0 by rw [hx x, hx y]
  intro x
  obtain ⟨R₁, hR₁, hk₁⟩ := h₁ U x
  obtain ⟨R₂, hR₂, hk₂⟩ := h₂ U x
  have hsep := ((isSheaf_iff_isSheaf_of_type J _).mp
    ((sheafCompose J (forget AddCommGrpCat.{w})).obj G).property _
      (J.intersection_covering hR₁ hR₂)).isSeparatedFor
  refine hsep.ext (t₁ := x) (t₂ := (0 : G.obj.obj (Opposite.op U))) fun V f hf => ?_
  obtain ⟨r, -, hr⟩ := hk₁ V f hf.1
  obtain ⟨n, -, hn, hn'⟩ := hk₂ V f hf.2
  have hcop : Nat.Coprime n (p ^ r) := Nat.Coprime.pow_right r hn
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, (n : ℤ) * a + (p ^ r : ℕ) * b = 1 := by
    refine ⟨Nat.gcdA n (p ^ r), Nat.gcdB n (p ^ r), ?_⟩
    rw [← Nat.gcd_eq_gcd_ab, hcop]; rfl
  show G.obj.map f.op x = G.obj.map f.op (0 : G.obj.obj (Opposite.op U))
  rw [map_zero]
  set y := G.obj.map f.op x
  calc y = (1 : ℤ) • y := (one_smul _ _).symm
    _ = (a * n + b * (p ^ r : ℕ) : ℤ) • y := by rw [← hab]; ring_nf
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hn', hr,
        smul_zero, smul_zero, add_zero]

end Torsion

section Statements

/-- A map between subsingleton groups is bijective. -/
theorem bijective_addMonoidHom_of_subsingleton {A B : Type*} [AddGroup A] [AddGroup B]
    [Subsingleton A] [Subsingleton B] (f : A →+ B) : Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩

/-- Étale cohomology which vanishes in positive degrees and is finite in degree zero is finite in
every degree. -/
theorem finite_sheafH_of_subsingleton_of_finite_zero {X : Scheme.{u}}
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (hvan : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w} G q)) (h0 : Finite (Sheaf.H.{w} G 0))
    (q : ℕ) : Finite (Sheaf.H.{w} G q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact h0
  · have := hvan q hq
    exact Finite.of_subsingleton

/-- In a short exact sequence of étale abelian sheaves with `p`-power torsion middle term, a
sub-object which is torsion prime to `p` is zero. -/
theorem isZero_X₁_of_isPrimePowerTorsion_X₂ {X : Scheme.{u}} {p : ℕ}
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (ht : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology p S.X₂)
    (hc : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₁) :
    IsZero S.X₁ :=
  isZero_of_isPrimePowerTorsion_of_isPrimeToCharacteristicTorsion
    (isPrimePowerTorsion_of_shortExact _ hS ht).1 hc

/-- In a short exact sequence of étale abelian sheaves whose middle term is torsion prime to `p`,
a `p`-power torsion sub-object is zero. -/
theorem isZero_X₁_of_isPrimeToCharacteristicTorsion_X₂ {X : Scheme.{u}} {p : ℕ}
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact)
    (hc : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₂)
    (ht : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology p S.X₁) : IsZero S.X₁ :=
  isZero_of_isPrimePowerTorsion_of_isPrimeToCharacteristicTorsion ht
    (isPrimeToCharacteristicTorsion_of_shortExact _ hS hc).1

variable {k : Type u} [Field k] [IsSepClosed k] {X X' : Scheme.{u}} (π : X ⟶ Spec (.of k))
  [LocallyOfFiniteType π] [QuasiCompact π] (j : X' ⟶ X) [IsOpenImmersion j]
  [Finite (closedComplement j)]

include π in
/-- Restriction along a scalar extension of separably closed fields is bijective on the étale
cohomology of a direct image from the finite closed complement: in degree zero by Tag 0A3I, in
positive degrees because both sides vanish. -/
theorem closedPart_bijective_scalarExtension (k' : Type u) [Field k'] [Algebra k k']
    [IsSepClosed k']
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (G : Sheaf (closedComplement j).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} (scalarExtensionFst k k' π)
      ((etaleAbelianDirectImage.{u, v} (closedComplementι j)).obj G) q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_zero k k' π _
  · have := closedPart_subsingleton.{u, v, w} π j G q hq
    have := closedPart_subsingleton_scalarExtension.{u, v, w} π j k' G q hq
    exact bijective_addMonoidHom_of_subsingleton _

/-- **The eight statements pass from the sub-object to the middle term** of a short exact
sequence whose quotient has no positive-degree cohomology, has bijective restriction to every
scalar extension and no degree-two cohomology on opens, provided constructibility of the middle
term passes to the sub-object and gives finite degree-zero cohomology of the quotient. -/
theorem curveStatements_X₂_of_shortExact {X : Scheme.{u}} {π : X ⟶ Spec (.of k)}
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (h : CurveStatements.{u, v, w} π S.X₁)
    (hvan : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w} S.X₃ q))
    (hc : ∀ (B : BigEtaleSite.{u}) (hX : B.Contains X)
      [∀ (T T' : B.Scheme) (f : T' ⟶ T),
        ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v}
          (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
          (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
      [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
        HasWeakSheafify
          ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
          AddCommGrpCat.{max (u + 1) v}],
      IsConstructibleEtaleAbelianSheaf.{u, v} B X hX S.X₂ →
        IsConstructibleEtaleAbelianSheaf.{u, v} B X hX S.X₁ ∧ Finite (Sheaf.H.{w} S.X₃ 0))
    (hbij : ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
      [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v})] (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w}
        (scalarExtensionFst k k' π) S.X₃ q))
    (hopen : ∀ (U : X.Opens)
      [HasExt.{w} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})],
      Subsingleton (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} U.ι).obj S.X₃) 2)) :
    CurveStatements.{u, v, w} π S.X₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have := h.vanishing q hq
    have := hvan q (by omega)
    exact subsingleton_sheafCohomology_X₂_of_shortExact hS q
  · intro hX q hq
    have := h.affineVanishing hX q hq
    have := hvan q (by omega)
    exact subsingleton_sheafCohomology_X₂_of_shortExact hS q
  · intro p _ hp ht q hq
    obtain ⟨ht₁, -⟩ := isPrimePowerTorsion_of_shortExact p hS ht
    have := h.primePowerVanishing p hp ht₁ q hq
    have := hvan q (by omega)
    exact subsingleton_sheafCohomology_X₂_of_shortExact hS q
  · intro B hX _ _ hcon ht q
    obtain ⟨hc₁, h0⟩ := hc B hX hcon
    obtain ⟨ht₁, -⟩ := isPrimeToCharacteristicTorsion_of_shortExact (ringExpChar k) hS ht
    have := h.finite_of_isPrimeToCharacteristicTorsion B hX hc₁ ht₁ q
    have := finite_sheafH_of_subsingleton_of_finite_zero hvan h0 q
    exact finite_sheafCohomology_X₂_of_shortExact hS q
  · intro B hX _ _ hpr hcon q
    obtain ⟨hc₁, h0⟩ := hc B hX hcon
    have := h.finite_of_isProper B hX hpr hc₁ q
    have := finite_sheafH_of_subsingleton_of_finite_zero hvan h0 q
    exact finite_sheafCohomology_X₂_of_shortExact hS q
  · intro ht k' _ _ _ _ _ q
    obtain ⟨ht₁, -⟩ := isPrimeToCharacteristicTorsion_of_shortExact (ringExpChar k) hS ht
    exact etaleCohomologyRestrictionMap_bijective_of_shortExact.{u, v, w}
      (scalarExtensionFst k k' π) hS
      (fun n => h.bijective_of_isPrimeToCharacteristicTorsion ht₁ k' n) (hbij k') q
  · intro hpr k' _ _ _ _ _ q
    exact etaleCohomologyRestrictionMap_bijective_of_shortExact.{u, v, w}
      (scalarExtensionFst k k' π) hS
      (fun n => h.bijective_of_isProper hpr k' n) (hbij k') q
  · intro U _
    have := hopen U
    exact surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact.{u, v, w} U.ι hS 2 3 rfl
      (h.vanishing 3 (by omega)) (h.surjective U) (fun _ => ⟨0, Subsingleton.elim _ _⟩)

include π in
/-- **The backward half of Tag 0GJA**, for an open immersion with finite closed complement. -/
theorem curveStatements_of_curveStatements_extensionByZero
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : CurveStatements.{u, v, w} π
      ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F))) :
    CurveStatements.{u, v, w} π F := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have : IsNoetherian X := { toIsLocallyNoetherian := inferInstance }
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, v}
    (closedComplementι j) j (range_eq_compl_range_closedComplementι j) F
  refine curveStatements_X₂_of_shortExact.{u, v, w} hS h
    (closedPart_subsingleton.{u, v, w} π j _) (fun B hX _ _ hc => ⟨?_, ?_⟩)
    (fun k' _ _ _ _ q => closedPart_bijective_scalarExtension.{u, v, w} π j k' _ q)
    (fun U _ => closedPart_subsingleton_open.{u, v, w} π j U _ 2 (by omega))
  · exact isConstructibleEtaleAbelianSheaf_extensionByZero_etaleRestriction B hX j F hc
  · exact finite_H_zero_etaleAbelianDirectImage_inverseImage B hX (closedComplementι j) F hc

/-- **The eight statements pass from the middle term to the sub-object** of a short exact
sequence whose quotient has no positive-degree cohomology, finite degree-zero cohomology,
bijective restriction to every scalar extension and no degree-one cohomology on opens, for a
constructible middle term whose torsion is primary to, or prime to, the characteristic. -/
theorem curveStatements_X₁_of_shortExact {X : Scheme.{u}} {π : X ⟶ Spec (.of k)}
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (h : CurveStatements.{u, v, w} π S.X₂)
    (hpure : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology (ringExpChar k) S.X₂ ∨
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) S.X₂)
    (hvan : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w} S.X₃ q))
    (hc : ∀ (B : BigEtaleSite.{u}) (hX : B.Contains X)
      [∀ (T T' : B.Scheme) (f : T' ⟶ T),
        ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v}
          (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
          (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
      [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
        HasWeakSheafify
          ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
          AddCommGrpCat.{max (u + 1) v}],
      IsConstructibleEtaleAbelianSheaf.{u, v} B X hX S.X₂ ∧ Finite (Sheaf.H.{w} S.X₃ 0))
    (hbij : ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
      [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v})] (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w}
        (scalarExtensionFst k k' π) S.X₃ q))
    (hopen : ∀ (U : X.Opens)
      [HasExt.{w} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})],
      Subsingleton (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} U.ι).obj S.X₃) 1)) :
    CurveStatements.{u, v, w} π S.X₁ := by
  have hsucc' : ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} S.X₂ q) →
      Subsingleton (Sheaf.H.{w} S.X₁ q) := fun q hq _ => by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    have := hvan m (by omega)
    exact subsingleton_sheafCohomology_X₁_of_shortExact hS m (m + 1) rfl
  have hfinX₁ : ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₃ 0) → (∀ q, Finite (Sheaf.H.{w} S.X₂ q)) →
      Finite (Sheaf.H.{w} S.X₁ q) := fun q h0 h₂ => by
    rcases q with _ | m
    · have := h₂ 0
      exact finite_sheafCohomology_X₁_zero_of_shortExact hS
    · have := h₂ (m + 1)
      have := finite_sheafH_of_subsingleton_of_finite_zero hvan h0 m
      exact finite_sheafCohomology_X₁_of_shortExact hS m (m + 1) rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun q hq => hsucc' q (by omega) (h.vanishing q hq)
  · exact fun hX q hq => hsucc' q hq (h.affineVanishing hX q hq)
  · intro p _ hp ht₁ q hq
    have : NeZero p := ⟨hp.ne'⟩
    have : ExpChar k p := ExpChar.prime (CharP.char_is_prime_of_pos k p).out
    have hexp := ringExpChar.eq k p
    rcases hpure with ht | hc'
    · rw [hexp] at ht
      exact hsucc' q hq (h.primePowerVanishing p hp ht q hq)
    · rw [← hexp] at ht₁
      exact Sheaf.subsingleton_H_of_isZero
        (isZero_X₁_of_isPrimeToCharacteristicTorsion_X₂.{u, v} hS hc' ht₁) q
  · intro B hX _ _ _ hc₁ q
    obtain ⟨hcon, h0⟩ := hc B hX
    rcases hpure with ht | hc'
    · exact @Finite.of_subsingleton _ <| Sheaf.subsingleton_H_of_isZero
        (isZero_X₁_of_isPrimePowerTorsion_X₂.{u, v} hS ht hc₁) q
    · exact hfinX₁ q h0 (h.finite_of_isPrimeToCharacteristicTorsion B hX hcon hc')
  · intro B hX _ _ hpr _ q
    obtain ⟨hcon, h0⟩ := hc B hX
    exact hfinX₁ q h0 (h.finite_of_isProper B hX hpr hcon)
  · intro hc₁ k' _ _ _ _ _ q
    rcases hpure with ht | hc'
    · have hz := isZero_X₁_of_isPrimePowerTorsion_X₂.{u, v} hS ht hc₁
      have := Sheaf.subsingleton_H_of_isZero hz q
      have := Sheaf.subsingleton_H_of_isZero
        ((etaleAbelianInverseImage.{u, v} (scalarExtensionFst k k' π)).map_isZero hz) q
      exact bijective_addMonoidHom_of_subsingleton _
    · exact etaleCohomologyRestrictionMap_bijective_of_shortExact_X₁.{u, v, w}
        (scalarExtensionFst k k' π) hS
        (fun n => h.bijective_of_isPrimeToCharacteristicTorsion hc' k' n) (hbij k') q
  · exact fun hpr k' _ _ _ _ _ q =>
      etaleCohomologyRestrictionMap_bijective_of_shortExact_X₁.{u, v, w} (scalarExtensionFst k k' π)
        hS (fun n => h.bijective_of_isProper hpr k' n) (hbij k') q
  · exact fun U _ => surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact.{u, v, w} U.ι hS 2 1
      rfl (hvan 2 (by omega)) (hopen U) (h.surjective U)

include π in
/-- **The forward half of Tag 0GJA** for a constructible sheaf whose torsion is primary to, or
prime to, the characteristic, for an open immersion with finite closed complement. -/
theorem curveStatements_extensionByZero_of_curveStatements
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ (B : BigEtaleSite.{u}) (hX : B.Contains X)
      [∀ (T T' : B.Scheme) (f : T' ⟶ T),
        ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v}
          (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
          (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
      [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
        HasWeakSheafify
          ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
          AddCommGrpCat.{max (u + 1) v}],
      IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F)
    (hpure : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology (ringExpChar k) F ∨
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F)
    (h : CurveStatements.{u, v, w} π F) :
    CurveStatements.{u, v, w} π
      ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) := by
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, v}
    (closedComplementι j) j (range_eq_compl_range_closedComplementι j) F
  exact curveStatements_X₁_of_shortExact.{u, v, w} hS h hpure
    (closedPart_subsingleton.{u, v, w} π j _)
    (fun B hX _ _ => ⟨hF B hX,
      finite_H_zero_etaleAbelianDirectImage_inverseImage B hX (closedComplementι j) F (hF B hX)⟩)
    (fun k' _ _ _ _ q => closedPart_bijective_scalarExtension.{u, v, w} π j k' _ q)
    (fun U _ => closedPart_subsingleton_open.{u, v, w} π j U _ 1 (by omega))

end Statements

section Dense

variable {k : Type u} [Field k] [IsSepClosed k] {X X' : Scheme.{u}} (π : X ⟶ Spec (.of k))
  [LocallyOfFiniteType π] [QuasiCompact π] (hdim : topologicalKrullDim X ≤ 1)
  (j : X' ⟶ X) [IsOpenImmersion j] (hj : Dense (Set.range j.base))
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

include hdim hj

/-- **Stacks Tag 0GJA, the direction from `j_! j^{-1} F` to `F`.** Let `X` be a quasi-compact
scheme locally of finite type over a separably closed field, of Krull dimension at most one, and
let `j : X' ⟶ X` be the inclusion of a dense open. If statements (1) -- (8) of Situation 0A52 hold
for `j_! j^{-1} F`, they hold for `F`. -/
theorem curveStatements_of_curveStatements_extensionByZero_of_dense
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : CurveStatements.{u, v, w} π
      ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F))) :
    CurveStatements.{u, v, w} π F :=
  have := finite_closedComplement j π hdim hj
  curveStatements_of_curveStatements_extensionByZero.{u, v, w} π j F h

/-- **Stacks Tag 0GJA, the direction from `F` to `j_! j^{-1} F`, for a constructible `F` whose
torsion is primary to, or prime to, the characteristic.** See the module docstring for why the
remaining case is an instance of Theorem 03SC and not of the sequence of Tag 095L. -/
theorem curveStatements_extensionByZero_of_curveStatements_of_dense
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ (B : BigEtaleSite.{u}) (hX : B.Contains X)
      [∀ (T T' : B.Scheme) (f : T' ⟶ T),
        ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v}
          (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
          (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
      [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
        HasWeakSheafify
          ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
          AddCommGrpCat.{max (u + 1) v}],
      IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F)
    (hpure : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology (ringExpChar k) F ∨
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F)
    (h : CurveStatements.{u, v, w} π F) :
    CurveStatements.{u, v, w} π
      ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) :=
  have := finite_closedComplement j π hdim hj
  curveStatements_extensionByZero_of_curveStatements.{u, v, w} π j F hF hpure h

/-- **Stacks Tag 0GJA for a constructible sheaf whose torsion is primary to, or prime to, the
characteristic**: statements (1) -- (8) of Situation 0A52 hold for `F` if and only if they hold
for `j_! j^{-1} F`. -/
theorem curveStatements_iff_extensionByZero_of_dense
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ (B : BigEtaleSite.{u}) (hX : B.Contains X)
      [∀ (T T' : B.Scheme) (f : T' ⟶ T),
        ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v}
          (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
          (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
      [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
        HasWeakSheafify
          ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
          AddCommGrpCat.{max (u + 1) v}],
      IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F)
    (hpure : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology (ringExpChar k) F ∨
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F) :
    CurveStatements.{u, v, w} π F ↔ CurveStatements.{u, v, w} π
      ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) :=
  ⟨curveStatements_extensionByZero_of_curveStatements_of_dense.{u, v, w} π hdim j hj F hF hpure,
    curveStatements_of_curveStatements_extensionByZero_of_dense.{u, v, w} π hdim j hj F⟩

end Dense

end Stacks.EtaleCohomology

end
