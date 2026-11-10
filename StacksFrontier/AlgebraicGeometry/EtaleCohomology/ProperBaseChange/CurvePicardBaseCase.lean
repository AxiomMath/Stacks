module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CurveRestrictionBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.RootsOfUnitySecondCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityConstant
public import StacksFrontier.AlgebraicGeometry.Curves.GeometricallyNormalSmooth
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Proper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base case of Stacks 03SC (7) for `ℓ` invertible, from the Picard group of a curve

Let `k ⊆ k'` be algebraically closed, `ℓ` a prime invertible in `k`, and `C` a proper normal
irreducible `k`-scheme of dimension one. Then `C` is a smooth projective curve over `k`, and so is
its scalar extension `C_{k'}` over `k'`, of the same genus `g`. With a primitive `ℓ`-th root of
unity, `ℤ/ℓ ≅ μ_ℓ` on both, and the Kummer sequence gives `H¹(μ_ℓ) ≅ Pic[ℓ]`,
`H²(μ_ℓ) ≅ Pic/ℓ` and `H^q(μ_ℓ) = 0` for `q ≥ 3` (Stacks 03RM). Granted the two facts about the
Picard group of a smooth projective curve over an algebraically closed field which this library
does not have,

* `#Pic(X)[n] = n^{2g}` for `n` invertible, and
* `Pic(X)/n Pic(X) ≅ ℤ/n` for `n` invertible (the degree is onto and `Pic⁰(X)` is `n`-divisible),

both sides of restriction `H^q(C, ℤ/ℓ) ⟶ H^q(C_{k'}, ℤ/ℓ)` have the same finite cardinality for
`q = 1, 2`, the target vanishes for `q ≥ 3`, and degree zero is the degree-zero theorem. So an
injective restriction map is surjective. This is the base case of the dévissage of Stacks 03SC (7)
for `ℓ ≠ char k`, in the form of the hypothesis `hbase` of
`EtaleCohomology.bijective_etaleCohomologyRestrictionMap_of_torsion_of_curve_of_isAlgClosed`.

The two Picard facts are hypotheses `hPic` and `hdiv` of the lemmas below, stated for every smooth
projective curve over every algebraically closed field of the universe; they are the results of
the Jacobian (Stacks 0BQ5, 0BQ6), which are being formalized elsewhere. No declaration of this file
is registered.

## Main results

* `AlgebraicGeometry.smooth_of_isNormal_of_isCurve`: a normal curve over a perfect field is smooth.
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_constant_zmod_of_picard`: the
  base case.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_of_torsion_of_curve_of_picard`,
  `Stacks.EtaleCohomology.properBaseChangeOverAlgClosed_of_picard`: Stacks 03SC (7) from `hPic`,
  `hdiv` and injectivity of restriction over algebraically closed fields (`hinj`).
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_isSepClosed_of_picard`: Stacks
  0A5E from the same inputs, through
  `Stacks.EtaleCohomology.etaleCohomologyBaseChangeMap_bijective_of_isSepClosed_of`.

The injectivity input `hinj` is the consequence of Stacks 03Q6 that a class on `X` vanishing on
`X_{k'}` vanishes on some `X_A`, `A ⊆ k'` a finitely generated `k`-algebra, hence on `X` by a
`k`-point of `A`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry

/-- **A normal curve over a perfect field is smooth.** Its local rings are normal of dimension at
most one, hence regular, and over a perfect field regularity of the local ring is smoothness at the
point (Stacks 0B8X). -/
@[ega "IV 6.7.5" "special case"]
theorem smooth_of_isNormal_of_isCurve (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsNormal X] : Smooth f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have hreg := isRegular_of_isNormal_of_topologicalKrullDim_le_one X
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro x _
  have hx : IsRegularLocalRing (X.presheaf.stalk x) :=
    (((isRegular_tfae X).out 1 2 rfl rfl).mp hreg).2 x
  have hsm : InfinitesimalLifting.SmoothAt f x := by
    have h := smoothAt_locus_eq_regular_locus k f
    rw [Set.ext_iff] at h
    exact (h x).2 hx
  exact InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f x hsm

/-- **A proper normal irreducible scheme of dimension one over a perfect field is a smooth
projective curve.** -/
theorem isCurve_smooth_isProjectiveVariety_of_isNormal (k : Type u) [Field k] [PerfectField k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsNormal X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 1) :
    IsCurve k f ∧ Smooth f ∧ IsProjectiveVariety k f := by
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have : IsCurve k f := { topologicalKrullDim_eq_one := hdim }
  exact ⟨inferInstance, smooth_of_isNormal_of_isCurve k f,
    { isProjective := isProjectiveMorphism_of_isProper_of_isCurve k f }⟩

/-- **The scalar extension of a smooth projective curve over an algebraically closed field is a
smooth projective curve.** It is integral, the curve being geometrically integral; of dimension
one, the dimension being invariant under extension of the ground field; smooth and proper by base
change; and projective, being a proper curve. -/
theorem isCurve_smooth_isProjectiveVariety_scalarExtension (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
    [Smooth f] [IsProper f] :
    IsCurve k' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ∧
      Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ∧
      IsProjectiveVariety k' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := by
  let f' := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  have : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X f
  have : GeometricallyReduced f := geometricallyReduced_of_isReduced f
  have : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have : UniversallyOpen f := universallyOpen_of_flat_of_locallyOfFinitePresentation f
  have : IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
    inferInstance
  have hdim : topologicalKrullDim
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{u}) = 1 := by
    rw [topologicalKrullDim_baseChange k k' (pullback.fst _ _) f' f
      (IsPullback.of_hasPullback _ _)]
    exact IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)
  have : IsCurve k' f' := { topologicalKrullDim_eq_one := hdim }
  exact ⟨inferInstance, inferInstance,
    { isProjective := isProjectiveMorphism_of_isProper_of_isCurve k' f' }⟩

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- An isomorphism of sheaves induces a bijection on cohomology groups. -/
private def sheafHEquivOfIso {X : Scheme.{u}}
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : A ≅ B) (q : ℕ) :
    Sheaf.H.{u + 1} A q ≃ Sheaf.H.{u + 1} B q where
  toFun := Sheaf.H.map e.hom q
  invFun := Sheaf.H.map e.inv q
  left_inv := fun x => by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  right_inv := fun x => by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]

/-- Isomorphic sheaves have cohomology groups of the same cardinality. -/
theorem nat_card_sheafH_eq_of_iso {X : Scheme.{u}}
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : A ≅ B) (q : ℕ) :
    Nat.card (Sheaf.H.{u + 1} A q) = Nat.card (Sheaf.H.{u + 1} B q) :=
  Nat.card_congr (sheafHEquivOfIso e q)

/-- **The cohomology of `ℤ/n` on a smooth projective curve, from the Picard group.** Let `X` be a
smooth projective curve over an algebraically closed field `K`, `n` invertible in `K`. Then
`H^q(X, ℤ/n)` is `μ_n`-cohomology, so `#H¹ = #Pic(X)[n]`, `H² ≅ Pic(X)/n`, and `H^q = 0` for
`q ≥ 3`. -/
theorem nat_card_sheafH_constant_zmod_of_isCurve {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProjectiveVariety K f]
    (n : ℕ) (hn : IsUnit (n : K)) :
    Nat.card (Sheaf.H.{u + 1} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) 1) =
      Nat.card (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (n : ℤ)) ∧
    Nat.card (Sheaf.H.{u + 1} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) 2) =
      Nat.card (Stacks.Picard.ofScheme X ⧸
        (nsmulAddMonoidHom n : Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X).range) ∧
    ∀ q, 3 ≤ q → Subsingleton (Sheaf.H.{u + 1} ((constantSheaf X.smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) q) := by
  classical
  have hn0 : (n : K) ≠ 0 := hn.ne_zero
  obtain ⟨e⟩ := Stacks.Kummer.nonempty_rootsOfUnity_iso_constant f
    (by rintro rfl; simp at hn0) hn0
  refine ⟨?_, ?_, fun q hq => ?_⟩
  · rw [nat_card_sheafH_eq_of_iso e 1]
    exact Nat.card_congr
      (Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion_of_isCurve.{u + 1, 0, u} X n
        (by rintro rfl; simp at hn0) (Stacks.Kummer.isUnit_natCast_globalSections X n f hn) f
        hn).toEquiv
  · rw [nat_card_sheafH_eq_of_iso e 2]
    exact Nat.card_congr
      (Stacks.Kummer.h2RootsOfUnityAddEquivPicardQuotient_of_smoothCurve f hn).toEquiv
  · exact (sheafHEquivOfIso e q).subsingleton_congr.2
      (Stacks.Kummer.subsingleton_sheafH_rootsOfUnitySheaf_of_isCurve f hn q hq)

/-- **The base case of Stacks 03SC (7) for `ℓ` invertible, from the Picard group.** Let
`k ⊆ k'` be algebraically closed, `ℓ` a prime invertible in `k`, and `C` a proper normal
irreducible `k`-scheme of dimension one. Suppose that for every smooth projective curve `X` over
an algebraically closed field `K` and every `n` invertible in `K`

* (`hPic`) `#Pic(X)[n] = n^{2g}`, `g` the genus, and
* (`hdiv`) `Pic(X)/n Pic(X) ≅ ℤ/n`, which is what the `n`-divisibility of `Pic⁰(X)` and the
  surjectivity of the degree give.

Then an injective restriction map `H^q(C, ℤ/ℓ) ⟶ H^q(C_{k'}, ℤ/ℓ)` is surjective. -/
theorem surjective_etaleCohomologyRestrictionMap_constant_zmod_of_picard
    (hPic : ∀ (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
      [IsCurve K f] [Smooth f] [IsProjectiveVariety K f] (n : ℕ), IsUnit (n : K) →
        Nat.card (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (n : ℤ)) =
          n ^ (2 * AlgebraicGeometry.genus f))
    (hdiv : ∀ (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
      [IsCurve K f] [Smooth f] [IsProjectiveVariety K f] (n : ℕ), IsUnit (n : K) →
        Nonempty (Stacks.Picard.ofScheme X ⧸
          (nsmulAddMonoidHom n : Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X).range ≃+
            ZMod n))
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓk : (ℓ : k) ≠ 0) (q : ℕ) {C : Scheme.{u}} (πC : C ⟶ Spec (.of k))
    [IsProper πC] [IsNormal C] [IrreducibleSpace C] (hdim : topologicalKrullDim C = 1)
    (hinj : Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (scalarExtensionFst k k' πC) ((constantSheaf C.smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (scalarExtensionFst k k' πC) ((constantSheaf C.smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q) := by
  obtain ⟨_, _, _⟩ := isCurve_smooth_isProjectiveVariety_of_isNormal k πC hdim
  let f' := pullback.snd πC (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  obtain ⟨_, _, _⟩ := isCurve_smooth_isProjectiveVariety_scalarExtension k k' πC
  have hgenus : AlgebraicGeometry.genus f' = AlgebraicGeometry.genus πC :=
    genus_baseChange k k' (pullback.fst _ _) f' πC (IsPullback.of_hasPullback _ _)
  have hℓu : IsUnit (ℓ : k) := hℓk.isUnit
  have hℓu' : IsUnit (ℓ : k') := by
    have := hℓu.map (algebraMap k k')
    rwa [map_natCast] at this
  let A := (constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))
  let eA := (etaleAbelianInverseImageConstantIso.{u, 0} (scalarExtensionFst k k' πC)).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))
  obtain ⟨h1, h2, h3⟩ := nat_card_sheafH_constant_zmod_of_isCurve πC ℓ hℓu
  obtain ⟨h1', h2', h3'⟩ := nat_card_sheafH_constant_zmod_of_isCurve f' ℓ hℓu'
  have hℓpos : 0 < ℓ := hℓ.pos
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  -- the target of restriction, through the constant sheaf upstairs
  have hcard : ∀ r, Nat.card (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (scalarExtensionFst k k' πC)).obj A) r) = Nat.card (Sheaf.H.{u + 1}
        ((constantSheaf (scalarExtension k k' πC).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) r) := fun r =>
    nat_card_sheafH_eq_of_iso eA r
  -- cardinality argument in degrees one and two
  have hbij : ∀ (N : ℕ), 0 < N →
      Nat.card (Sheaf.H.{u + 1} A q) = N →
      Nat.card (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (scalarExtensionFst k k' πC)).obj A) q) = N →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' πC) A q) := fun N hN hs ht => by
    have : Finite (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (scalarExtensionFst k k' πC)).obj A) q) := Nat.finite_of_card_ne_zero (by omega)
    exact (hinj.bijective_of_nat_card_le (by rw [hs, ht])).2
  rcases q with _ | _ | _ | q
  · exact (etaleCohomologyRestrictionMap_zero_bijective_of_isSepClosed k k' πC A).2
  · refine hbij (ℓ ^ (2 * AlgebraicGeometry.genus πC)) (pow_pos hℓpos _) ?_ ?_
    · rw [h1, hPic k πC ℓ hℓu]
    · rw [hcard, h1', hPic k' f' ℓ hℓu', hgenus]
  · obtain ⟨d⟩ := hdiv k πC ℓ hℓu
    obtain ⟨d'⟩ := hdiv k' f' ℓ hℓu'
    refine hbij ℓ hℓpos ?_ ?_
    · rw [h2, Nat.card_congr d.toEquiv, Nat.card_zmod]
    · rw [hcard, h2', Nat.card_congr d'.toEquiv, Nat.card_zmod]
  · have : Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (scalarExtensionFst k k' πC)).obj A) (q + 3)) := by
      exact (sheafHEquivOfIso eA (q + 3)).subsingleton_congr.2 (h3' (q + 3) (by omega))
    exact fun y => ⟨0, Subsingleton.elim _ _⟩

/-- **Stacks 03SC (7) from injectivity and the Picard group.** Let `k ⊆ k'` be algebraically
closed, `X` proper over `k` of dimension at most one and `F` a torsion abelian sheaf. Granted
injectivity of restriction to the scalar extension for every abelian sheaf on every proper
`k`-scheme of dimension at most one, and the two Picard facts `hPic` and `hdiv` of
`Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_constant_zmod_of_picard`,
restriction `H^q(X, F) ⟶ H^q(X_{k'}, F)` is bijective. -/
theorem bijective_etaleCohomologyRestrictionMap_of_torsion_of_curve_of_picard
    (hPic : ∀ (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
      [IsCurve K f] [Smooth f] [IsProjectiveVariety K f] (n : ℕ), IsUnit (n : K) →
        Nat.card (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (n : ℤ)) =
          n ^ (2 * AlgebraicGeometry.genus f))
    (hdiv : ∀ (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
      [IsCurve K f] [Smooth f] [IsProjectiveVariety K f] (n : ℕ), IsUnit (n : K) →
        Nonempty (Stacks.Picard.ofScheme X ⧸
          (nsmulAddMonoidHom n : Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X).range ≃+
            ZMod n))
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    (hinj : ∀ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (p : ℕ), Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G p))
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsProper π] (hdim : topologicalKrullDim X ≤ 1)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      F q) :=
  bijective_etaleCohomologyRestrictionMap_of_torsion_of_curve_of_isAlgClosed k k' hinj
    (fun ℓ hℓ hℓk r C πC hC hn hirr hCdim =>
      have : IsProper πC := hC
      have : IsNormal C := hn
      have : IrreducibleSpace C := hirr
      surjective_etaleCohomologyRestrictionMap_constant_zmod_of_picard hPic hdiv k k' ℓ hℓ hℓk r
        πC hCdim (hinj C πC hC hCdim.le _ r))
    π hdim F hF q

/-- **Stacks 03SC (7) in the form of `Stacks.EtaleCohomology.ProperBaseChangeOverAlgClosed`, from
injectivity and the Picard group.** -/
theorem properBaseChangeOverAlgClosed_of_picard
    (hPic : ∀ (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
      [IsCurve K f] [Smooth f] [IsProjectiveVariety K f] (n : ℕ), IsUnit (n : K) →
        Nat.card (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (n : ℤ)) =
          n ^ (2 * AlgebraicGeometry.genus f))
    (hdiv : ∀ (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
      [IsCurve K f] [Smooth f] [IsProjectiveVariety K f] (n : ℕ), IsUnit (n : K) →
        Nonempty (Stacks.Picard.ofScheme X ⧸
          (nsmulAddMonoidHom n : Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X).range ≃+
            ZMod n))
    (hinj : ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k]
      [IsAlgClosed k'] (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (p : ℕ), Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G p)) :
    ProperBaseChangeOverAlgClosed.{u, 0} := by
  intro k k' _ _ _ _ _ X f _ hdim F hF q
  exact (etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, 0, u + 1}
    (scalarExtensionFst k k' f) F q).mp
    (bijective_etaleCohomologyRestrictionMap_of_torsion_of_curve_of_picard hPic hdiv k k'
      (hinj k k') f hdim F hF q)

/-- **Stacks 0A5E from injectivity and the Picard group.** For `k ⊆ k'` separably closed, `X`
proper over `k` of dimension at most one and `F` a torsion abelian sheaf, restriction
`H^q(X, F) ⟶ H^q(X_{k'}, F)` is bijective, granted injectivity over algebraically closed fields
and the Picard facts `hPic`, `hdiv`. -/
theorem etaleCohomologyRestrictionMap_bijective_of_isSepClosed_of_picard
    (hPic : ∀ (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
      [IsCurve K f] [Smooth f] [IsProjectiveVariety K f] (n : ℕ), IsUnit (n : K) →
        Nat.card (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (n : ℤ)) =
          n ^ (2 * AlgebraicGeometry.genus f))
    (hdiv : ∀ (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
      [IsCurve K f] [Smooth f] [IsProjectiveVariety K f] (n : ℕ), IsUnit (n : K) →
        Nonempty (Stacks.Picard.ofScheme X ⧸
          (nsmulAddMonoidHom n : Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X).range ≃+
            ZMod n))
    (hinj : ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k]
      [IsAlgClosed k'] (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (p : ℕ), Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G p))
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsSepClosed k] [IsSepClosed k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (smallEtaleTopology (scalarExtension k k' f)) AddCommGrpCat.{u + 1})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1} (smallEtaleTopology X) F) (q : ℕ) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' f) F q) :=
  etaleCohomologyBaseChangeMap_bijective_of_isSepClosed_of.{u, 0, w}
    (properBaseChangeOverAlgClosed_of_picard hPic hdiv hinj) k k' f hdim F hF q

end Stacks.EtaleCohomology

end
