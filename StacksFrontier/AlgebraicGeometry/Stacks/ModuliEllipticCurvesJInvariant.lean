module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesFibreProduct

/-!
# The `j`-invariant of an elliptic curve is a function on its base

Let `E` be an elliptic curve over a scheme `S`. Zariski locally on `S` it is the restriction of
the Weierstrass family along a morphism `b : U ⟶ W`, and the `j`-invariant `c₄³/Δ` of the
Weierstrass equation classified by `b` is a function on `U`. Two Weierstrass equations of the same
curve differ by a coordinate change, which leaves the `j`-invariant unchanged, so these local
functions glue to a global function `j_E` on `S`: for every triple `(b, a', α)` comparing the
Weierstrass family with `E` over a scheme `T`, the `j`-invariant of the equation classified by
`b` is the pullback of `j_E` along `a' : T ⟶ S`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.j_curveAt_comp`: the `j`-invariant of the
  classified equation is compatible with base change.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.j_curveAt_fst_eq_snd`: two Weierstrass
  equations of isomorphic curves have the same `j`-invariant.
* `AlgebraicGeometry.ModuliEllipticCurves.Comparison.j_curveAt_fst_eq`: two presentations of the
  same elliptic curve by the Weierstrass family have the same `j`-invariant.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.exists_jInvariant`: **the `j`-invariant
  of an elliptic curve is a global function on its base.**
* `AlgebraicGeometry.Scheme.exists_ι_appTop_eq_of_compatible`: functions on the members of an
  open cover of a scheme which agree on the pairwise intersections glue.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.pullbackFamilyIsoOfEq`: equal morphisms to
  the base pull a pointed family back to isomorphic pointed families.

## Implementation notes

The `j`-invariant of a Weierstrass equation is Mathlib's `WeierstrassCurve.j`, defined for an
equation with invertible discriminant; the equation `curveAt b` classified by `b : T ⟶ W` has
invertible discriminant. Its invariance under coordinate changes is
`WeierstrassCurve.variableChange_j`, and it reaches the comparison of two presentations through
the fibre product `W ×_{𝓜₁,₁} W = H × W`
(`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.representsComparisons_coordinateChange`):
a triple comparing two pulled-back Weierstrass families over `T` is a `T`-point of `H × W`, whose
two morphisms to `W` are the action and the projection.

## References

* [Stacks Project, Tag 072M](https://stacks.math.columbia.edu/tag/072M)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-! ### Gluing functions on an open cover -/

/-- Restricting a function along `V ≤ U`, read on the open subschemes, as a commutative square
of ring homomorphisms. The intermediate objects `Γ(U, ⊤)` and `Γ(S, U.ι ''ᵁ ⊤)` are
definitionally but not syntactically equal, so the identity is proved as a term. -/
theorem Scheme.homOfLE_appTop_comp_topIso_hom {S : Scheme.{u}} {V U : S.Opens} (h : V ≤ U) :
    (S.homOfLE h).appTop ≫ V.topIso.hom = U.topIso.hom ≫ S.presheaf.map (homOfLE h).op := by
  rw [Scheme.homOfLE_appTop]
  exact (S.presheaf.map_comp _ _).symm.trans
    ((congrArg S.presheaf.map (Subsingleton.elim _ _)).trans (S.presheaf.map_comp _ _))

/-- The pullback of a function along the inclusion of an open subscheme is its restriction. -/
theorem Scheme.ι_appTop_comp_topIso_hom {S : Scheme.{u}} (U : S.Opens) :
    U.ι.appTop ≫ U.topIso.hom = S.presheaf.map (homOfLE le_top).op :=
  (S.presheaf.map_comp (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op
      (eqToIso U.ι_image_top.symm).op.hom).symm.trans
    (congrArg S.presheaf.map (Subsingleton.elim _ _))

/-- **Gluing functions.** Functions on the members of an open cover of a scheme which agree on the
pairwise intersections are the restrictions of a global function. -/
theorem Scheme.exists_ι_appTop_eq_of_compatible {S : Scheme.{u}} {ι : Type u} (U : ι → S.Opens)
    (hU : ⨆ i, U i = ⊤) (s : ∀ i, Γ((U i).toScheme, ⊤))
    (h : ∀ i j, (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).appTop (s i) =
      (S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).appTop (s j)) :
    ∃ J : Γ(S, ⊤), ∀ i, (U i).ι.appTop J = s i := by
  obtain ⟨J, hJ, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.sheaf U ⊤ (fun i ↦ homOfLE le_top)
    hU.ge (fun i ↦ (U i).topIso.hom (s i)) (fun i j ↦ by
      have hi := congr($(Scheme.homOfLE_appTop_comp_topIso_hom
        (inf_le_left : U i ⊓ U j ≤ U i)) (s i))
      have hj := congr($(Scheme.homOfLE_appTop_comp_topIso_hom
        (inf_le_right : U i ⊓ U j ≤ U j)) (s j))
      change S.presheaf.map (homOfLE inf_le_left).op ((U i).topIso.hom (s i)) =
        S.presheaf.map (homOfLE inf_le_right).op ((U j).topIso.hom (s j))
      exact hi.symm.trans ((congrArg (U i ⊓ U j).topIso.hom (h i j)).trans hj))
  refine ⟨J, fun i ↦ ?_⟩
  have e := congr($(Scheme.ι_appTop_comp_topIso_hom (U i)) J)
  have e' : (U i).topIso.hom ((U i).ι.appTop J) = (U i).topIso.hom (s i) := e.trans (hJ i)
  exact (U i).topIso.commRingCatIsoToRingEquiv.injective e'

/-- Two global functions which agree after restriction to the members of an open cover are
equal. -/
theorem Scheme.eq_of_ι_appTop_eq {S : Scheme.{u}} {ι : Type*} (U : ι → S.Opens)
    (hU : ⨆ i, U i = ⊤) {a b : Γ(S, ⊤)} (h : ∀ i, (U i).ι.appTop a = (U i).ι.appTop b) :
    a = b := by
  refine TopCat.Sheaf.eq_of_locally_eq' S.sheaf U ⊤ (fun i ↦ homOfLE le_top) hU.ge a b
    fun i ↦ ?_
  have ea := congr($(Scheme.ι_appTop_comp_topIso_hom (U i)) a)
  have eb := congr($(Scheme.ι_appTop_comp_topIso_hom (U i)) b)
  exact ea.symm.trans ((congrArg (U i).topIso.hom (h i)).trans eb)

namespace ModuliEllipticCurves

namespace Weierstrass

/-- The `j`-invariant of the classified equation is compatible with base change. -/
theorem j_curveAt_comp {T T' : Scheme.{u}} (h : T' ⟶ T) (b : T ⟶ base.{u}) :
    (curveAt (h ≫ b)).j = h.appTop (curveAt b).j := by
  rw [← WeierstrassCurve.map_j]
  congr 1

/-- A coordinate change does not change the `j`-invariant: the universal case, on `H × W`. -/
theorem j_curveAt_actionMap : (curveAt actionMap.{u}).j = (curveAt productToBase.{u}).j := by
  have h : curveAt actionMap.{u} = changeAt productToGroup.{u} • curveAt productToBase.{u} :=
    curveAt_actionMap
  rw [← WeierstrassCurve.variableChange_j (curveAt productToBase.{u}) (changeAt productToGroup)]
  congr 1

/-- **Isomorphic Weierstrass curves have the same `j`-invariant.** For a triple comparing the
Weierstrass family with itself along `b, b' : T ⟶ W`, the equations classified by `b` and `b'`
have the same `j`-invariant. -/
theorem j_curveAt_fst_eq_snd {T : Scheme.{u}} (z : Comparison family.{u} family.{u} T) :
    (curveAt z.fst).j = (curveAt z.snd).j := by
  obtain ⟨g, rfl⟩ := (representsComparisons_coordinateChange.{u}.homEquiv T).surjective z
  rw [RepresentsComparisons.fst_homEquiv, RepresentsComparisons.snd_homEquiv,
    representsComparisons_coordinateChange_homEquiv_id_fst,
    representsComparisons_coordinateChange_homEquiv_id_snd, j_curveAt_comp, j_curveAt_comp,
    j_curveAt_actionMap]

end Weierstrass

/-- Equal morphisms to the base pull a pointed family back to isomorphic pointed families. -/
def PointedFamily.pullbackFamilyIsoOfEq {S T : Scheme.{u}} (E : PointedFamily S) {a b : T ⟶ S}
    (h : a = b) : FamilyIso (E.pullback a) (E.pullback b) :=
  ⟨E.pullbackIsoOfEq h, E.pullbackIsoOfEq_hom_map h, E.zero_pullbackIsoOfEq_hom h⟩

/-- **Two presentations of an elliptic curve have the same `j`-invariant.** If two triples compare
the Weierstrass family with `E` over `T` along the same morphism to the base of `E`, the
Weierstrass equations they classify have the same `j`-invariant. -/
theorem Comparison.j_curveAt_fst_eq {S T : Scheme.{u}} {E : PointedFamily S}
    (x y : Comparison Weierstrass.family.{u} E T) (h : x.snd = y.snd) :
    (Weierstrass.curveAt x.fst).j = (Weierstrass.curveAt y.fst).j :=
  Weierstrass.j_curveAt_fst_eq_snd (Comparison.ofFamilyIso x.fst y.fst
    ((x.familyIso.trans (E.pullbackFamilyIsoOfEq h)).trans y.familyIso.symm))

/-- **The `j`-invariant of an elliptic curve is a function on its base.** For an elliptic curve
`E` over `S` there is a function `j_E` on `S` such that for every triple `(b, a', α)` comparing the
Weierstrass family with `E` over a scheme `T`, the `j`-invariant of the Weierstrass equation
classified by `b : T ⟶ W` is the pullback of `j_E` along `a' : T ⟶ S`. -/
theorem PointedFamily.exists_jInvariant {S : Scheme.{u}} (E : PointedFamily S)
    (hE : E.IsElliptic) :
    ∃ J : Γ(S, ⊤), ∀ {T : Scheme.{u}} (y : Comparison Weierstrass.family.{u} E T),
      (Weierstrass.curveAt y.fst).j = y.snd.appTop J := by
  choose U hU x hx using
    Weierstrass.localWeierstrassAt_of_noetherian Weierstrass.localWeierstrassNoetherian E hE
  have hcov : ⨆ s, U s = ⊤ :=
    eq_top_iff.2 fun s _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨s, hU s⟩
  obtain ⟨J, hJ⟩ := Scheme.exists_ι_appTop_eq_of_compatible U hcov
    (fun s ↦ (Weierstrass.curveAt (x s).fst).j) (fun s t ↦ by
      rw [← Weierstrass.j_curveAt_comp, ← Weierstrass.j_curveAt_comp]
      refine Comparison.j_curveAt_fst_eq ((x s).baseChange (S.homOfLE inf_le_left))
        ((x t).baseChange (S.homOfLE inf_le_right)) ?_
      change S.homOfLE _ ≫ (x s).snd = S.homOfLE _ ≫ (x t).snd
      rw [hx s, hx t, Scheme.homOfLE_ι, Scheme.homOfLE_ι])
  refine ⟨J, fun {T} y ↦ ?_⟩
  let V (s : S) : T.Opens := y.snd ⁻¹ᵁ U s
  have hV : ⨆ s, V s = ⊤ :=
    eq_top_iff.2 fun t _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y.snd t, hU (y.snd t)⟩
  refine Scheme.eq_of_ι_appTop_eq V hV fun s ↦ ?_
  have hr := morphismRestrict_ι y.snd (U s)
  have key := Comparison.j_curveAt_fst_eq (y.baseChange (V s).ι)
    ((x s).baseChange (y.snd ∣_ U s)) (by
      change (V s).ι ≫ y.snd = (y.snd ∣_ U s) ≫ (x s).snd
      rw [hx s, hr])
  change (V s).ι.appTop (Weierstrass.curveAt y.fst).j = (V s).ι.appTop (y.snd.appTop J)
  rw [← Weierstrass.j_curveAt_comp]
  rw [key]
  change (Weierstrass.curveAt ((y.snd ∣_ U s) ≫ (x s).fst)).j = _
  rw [Weierstrass.j_curveAt_comp, ← hJ s]
  change ((y.snd ∣_ U s) ≫ (U s).ι).appTop J = ((V s).ι ≫ y.snd).appTop J
  rw [hr]

end ModuliEllipticCurves

end AlgebraicGeometry
