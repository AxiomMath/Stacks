module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.Decomposition

/-!
# Splitting off the isolated points of a fibre after an étale base change

A separated morphism locally of finite type whose fibre over a point of the base has only finitely
many isolated points becomes, after passing to an elementary étale neighbourhood of that point, the
disjoint union of a piece finite over the neighbourhood and a piece whose fibre over the
distinguished point has no isolated point at all. If the whole fibre is finite, the second piece
has no point over the distinguished point whatsoever.

## Main results

* `AlgebraicGeometry.exists_elementaryEtale_isCompl_not_quasiFiniteAt_of_finite_isolatedPoints`:
  the elementary étale neighbourhood and the two complementary open-and-closed pieces exist, the
  first finite over the neighbourhood and the second with no isolated point in its fibre over the
  distinguished point.
* `AlgebraicGeometry.exists_elementaryEtale_isCompl_isEmpty_fiber_of_finite_fiber`: for a finite
  fibre the second piece has no point over the distinguished point.
* `AlgebraicGeometry.exists_etale_isCompl_isEmpty_fiber_of_finite_fiber`: the same conclusion with
  the residue field clause of the neighbourhood dropped.

## Implementation notes

Isolated points of a fibre are spelled through quasi-finiteness: a point `x` of `X` lying over `s`
is isolated in the fibre `X_s` exactly when `f` is quasi-finite at `x`, which is
`AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`. Since the second piece
`W` is open in the base change, a point of its fibre over the distinguished point is isolated there
exactly when the base change is quasi-finite at the corresponding point, so the conclusion "the
fibre of `W` over `u` contains no isolated points" is stated as the negation of quasi-finiteness of
the second projection at the points of `W` over `u`.

The two pieces come from `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_decomposition`
applied to the family of isolated points of the fibre: the finite piece is the supremum of the open
ranges of the pieces attached to those points, and the other piece is the open range of the
complementary piece. Finiteness of the supremum is reduced to the binary case by induction over a
`Finset`, and the binary case to finiteness of a coproduct descent map, two disjoint open
subschemes covering a scheme exhibiting it as their coproduct.

That the remaining piece has no isolated point over the distinguished point uses that the fibre of
the base change over the distinguished point of an elementary neighbourhood is isomorphic to the
original fibre, so an isolated point of the former gives an isolated point of the latter, which the
decomposition has excluded from that piece.

## References

* [Stacks Project, Tag 02LP](https://stacks.math.columbia.edu/tag/02LP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism out of the empty open subscheme is finite. -/
private lemma isFinite_bot_ι_comp {Y U : Scheme.{u}} (h : Y ⟶ U) :
    IsFinite ((⊥ : Y.Opens).ι ≫ h) := by
  have : IsEmpty ((⊥ : Y.Opens) : Type u) := ⟨fun z => absurd z.2 (by simp)⟩
  infer_instance

/-- If two open immersions into `Y` have complementary open ranges and both become finite after
composing with `h : Y ⟶ U`, then `h` is finite. -/
private lemma isFinite_of_isCompl_opensRange {A B Y U : Scheme.{u}} (a : A ⟶ Y) (b : B ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (hab : IsCompl a.opensRange b.opensRange) (h : Y ⟶ U)
    (ha : IsFinite (a ≫ h)) (hb : IsFinite (b ≫ h)) : IsFinite h := by
  obtain ⟨H⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl a b hab
  let i : Y ≅ A ⨿ B := H.coconePointUniqueUpToIso (colimit.isColimit (pair A B))
  have ha' : a ≫ i.hom = coprod.inl := H.comp_coconePointUniqueUpToIso_hom _ ⟨.left⟩
  have hb' : b ≫ i.hom = coprod.inr := H.comp_coconePointUniqueUpToIso_hom _ ⟨.right⟩
  have key : i.inv ≫ h = coprod.desc (a ≫ h) (b ≫ h) := by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc, ← ha', Category.assoc, Iso.hom_inv_id_assoc]
    · rw [coprod.inr_desc, ← hb', Category.assoc, Iso.hom_inv_id_assoc]
  have hinv : IsFinite (i.inv ≫ h) := by
    rw [key]
    infer_instance
  rw [← Iso.hom_inv_id_assoc i h]
  infer_instance

/-- The union of two disjoint open subschemes finite over `U` is finite over `U`. -/
private lemma isFinite_sup_ι_comp {Y U : Scheme.{u}} (h : Y ⟶ U) {A B : Y.Opens}
    (hAB : Disjoint A B) (hA : IsFinite (A.ι ≫ h)) (hB : IsFinite (B.ι ≫ h)) :
    IsFinite ((A ⊔ B).ι ≫ h) := by
  have hA' : A ≤ A ⊔ B := le_sup_left
  have hB' : B ≤ A ⊔ B := le_sup_right
  have hcompl : IsCompl (Y.homOfLE hA').opensRange (Y.homOfLE hB').opensRange := by
    rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE]
    constructor
    · rw [disjoint_iff, ← Scheme.Hom.preimage_inf, hAB.eq_bot]
      simp
    · rw [codisjoint_iff, ← Scheme.Hom.preimage_sup, Scheme.Opens.ι_preimage_self]
  refine isFinite_of_isCompl_opensRange (Y.homOfLE hA') (Y.homOfLE hB') hcompl
    ((A ⊔ B).ι ≫ h) ?_ ?_
  · rwa [← Category.assoc, Y.homOfLE_ι]
  · rwa [← Category.assoc, Y.homOfLE_ι]

/-- The union of a finite family of pairwise disjoint open subschemes finite over `U` is finite
over `U`. -/
private lemma isFinite_biSup_ι_comp {ι : Type*} {Y U : Scheme.{u}} (h : Y ⟶ U) (A : ι → Y.Opens)
    (hd : Pairwise fun i₁ i₂ => Disjoint (A i₁) (A i₂))
    (hA : ∀ i, IsFinite ((A i).ι ≫ h)) (t : Finset ι) :
    IsFinite ((⨆ i ∈ t, A i).ι ≫ h) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      rw [show (⨆ i ∈ (∅ : Finset ι), A i) = (⊥ : Y.Opens) by simp]
      exact isFinite_bot_ι_comp h
  | insert a t ha ih =>
      rw [Finset.iSup_insert]
      refine isFinite_sup_ι_comp h ?_ (hA a) ih
      simp only [disjoint_iSup_iff]
      exact fun i hi => hd fun hia => ha (hia ▸ hi)

/-- A decomposition of `Y` into open-and-closed pieces indexed by `Option (Fin n)`, all but the
piece indexed by `none` finite over `T`, gives two complementary open subschemes of `Y`: the union
of the finite pieces, which is finite over `T`, and the remaining piece. -/
private lemma exists_isCompl_isFinite_of_isIso_sigmaDesc {n : ℕ} {Y T : Scheme.{u}} (h : Y ⟶ T)
    (P : Option (Fin n) → Scheme.{u}) (j : ∀ a, P a ⟶ Y)
    (hjopen : ∀ a, IsOpenImmersion (j a)) (hjdesc : IsIso (Sigma.desc j))
    (hjfin : ∀ i, IsFinite (j (some i) ≫ h)) :
    ∃ V W : Y.Opens, IsCompl V W ∧ IsFinite (V.ι ≫ h) ∧
      ∀ w : W, ∃ z : P none, (j none).base z = W.ι.base w := by
  classical
  -- every point of the coproduct lies in the range of one of its inclusions
  have hsigma : ∀ w : (∐ P : Scheme.{u}), ∃ (a : Option (Fin n)) (z : P a),
      (Sigma.ι P a).base z = w := by
    intro w
    obtain ⟨a, z, hz⟩ := (sigmaOpenCover P).exists_eq w
    exact ⟨a, z, hz⟩
  -- every point of `Y` lies in the range of one of the pieces
  have hsurj : ∀ y : Y, ∃ (a : Option (Fin n)) (z : P a), (j a).base z = y := by
    intro y
    obtain ⟨w, hw⟩ := (Sigma.desc j).surjective y
    obtain ⟨a, z, hz⟩ := hsigma w
    refine ⟨a, z, ?_⟩
    rw [← hw, ← hz, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
  -- the ranges of two distinct pieces are disjoint
  have hdisjrange : ∀ a b, a ≠ b → ∀ (z : P a) (w : P b), (j a).base z ≠ (j b).base w := by
    intro a b hab z w e
    have e' : (Sigma.desc j).base ((Sigma.ι P a).base z) =
        (Sigma.desc j).base ((Sigma.ι P b).base w) := by
      rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_desc, Sigma.ι_desc]
    obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp ((Sigma.desc j).homeomorph.injective e')
    exact hab rfl
  refine ⟨⨆ i : Fin n, (j (some i)).opensRange, (j none).opensRange, ?_, ?_, fun w => w.2⟩
  · constructor
    · rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left]
      rintro y hyV ⟨w, hw⟩
      simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at hyV
      obtain ⟨i, z, hz⟩ := hyV
      exact hdisjrange (some i) none (by simp) z w (hz.trans hw.symm)
    · rw [codisjoint_iff, eq_top_iff]
      intro y _
      obtain ⟨a, z, hz⟩ := hsurj y
      cases a with
      | none => exact Or.inr ⟨z, hz⟩
      | some i =>
          refine Or.inl ?_
          simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion]
          exact ⟨i, z, hz⟩
  · have heq : (⨆ i ∈ (Finset.univ : Finset (Fin n)), (j (some i)).opensRange) =
        ⨆ i : Fin n, (j (some i)).opensRange := by simp
    rw [← heq]
    refine isFinite_biSup_ι_comp h (fun i => (j (some i)).opensRange) ?_ (fun i => ?_) Finset.univ
    · intro i₁ i₂ hi
      rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left]
      rintro y ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
      exact hdisjrange (some i₁) (some i₂) (by simpa using hi) z₁ z₂ (hz₁.trans hz₂.symm)
    · have : IsFinite (j (some i) ≫ h) := hjfin i
      rw [← Scheme.Hom.isoOpensRange_inv_comp (j (some i)), Category.assoc]
      infer_instance

/-- Transporting the canonical point of a fibre along an equality of base points does not change
its image in the ambient scheme. -/
private lemma fiberι_cast_asFiber {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) {y : Y}
    (h : f.base x = y) : f.fiberι y (h ▸ f.asFiber x) = x := by
  cases h
  exact f.fiberι_asFiber x

/-- Isolation of the canonical point of a fibre does not depend on which of two equal points of
the base the fibre is taken over. -/
private lemma isIsolatedPoint_asFiber_cast {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {y : Y} (hxy : f.base x = y) :
    IsIsolatedPoint (hxy ▸ f.asFiber x) ↔ IsIsolatedPoint (f.asFiber x) := by
  cases hxy
  rfl

/-- A point of the base change of `f` along an étale neighbourhood `(U, u)` of `s` lying over `u`
maps to a point of `X` lying over `s`. -/
private lemma base_fst_eq_of_base_snd_eq {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (U : EtaleNeighborhood S s) (y : (pullback f U.toBase : Scheme.{u}))
    (hy : (pullback.snd f U.toBase).base y = U.point) :
    f.base ((pullback.fst f U.toBase).base y) = s := by
  have hcond := congrArg (fun m : (pullback f U.toBase : Scheme.{u}) ⟶ S => m.base y)
    (pullback.condition (f := f) (g := U.toBase))
  simp only [Scheme.Hom.comp_apply] at hcond
  rw [hcond, hy]
  exact U.map_point

/-- A point of the base change of `f` along an elementary étale neighbourhood `(U, u)` of `s` which
lies over `u` and is isolated in its fibre maps to a point of `X` isolated in the fibre of `f`
over `s`. -/
private lemma isIsolatedPoint_asFiber_of_elementary_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (y : (pullback f U.toBase : Scheme.{u}))
    (hy : (pullback.snd f U.toBase).base y = U.point)
    (hyi : IsIsolatedPoint ((pullback.snd f U.toBase).asFiber y)) :
    IsIsolatedPoint (f.asFiber ((pullback.fst f U.toBase).base y)) := by
  have hxs := base_fst_eq_of_base_snd_eq f U y hy
  let q := pullback.snd f U.toBase
  let e := fiberIsoOfIsElementary f s U hU
  let py : q.fiber U.point := hy ▸ q.asFiber y
  have he : e.hom ≫ f.fiberι s = q.fiberι U.point ≫ pullback.fst f U.toBase := by
    simpa [e, q] using fiberIsoOfIsElementary_hom_fiberι f s U hU
  have hp : e.hom py = hxs ▸ f.asFiber ((pullback.fst f U.toBase).base y) := by
    apply (f.fiberι s).isEmbedding.injective
    calc
      f.fiberι s (e.hom py) = (e.hom ≫ f.fiberι s) py := by simp
      _ = (q.fiberι U.point ≫ pullback.fst f U.toBase) py := by rw [he]
      _ = (pullback.fst f U.toBase).base y := by
        show (pullback.fst f U.toBase).base (q.fiberι U.point py) = _
        rw [show q.fiberι U.point py = y from fiberι_cast_asFiber q y hy]
      _ = f.fiberι s (hxs ▸ f.asFiber ((pullback.fst f U.toBase).base y)) :=
        (fiberι_cast_asFiber f _ hxs).symm
  have hopen : IsOpen ((TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)) '' {py}) :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isOpen_image.mpr
      ((isIsolatedPoint_asFiber_cast q y hy).2 hyi)
  rw [Set.image_singleton] at hopen
  refine (isIsolatedPoint_asFiber_cast f _ hxs).1 ?_
  rw [← hp]
  exact hopen

/-- **Stacks Project, Tag 02LP**, the main assertion. Let `f : X ⟶ S` be separated and locally of
finite type and let `s : S` be such that the fibre `X_s` has only finitely many isolated points,
i.e. only finitely many points of `X` over `s` at which `f` is quasi-finite. Then there is an
elementary étale neighbourhood `(U, u)` of `s` — an étale `g : U ⟶ S` with `g u = s` inducing an
isomorphism of residue fields — and a decomposition of `U ×_S X` into two complementary
open-and-closed pieces `V` and `W` such that `V ⟶ U` is finite and the fibre `W_u` contains no
isolated point, i.e. the second projection is quasi-finite at no point of `W` over `u`. -/
@[stacks 02LP "the main assertion: `V ⟶ U` is finite and `W_u` has no isolated point",
  ega "IV 18.12.1" "separated case", ega "IV 18.12.3"]
theorem exists_elementaryEtale_isCompl_not_quasiFiniteAt_of_finite_isolatedPoints
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f] {s : S}
    (hfin : {x : X | f.base x = s ∧ f.QuasiFiniteAt x}.Finite) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U), Etale g ∧ g.base u = s ∧
        IsIso (g.residueFieldMap u) ∧
      ∃ V W : (pullback f g).Opens, IsCompl V W ∧
        IsFinite (V.ι ≫ pullback.snd f g) ∧
        ∀ w : W, (pullback.snd f g).base (W.ι.base w) = u →
          ¬ (pullback.snd f g).QuasiFiniteAt (W.ι.base w) := by
  classical
  obtain ⟨n, x, hxinj, hxrange⟩ := hfin.fin_param
  have hxmem : ∀ i, x i ∈ {x : X | f.base x = s ∧ f.QuasiFiniteAt x} := by
    intro i
    rw [← hxrange]
    exact Set.mem_range_self i
  have hx : ∀ i, f.base (x i) = s := fun i => (hxmem i).1
  have hxisolated : ∀ i, IsOpen {f.asFiber (x i)} := fun i =>
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (hxmem i).2
  obtain ⟨U, hU, P, j, hjopen, -, hjdesc, v, hjfin, hvx, hvfib, -, hnone⟩ :=
    exists_elementaryEtaleNeighborhood_decomposition f s n x hx hxinj hxisolated
  obtain ⟨V, W, hcompl, hVfin, hW⟩ := exists_isCompl_isFinite_of_isIso_sigmaDesc
    (pullback.snd f U.toBase) P j hjopen hjdesc hjfin
  refine ⟨U.scheme, U.toBase, U.point, inferInstance, U.map_point,
    (U.isElementary_iff).mp hU, V, W, hcompl, hVfin, ?_⟩
  intro w hwu hwq
  obtain ⟨z, hz⟩ := hW w
  rw [← hz] at hwu hwq
  have hisolated : IsIsolatedPoint
      (f.asFiber ((pullback.fst f U.toBase).base ((j none).base z))) :=
    isIsolatedPoint_asFiber_of_elementary_baseChange f s U hU ((j none).base z) hwu
      (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hwq)
  have hmem : (pullback.fst f U.toBase).base ((j none).base z) ∈
      {x : X | f.base x = s ∧ f.QuasiFiniteAt x} := by
    exact ⟨base_fst_eq_of_base_snd_eq f U _ hwu,
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr hisolated⟩
  rw [← hxrange] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact hnone z hwu i hi.symm

/-- **Stacks Project, Tag 02LP**, the final assertion. Let `f : X ⟶ S` be separated and locally of
finite type with finite fibre over `s : S`. Then there is an elementary étale neighbourhood
`(U, u)` of `s` and a decomposition of `U ×_S X` into two complementary open-and-closed pieces `V`
and `W` such that `V ⟶ U` is finite and `W` has no point over `u` at all. -/
@[stacks 02LP "the final assertion: `W_u = ∅` when the fibre over `s` is finite",
  ega "IV 18.12.1" "separated, finite fibre", ega "IV 18.12.3"]
theorem exists_elementaryEtale_isCompl_isEmpty_fiber_of_finite_fiber {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f] {s : S}
    (hfin : (f.base ⁻¹' {s}).Finite) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U), Etale g ∧ g.base u = s ∧
        IsIso (g.residueFieldMap u) ∧
      ∃ V W : (pullback f g).Opens, IsCompl V W ∧
        IsFinite (V.ι ≫ pullback.snd f g) ∧
        ∀ w : W, (pullback.snd f g).base (W.ι.base w) ≠ u := by
  classical
  obtain ⟨n, x, hxinj, hxrange⟩ := hfin.fin_param
  have hx : ∀ i, f.base (x i) = s := by
    intro i
    have hmem : x i ∈ f.base ⁻¹' {s} := by
      rw [← hxrange]
      exact Set.mem_range_self i
    simpa using hmem
  have hxisolated : ∀ i, IsOpen {f.asFiber (x i)} := by
    intro i
    have : Finite (f.fiber (f.base (x i))) := by
      rw [hx i]
      exact (f.fiberHomeo s).finite_iff.mpr hfin
    exact isOpen_discrete _
  obtain ⟨U, hU, P, j, hjopen, -, hjdesc, v, hjfin, hvx, hvfib, -, hnone⟩ :=
    exists_elementaryEtaleNeighborhood_decomposition f s n x hx hxinj hxisolated
  obtain ⟨V, W, hcompl, hVfin, hW⟩ := exists_isCompl_isFinite_of_isIso_sigmaDesc
    (pullback.snd f U.toBase) P j hjopen hjdesc hjfin
  refine ⟨U.scheme, U.toBase, U.point, inferInstance, U.map_point,
    (U.isElementary_iff).mp hU, V, W, hcompl, hVfin, ?_⟩
  intro w hwu
  obtain ⟨z, hz⟩ := hW w
  rw [← hz] at hwu
  have hzx : (pullback.fst f U.toBase).base ((j none).base z) ∈ f.base ⁻¹' {s} :=
    base_fst_eq_of_base_snd_eq f U _ hwu
  rw [← hxrange] at hzx
  obtain ⟨i, hi⟩ := hzx
  exact hnone z hwu i hi.symm

/-- **Stacks Project, Tag 02LP**, the final assertion, with the residue field clause of the
neighbourhood dropped: for a separated morphism locally of finite type with finite fibre over `s`
there are an étale `g : U ⟶ S`, a point `u` of `U` over `s`, and a decomposition of `U ×_S X` into
two complementary open-and-closed pieces, the first finite over `U` and the second with no point
over `u`. -/
@[ega "IV 18.12.3" "partial", sga "7 IX 3.1.3" "partial"]
theorem exists_etale_isCompl_isEmpty_fiber_of_finite_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsSeparated f] {s : S} (hfin : (f.base ⁻¹' {s}).Finite) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U), Etale g ∧ g.base u = s ∧
      ∃ V W : (Limits.pullback f g).Opens, IsCompl V W ∧
        IsFinite (V.ι ≫ Limits.pullback.snd f g) ∧
        ∀ w : W, (Limits.pullback.snd f g).base (W.ι.base w) ≠ u := by
  obtain ⟨U, g, u, hg, hgu, -, V, W, hcompl, hVfin, hWu⟩ :=
    exists_elementaryEtale_isCompl_isEmpty_fiber_of_finite_fiber f hfin
  exact ⟨U, g, u, hg, hgu, V, W, hcompl, hVfin, hWu⟩

end AlgebraicGeometry

end
