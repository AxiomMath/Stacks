module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkSurjectivity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.SingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.QuasiFiniteEtaleLocalisation
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The geometric input of the germ decomposition of a finite-support stalk

Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes in the Stacks sense, i.e. one which
is both locally of finite type and locally quasi-finite in the Mathlib sense, let `ȳ` be a
geometric point of `Y` and let `x̄` be a geometric point of `X` over `ȳ`. The source's proof of
Stacks 0F6P represents a germ at `x̄` on an *open* of a base change `X_V` which is finite over the
étale neighbourhood `V` of `ȳ` and meets the geometric fibre only in `x̄`. This file produces such
an open, for an arbitrary étale neighbourhood of `x̄` in which the germ is given.

The route is the source's: `U → Y` is locally quasi-finite for every étale `U → X`, so its fibre
over the image of `ȳ` is discrete, and Stacks 02LM
(`AlgebraicGeometry.exists_etale_finite_opens_of_isolated_fiber_points`) supplies an étale
neighbourhood `V` of that image together with an open of `U ×_Y V` finite over `V` whose fibre over
the chosen point of `V` is one point with purely inseparable residue extension. That open maps
étale-ly to `X_V`; shrinking `V` around an affine open of `X_V` containing the image, the map
becomes a finite étale morphism with singleton fibre, hence an isomorphism onto an open of `X_V`
over a neighbourhood of the image point by Stacks 04DH
(`AlgebraicGeometry.exists_open_restrict_isIso_of_finite_etale_fiber_eq_singleton`).

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.exists_etale_finite_open_of_geometricPoint` — Stacks 02LM read at a geometric
  point: an étale neighbourhood of the image geometric point and an open of the base change,
  finite over it, through which the given lift factors uniquely.
* `AlgebraicGeometry.exists_etale_finite_open_lift_of_isSeparated` — the separated case of the
  shrinking step, where the open of `U ×_Y V` already maps into an affine open of `X ×_Y V`.
* `AlgebraicGeometry.exists_etale_finite_open_lift` — the same with the lift taken on an étale
  scheme `U` over `X`, and the open an open of `X ×_Y V` rather than of `U ×_Y V`; this is the
  shrinking step of the source's argument.
* `AlgebraicGeometry.SmallEtale.exists_finite_open_neighborhood` — the previous result transported
  into the language of the small étale site: an element of the category of elements of
  `AlgebraicGeometry.geometricPointFiber` on `Y`, an open of the base change finite over it, and a
  morphism of the site onto the given étale neighbourhood of the point of the geometric fibre.

## Implementation notes

Uniqueness of the lift of the geometric point into the produced open is carried instead of the
singleton-fibre and purely-inseparable conditions of Stacks 02LM. The two are equivalent in the
presence of finiteness — `eq_of_comp_eq_of_preimage_singleton_of_isPurelyInseparable` derives the
former from the latter — but only the former survives the two shrinkings of the argument without
being re-derived, and it is what the decomposition map needs: that no second point of the geometric
fibre lands in the support.

The intermediate scheme-theoretic statements are phrased with the structure morphism `U ⟶ X` of the
étale neighbourhood explicit rather than with `U` an object of the small étale site, because the
appeal to Stacks 02LM is to the composite `U ⟶ X ⟶ Y` and the output is an open of `X ×_Y V`, so
neither end of the argument lives over a single base.

## References

* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
* [Stacks Project, Tag 02LM](https://stacks.math.columbia.edu/tag/02LM)
* [Stacks Project, Tag 04DH](https://stacks.math.columbia.edu/tag/04DH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

section SchemeLevel

/-- If `f x = y` and the composite `κ(y) ≅ κ(f x) ⟶ κ(x)` of the identification with
`f.residueFieldMap x` is purely inseparable, then `f.residueFieldMap x` is purely inseparable. -/
public theorem residueFieldMap_isPurelyInseparable_of_congr
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y)
    (hp : ((Y.residueFieldCongr h).inv ≫ f.residueFieldMap x).hom.IsPurelyInseparable) :
    (f.residueFieldMap x).hom.IsPurelyInseparable := by
  subst y
  simpa using hp

/-- Purely inseparable residue extension passes to a factor of a composite. -/
public theorem residueFieldMap_isPurelyInseparable_of_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (h : ((f ≫ g).residueFieldMap x).hom.IsPurelyInseparable) :
    (f.residueFieldMap x).hom.IsPurelyInseparable := by
  rw [Scheme.residueFieldMap_comp] at h
  let a := (g.residueFieldMap (f x)).hom
  let b := (f.residueFieldMap x).hom
  let := a.toAlgebra
  let := b.toAlgebra
  let := (b.comp a).toAlgebra
  have : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsPurelyInseparable (Z.residueField (g (f x))) (X.residueField x) := h
  exact IsPurelyInseparable.tower_top (Z.residueField (g (f x)))
    (Y.residueField (f x)) (X.residueField x)

/-- A closed map admits, around a point, an open whose preimage lies in a given open containing the
fibre over that point. -/
public theorem exists_open_preimage_le_of_isClosedMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsClosedMap f) (y : Y) (U : TopologicalSpace.Opens X)
    (hU : f ⁻¹' {y} ⊆ U) :
    ∃ V : TopologicalSpace.Opens Y, y ∈ V ∧ f ⁻¹' (V : Set Y) ⊆ U := by
  refine ⟨⟨(f '' (U : Set X)ᶜ)ᶜ, (hf _ U.isOpen.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hU hxy)
  · intro x hx
    by_contra hn
    exact hx ⟨x, hn, rfl⟩

/-- A point of a fibre of a morphism which is locally of finite type and locally quasi-finite is
isolated in that fibre. -/
@[sga "3 V 7.3" "partial"]
public theorem isIsolatedPoint_asFiber {X Y : Scheme.{u}} (g : X ⟶ Y)
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] (x : X) :
    IsIsolatedPoint (g.asFiber x) :=
  g.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (g.quasiFiniteAt x)

/-- An étale morphism which becomes finite after a separated morphism, with singleton fibre and
purely inseparable residue extension at the chosen point, is an open immersion over an open
neighbourhood of the image of that point. -/
public theorem exists_open_preimage_isOpenImmersion_of_finite_comp
    {W T S : Scheme.{u}} (h : W ⟶ T) (g : T ⟶ S)
    [Etale h] [IsSeparated g] [IsFinite (h ≫ g)] (w : W)
    (hfiber : (h ≫ g) ⁻¹' {(h ≫ g) w} = {w})
    (hpure : ((h ≫ g).residueFieldMap w).hom.IsPurelyInseparable) :
    ∃ V : S.Opens, (h ≫ g) w ∈ V ∧
      IsOpenImmersion (((h ≫ g) ⁻¹ᵁ V).ι ≫ h) := by
  let : IsFinite h := IsFinite.of_comp h g
  have hf : h ⁻¹' {h w} = {w} := by
    apply Set.Subset.antisymm
    · intro z hz
      have hh : z ∈ (h ≫ g) ⁻¹' {(h ≫ g) w} := congrArg g hz
      simpa only [hfiber, Set.mem_singleton_iff] using hh
    · rintro z rfl
      rfl
  have hp := residueFieldMap_isPurelyInseparable_of_comp h g w hpure
  obtain ⟨O, hw, hO⟩ :=
    AlgebraicGeometry.exists_open_restrict_isIso_of_finite_etale_fiber_eq_singleton
      h (h w) w hf (by
        change (((T.residueFieldCongr (show h w = h w from rfl)).inv ≫
          h.residueFieldMap w).hom).IsPurelyInseparable
        simpa using hp)
  let : IsIso (h ∣_ O) := hO
  have : IsOpenImmersion (h ∣_ O) := inferInstance
  obtain ⟨V, hv, hV⟩ := exists_open_preimage_le_of_isClosedMap
    (h ≫ g) (h ≫ g).isClosedMap ((h ≫ g) w) (h ⁻¹ᵁ O) (by
      intro z hz
      have : z = w := by simpa only [hfiber, Set.mem_singleton_iff] using hz
      subst z
      exact hw)
  have hle : (h ≫ g) ⁻¹ᵁ V ≤ h ⁻¹ᵁ O := hV
  refine ⟨V, hv, ?_⟩
  have he : ((h ≫ g) ⁻¹ᵁ V).ι ≫ h =
      W.homOfLE hle ≫ (h ∣_ O) ≫ O.ι := by
        rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  rw [he]
  infer_instance

/-- A morphism from a geometric point to `X` whose image lies in an open `O` lifts to `O`. -/
private theorem exists_comp_eq_of_apply_mem {Y X : Scheme.{u}} (s : GeometricPoint Y)
    (O : X.Opens) (a : s.source ⟶ X) (ha : a default ∈ O) :
    ∃ b : s.source ⟶ (↑O : Scheme.{u}), b ≫ O.ι = a :=
  ⟨IsOpenImmersion.lift O.ι a (by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    exact ⟨⟨_, ha⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩

/-- **Stacks 02LM at a geometric point.** Let `f : X ⟶ Y` be locally of finite type and locally
quasi-finite and let `p` be a lift of a geometric point `s` of `Y` to `X`. Then there is an étale
neighbourhood `(U, q)` of `s` in `Y` and an open `W` of `X ×_Y U`, finite over `U`, through which
`p` and `q` factor by a lift which is the unique lift of `q` into `W`. -/
public theorem exists_etale_finite_open_of_geometricPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (s : GeometricPoint Y) (p : s.source ⟶ X) (hp : p ≫ f = s.hom) :
    ∃ (U : Scheme.{u}) (g : U ⟶ Y) (_ : Etale g)
      (q : s.source ⟶ U) (_ : q ≫ g = s.hom)
      (W : (pullback f g).Opens) (r : s.source ⟶ W),
      IsFinite (W.ι ≫ pullback.snd f g) ∧
      r ≫ W.ι ≫ pullback.fst f g = p ∧
      r ≫ W.ι ≫ pullback.snd f g = q ∧
      (W.ι ≫ pullback.snd f g) ⁻¹' {q default} = {r default} ∧
      ((W.ι ≫ pullback.snd f g).residueFieldMap (r default)).hom.IsPurelyInseparable ∧
      ∀ r' : s.source ⟶ W, r' ≫ W.ι ≫ pullback.snd f g = q → r' = r := by
  obtain ⟨U, m, V, w, hV, _, hcover⟩ :=
    AlgebraicGeometry.exists_etale_finite_opens_of_isolated_fiber_points f 1
      (s.hom default) (fun _ => p default)
      (fun _ => congrArg (fun h : s.source ⟶ Y => h default) hp)
      (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ => isIsolatedPoint_asFiber f _)
  obtain ⟨q, hq, hqpoint⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    U.toBase s.hom U.point U.map_point
  let z := pullback.lift p q (hp.trans hq.symm)
  have hzfst : (pullback.fst f U.toBase) (z default) = p default := by
    change (z ≫ pullback.fst f U.toBase) default = _
    exact congrArg (fun h : s.source ⟶ X => h default) (pullback.lift_fst p q _)
  have hzsnd : (pullback.snd f U.toBase) (z default) = U.point := by
    change (z ≫ pullback.snd f U.toBase) default = _
    exact (congrArg (fun h : s.source ⟶ U.scheme => h default)
      (pullback.lift_snd p q _)).trans hqpoint
  obtain ⟨j, hj⟩ := hcover 0 (z default) hzsnd hzfst
  let W := V 0 j
  have hW : z default ∈ W := by rw [← hj]; exact (w 0 j).property
  obtain ⟨r, hr⟩ := exists_comp_eq_of_apply_mem s W z hW
  obtain ⟨hfinite, hfiber, _, hwp, _, hpure⟩ := hV 0 j
  let d := W.ι ≫ pullback.snd f U.toBase
  have hrd : r ≫ d = q := by
    change (r ≫ W.ι) ≫ pullback.snd f U.toBase = q
    rw [hr]
    exact pullback.lift_snd p q _
  have hpoint (r' : s.source ⟶ W) (h : r' ≫ d = q) : r' default = w 0 j := by
    have hh : r' default ∈ d ⁻¹' {U.point} := by
      change (r' ≫ d) default = U.point
      rw [h, hqpoint]
    change d ⁻¹' {U.point} = {w 0 j} at hfiber
    rw [hfiber] at hh
    exact hh
  have hdr : d (r default) = q default := congrArg (fun k : s.source ⟶ U.scheme => k default) hrd
  have hfib' : d.base ⁻¹' {d.base (r default)} = {r default} := by
    rw [hdr, hqpoint, hpoint r hrd]
    exact hfiber
  have hpure' : (d.residueFieldMap (r default)).hom.IsPurelyInseparable := by
    rw [hpoint r hrd]
    exact residueFieldMap_isPurelyInseparable_of_congr d (w 0 j) U.point hwp hpure
  refine ⟨U.scheme, U.toBase, inferInstance, q, hq, W, r, hfinite, ?_, hrd, ?_, hpure', ?_⟩
  · change (r ≫ W.ι) ≫ pullback.fst f U.toBase = p
    rw [hr]
    exact pullback.lift_fst p q _
  · change d ⁻¹' {q default} = {r default}
    rw [← hdr]
    exact hfib'
  · intro r' hr'
    refine eq_of_comp_eq_of_preimage_singleton_of_isPurelyInseparable d (r default) hfib'
      r' r (hr'.trans hrd.symm) ?_ hpure'
    rw [Subsingleton.elim (IsLocalRing.closedPoint s.residueField) (default : ↥s.source)]
    exact (hpoint r' hr').trans (hpoint r hrd).symm

/-- The separated case of the shrinking step: for `h : U ⟶ X` étale and `f : X ⟶ Y` separated,
locally of finite type and locally quasi-finite, a lift of a geometric point of `Y` to `U` extends
to an open subscheme of some `X ×_Y V` finite over an affine étale neighbourhood `V`, compatibly
with `h` and with a unique lift of the geometric point. -/
public theorem exists_etale_finite_open_lift_of_isSeparated
    {U X Y : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ Y)
    [Etale h] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsSeparated f]
    (s : GeometricPoint Y) (p : s.source ⟶ U)
    (hp : p ≫ h ≫ f = s.hom) :
    ∃ (V : Scheme.{u}) (g : V ⟶ Y) (_ : Etale g) (_ : IsAffine V)
      (q : s.source ⟶ V) (_ : q ≫ g = s.hom)
      (W : Scheme.{u}) (i : W ⟶ pullback f g) (_ : IsOpenImmersion i)
      (j : W ⟶ U) (r : s.source ⟶ W),
      IsFinite (i ≫ pullback.snd f g) ∧
      i ≫ pullback.fst f g = j ≫ h ∧ r ≫ j = p ∧
      r ≫ i ≫ pullback.snd f g = q ∧
      ∀ r' : s.source ⟶ W, r' ≫ i ≫ pullback.snd f g = q → r' = r := by
  have : LocallyQuasiFinite h := (locallyQuasiFinite_of_etale h).2
  obtain ⟨V, g, hg, q, hq, W, r, hfin, hrU, hrV, hfib, hpure, huniq⟩ :=
    exists_etale_finite_open_of_geometricPoint (h ≫ f) s p hp
  let : Etale g := hg
  let d := W.ι ≫ pullback.snd (h ≫ f) g
  let a : (↑W : Scheme.{u}) ⟶ pullback f g :=
    W.ι ≫ pullback.map (h ≫ f) g f g h (𝟙 _) (𝟙 _) (by simp) (by simp)
  have haV : a ≫ pullback.snd f g = d := by
    simp only [a, d, Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
  have haU : a ≫ pullback.fst f g = W.ι ≫ pullback.fst (h ≫ f) g ≫ h := by
    simp only [a, Category.assoc, pullback.map, pullback.lift_fst]
  have : Etale a := by
    have : MorphismProperty.IsStableUnderComposition @Etale :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    have : Etale (pullback.map (h ≫ f) g f g h (𝟙 _) (𝟙 _)
        (by simp) (by simp)) :=
      MorphismProperty.pullbackMap (P := @Etale) inferInstance inferInstance rfl (by simp)
    dsimp [a]
    infer_instance
  have : IsFinite d := hfin
  have hfinA : IsFinite (a ≫ pullback.snd f g) := haV.symm ▸ hfin
  have : IsFinite (a ≫ pullback.snd f g) := hfinA
  have hrV' : d (r default) = q default :=
    congrArg (fun k : s.source ⟶ V => k default) hrV
  obtain ⟨O, hO, hOi⟩ := exists_open_preimage_isOpenImmersion_of_finite_comp
    a (pullback.snd f g) (r default)
    (by simpa only [haV, hrV'] using hfib) (by rw [haV]; exact hpure)
  have hqO : q default ∈ O := by simpa only [haV, hrV'] using hO
  have : IsOpenImmersion ((d ⁻¹ᵁ O).ι ≫ a) := by
    rw [haV] at hOi
    exact hOi
  obtain ⟨_, ⟨A₀, hA, rfl⟩, hqA, hAO⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open hqO O.isOpen
  let A : V.Opens := A₀
  have : IsAffine (↑A : Scheme.{u}) := hA
  have hAO' : A ≤ O := hAO
  have hqA' : q default ∈ A := hqA
  let R := d ⁻¹ᵁ A
  have : IsOpenImmersion (R.ι ≫ a) := by
    have he : R.ι ≫ a =
        (↑W : Scheme.{u}).homOfLE (d.preimage_mono hAO') ≫ (d ⁻¹ᵁ O).ι ≫ a := by
      rw [Scheme.homOfLE_ι_assoc]
    rw [he]
    infer_instance
  obtain ⟨q', hq'⟩ := exists_comp_eq_of_apply_mem s A q hqA'
  obtain ⟨r', hr'⟩ := exists_comp_eq_of_apply_mem s R r (show d (r default) ∈ A by
    rw [hrV']
    exact hqA')
  let g' := A.ι ≫ g
  let i : (↑R : Scheme.{u}) ⟶ pullback f g' :=
    pullback.lift (R.ι ≫ a ≫ pullback.fst f g) (d ∣_ A) (by
      calc
        (R.ι ≫ a ≫ pullback.fst f g) ≫ f = R.ι ≫ d ≫ g := by
          simp only [Category.assoc, pullback.condition, ← haV]
        _ = (d ∣_ A) ≫ g' := (morphismRestrict_ι_assoc d A g).symm)
  let t : pullback f g' ⟶ pullback f g :=
    pullback.map f g' f g (𝟙 _) A.ι (𝟙 _) (by simp) (by simp [g'])
  have hit : i ≫ t = R.ι ≫ a := by
    apply pullback.hom_ext <;>
      simp only [i, t, Category.assoc, pullback.map, pullback.lift_fst,
        pullback.lift_snd_assoc, pullback.lift_snd, Category.comp_id, haV, morphismRestrict_ι]
    rfl
  have : IsOpenImmersion t :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      inferInstance inferInstance (by simp) rfl
  have : IsOpenImmersion i := by
    have : IsOpenImmersion (i ≫ t) := hit.symm ▸ inferInstance
    exact IsOpenImmersion.of_comp i t
  have hiV : i ≫ pullback.snd f g' = d ∣_ A := pullback.lift_snd _ _ _
  have hrq : r' ≫ i ≫ pullback.snd f g' = q' := by
    apply (cancel_mono A.ι).1
    rw [Category.assoc, hiV, morphismRestrict_ι, ← Category.assoc, hr', hq']
    exact hrV
  refine ⟨A, g', inferInstance, inferInstance, q', by simp [g', ← Category.assoc, hq', hq],
    R, i, inferInstance, R.ι ≫ W.ι ≫ pullback.fst (h ≫ f) g, r', ?_, ?_, ?_,
    hrq, ?_⟩
  · rw [hiV]
    exact inferInstanceAs (IsFinite (d ∣_ A))
  · simp only [i, pullback.lift_fst, Category.assoc, haU]
  · rw [← Category.assoc, hr']
    exact hrU
  · intro r'' hr''
    apply (cancel_mono R.ι).1
    rw [hr']
    apply huniq
    have H := congrArg (fun k => k ≫ A.ι) hr''
    simpa only [Category.assoc, hiV, morphismRestrict_ι, hq'] using H

/-- **The shrinking step of the surjectivity half of Stacks 0F6P.** For `h : U ⟶ X` étale and
`f : X ⟶ Y` locally of finite type and locally quasi-finite, a lift of a geometric point of `Y` to
`U` extends to an open subscheme of some `X ×_Y V` finite over an affine étale neighbourhood `V` of
the geometric point, compatibly with `h` and with a unique lift of the geometric point. -/
public theorem exists_etale_finite_open_lift
    {U X Y : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ Y)
    [Etale h] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (s : GeometricPoint Y) (p : s.source ⟶ U)
    (hp : p ≫ h ≫ f = s.hom) :
    ∃ (V : Scheme.{u}) (g : V ⟶ Y) (_ : Etale g) (_ : IsAffine V)
      (q : s.source ⟶ V) (_ : q ≫ g = s.hom)
      (W : Scheme.{u}) (i : W ⟶ pullback f g) (_ : IsOpenImmersion i)
      (j : W ⟶ U) (r : s.source ⟶ W),
      IsFinite (i ≫ pullback.snd f g) ∧
      i ≫ pullback.fst f g = j ≫ h ∧ r ≫ j = p ∧
      r ≫ i ≫ pullback.snd f g = q ∧
      ∀ r' : s.source ⟶ W, r' ≫ i ≫ pullback.snd f g = q → r' = r := by
  obtain ⟨_, ⟨O₀, hO, rfl⟩, hpO, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show h (p default) ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).isOpen
  let O : X.Opens := O₀
  have : IsAffine (↑O : Scheme.{u}) := hO
  let R := h ⁻¹ᵁ O
  obtain ⟨p', hp'⟩ := exists_comp_eq_of_apply_mem s R p hpO
  let h' := h ∣_ O
  let f' := O.ι ≫ f
  obtain ⟨V, g, hg, hV, q, hq, W, i, hi, j, r, hfin, hiX, hrU, hrV, huniq⟩ :=
    exists_etale_finite_open_lift_of_isSeparated h' f' s p' (by
      dsimp [h', f']
      rw [morphismRestrict_ι_assoc, ← Category.assoc, hp']
      exact hp)
  let : Etale g := hg
  let : IsOpenImmersion i := hi
  let t : pullback f' g ⟶ pullback f g :=
    pullback.map f' g f g O.ι (𝟙 _) (𝟙 _) (by simp [f']) (by simp)
  have : IsOpenImmersion t :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      inferInstance inferInstance rfl (by simp)
  have htX : t ≫ pullback.fst f g = pullback.fst f' g ≫ O.ι := by
    simp only [t, pullback.map, pullback.lift_fst]
  have htV : t ≫ pullback.snd f g = pullback.snd f' g := by
    simp only [t, pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨V, g, hg, hV, q, hq, W, i ≫ t, inferInstance, j ≫ R.ι, r, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Category.assoc, htV] using hfin
  · rw [Category.assoc, htX, ← Category.assoc, hiX, Category.assoc]
    dsimp [h']
    rw [morphismRestrict_ι, Category.assoc]
  · rw [← Category.assoc, hrU, hp']
  · simpa only [Category.assoc, htV] using hrV
  · intro r' hr'
    apply huniq
    simpa only [Category.assoc, htV] using hr'

end SchemeLevel

namespace SmallEtale

section Site

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (s : GeometricPoint Y.obj)

/-- **The geometric input of the surjectivity half of Stacks 0F6P.** Given a point `x` of the
geometric fibre of `f` over `s` and an étale neighbourhood `N` of the corresponding geometric point
of `X`, there is an étale neighbourhood `U` of `s` in `Y`, a Zariski open `O` of the base change
`X_U` finite over `U`, a lift `r` of `s` to `O` which is the unique such lift, and a morphism `t`
of the small étale site of `X` from `O` to `N` carrying `r` to the chosen lift on `N`. -/
public theorem exists_finite_open_neighborhood
    (x : GeometricFiberPoint B f s)
    (N : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).Elements) :
    ∃ (U : (geometricPointFiber B Y.obj Y.property s).Elements)
      (O : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1)).Opens)
      (r : s.source ⟶ (↑O : Scheme.{u}))
      (t : openObject B X.obj X.property (baseChange B f U.1) O ⟶ N.1),
      IsFinite (O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)) ∧
      r ≫ O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f) = U.2.1 ∧
      r ≫ (SmallEtale.toScheme B X.obj X.property).map t = N.2.1 ∧
      ∀ r' : s.source ⟶ (↑O : Scheme.{u}),
        r' ≫ O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f) = U.2.1 → r' = r := by
  let h := B.inclusion.map N.1.obj.hom
  have : Etale h := N.1.property
  obtain ⟨V, g, hg, hV, q, hq, W, i, hi, j, r, hfin, hiX, hrN, hrV, huniq⟩ :=
    exists_etale_finite_open_lift h (B.inclusion.map f) s N.2.1
      (by rw [← Category.assoc, N.2.2]; exact x.2)
  let : Etale g := hg
  let : AlgebraicGeometry.IsAffine V := hV
  let : IsOpenImmersion i := hi
  have hVB : B.Contains V :=
    (Scheme.size_le_of_locallyOfFiniteType g).trans_lt Y.property
  let Vb : B.Scheme := ⟨V, hVB⟩
  obtain ⟨gb, rfl⟩ : ∃ gb : Vb ⟶ Y, B.inclusion.map gb = g :=
    ⟨B.inclusion.preimage g, B.inclusion.map_preimage (X := Vb) (Y := Y) g⟩
  let U₀ : SmallEtale B Y.obj Y.property := ⟨Over.mk gb, hg⟩
  let U : (geometricPointFiber B Y.obj Y.property s).Elements :=
    Functor.elementsMk _ U₀ ⟨q, hq⟩
  let pb := (IsPullback.of_hasPullback gb f).map B.inclusion
  let e : pullback (B.inclusion.map f) (B.inclusion.map gb) ≅
      (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1) :=
    (pullbackSymmetry _ _) ≪≫ pb.isoPullback.symm
  have heX : e.hom ≫ B.inclusion.map (pullback.snd gb f) =
      pullback.fst (B.inclusion.map f) (B.inclusion.map gb) := by
    simp [e]
  have heV : e.hom ≫ B.inclusion.map (pullback.fst gb f) =
      pullback.snd (B.inclusion.map f) (B.inclusion.map gb) := by
    simp [e]
  let i' := i ≫ e.hom
  have hi'X : i' ≫ B.inclusion.map (pullback.snd gb f) = j ≫ h := by
    rw [Category.assoc, heX, hiX]
  have hi'V : i' ≫ B.inclusion.map (pullback.fst gb f) =
      i ≫ pullback.snd (B.inclusion.map f) (B.inclusion.map gb) := by
    rw [Category.assoc, heV]
  have : IsOpenImmersion i' := inferInstance
  let O := i'.opensRange
  let k := i'.isoOpensRange.inv
  let t₀ : openObject B X.obj X.property (baseChange B f U.1) O ⟶ N.1 := by
    refine ⟨Over.homMk (B.inclusion.preimage (k ≫ j)) ?_⟩
    apply B.inclusion.map_injective
    simp only [Over.mk_hom, Functor.map_comp, Functor.map_preimage]
    change (k ≫ j) ≫ h = O.ι ≫ B.inclusion.map (pullback.snd gb f)
    rw [Category.assoc, ← hi'X, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  have ht₀ : (SmallEtale.toScheme B X.obj X.property).map t₀ = k ≫ j :=
    B.inclusion.map_preimage _
  let r₀ := r ≫ i'.isoOpensRange.hom
  have hr₀ : r₀ ≫ O.ι = r ≫ i' := by
    simp only [r₀, O, Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  refine ⟨U, O, r₀, t₀, ?_, ?_, ?_, ?_⟩
  · change IsFinite (O.ι ≫ B.inclusion.map (pullback.fst gb f))
    rw [← Scheme.Hom.isoOpensRange_inv_comp i', Category.assoc, hi'V]
    let : IsFinite (i ≫ pullback.snd (B.inclusion.map f) (B.inclusion.map gb)) := hfin
    infer_instance
  · change r₀ ≫ O.ι ≫ B.inclusion.map (pullback.fst gb f) = q
    rw [← Category.assoc, hr₀, Category.assoc, hi'V]
    exact hrV
  · rw [ht₀]
    simp only [r₀, k, Category.assoc, Iso.hom_inv_id_assoc]
    exact hrN
  · intro r' hr'
    have H : r' ≫ k = r := by
      apply huniq
      rw [← hi'V]
      change (r' ≫ i'.isoOpensRange.inv) ≫ i' ≫
        B.inclusion.map (pullback.fst gb f) = q
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp_assoc]
      exact hr'
    change r' = r ≫ i'.isoOpensRange.hom
    rw [← H]
    simp only [k, Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **Uniqueness of the point of the geometric fibre lifting into an open with a unique lift of the
geometric point.** This is the variant of
`AlgebraicGeometry.SmallEtale.eq_of_fiberPointLift_mem_of_preimage_singleton` which takes
uniqueness of the lift of the geometric point as the hypothesis, in the form
`AlgebraicGeometry.SmallEtale.exists_finite_open_neighborhood` produces it. -/
public theorem eq_of_fiberPointLift_mem_of_unique_lift
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    (O : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1)).Opens)
    (r : s.source ⟶ (↑O : Scheme.{u}))
    (huniq : ∀ r' : s.source ⟶ (↑O : Scheme.{u}),
      r' ≫ O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f) = U.2.1 → r' = r)
    (x : GeometricFiberPoint B f s) (hx : r ≫ O.ι = fiberPointLift B f s U.1 U.2 x)
    (x' : GeometricFiberPoint B f s)
    (hmem : (fiberPointLift B f s U.1 U.2 x').base default ∈
      (O : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1)))) :
    x' = x := by
  let r' := IsOpenImmersion.lift O.ι (fiberPointLift B f s U.1 U.2 x')
    (fiberPointLift_range_subset_opens B f s U.1 U.2 x' O hmem)
  have hr' : r' ≫ O.ι = fiberPointLift B f s U.1 U.2 x' := IsOpenImmersion.lift_fac _ _ _
  have h1 : r' = r := by
    refine huniq r' ?_
    rw [← Category.assoc, hr']
    exact fiberPointLift_comp_fst B f s U.1 U.2 x'
  have h2 : fiberPointLift B f s U.1 U.2 x' = fiberPointLift B f s U.1 U.2 x := by
    rw [← hr', h1, hx]
  exact Subtype.ext ((fiberPointLift_comp_snd B f s U.1 U.2 x').symm.trans
    ((congrArg (fun m => m ≫ B.inclusion.map (pullback.snd U.1.obj.hom f)) h2).trans
      (fiberPointLift_comp_snd B f s U.1 U.2 x)))

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v})

open Classical in
/-- The preimage of a single-summand germ under the germ decomposition map, produced from an open
of `X_U` finite over the étale neighbourhood `U` of the geometric point of `Y` into which the
geometric point lifts uniquely, and which maps to the étale neighbourhood of the point of the
geometric fibre carrying the germ.

This is the variant of `AlgebraicGeometry.SmallEtale.exists_preimage_of_openFiniteSupport` whose
hypothesis is uniqueness of the lift rather than the singleton fibre and purely inseparable
residue extension which imply it. -/
public theorem exists_preimage_of_unique_openFiniteSupport
    (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{max u v} (FiniteSupport B f V))
    (x : GeometricFiberPoint B f s) (W : SmallEtale B X.obj X.property)
    (q : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).obj W)
    (a₀ : F.obj.obj (op W))
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    (O : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1)).Opens)
    (τ : openObject B X.obj X.property (baseChange B f U.1) O ⟶ W)
    (p : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).obj
      (openObject B X.obj X.property (baseChange B f U.1) O))
    (hfin : IsFinite (O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)))
    (huniq : ∀ r' : s.source ⟶ (↑O : Scheme.{u}),
      r' ≫ O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f) = U.2.1 → r' = p.1)
    (hτ : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).map τ p = q)
    (hp : p.1 ≫ O.ι = fiberPointLift B f s U.1 U.2 x) :
    ∃ g, finiteSupportStalkToFiberStalks B f s F hsmall g =
      DirectSum.of (fun y : GeometricFiberPoint B f s =>
        ↑(etaleStalk B X.obj X.property (y.toGeometricPoint B f s) F.obj)) x
        (etaleGerm B X.obj X.property (x.toGeometricPoint B f s) F.obj W q a₀) := by
  have hO : IsFiniteSupport B f U.1
      (O : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))) :=
    isFiniteSupport_of_isFinite_opens B f U.1 O hfin
  set E : FiniteSupport B f U.1 := ⟨(O : Set _), hO⟩ with hE
  set a := (supportedSectionsOpenEquivSections B X.obj X.property F (baseChange B f U.1) O
    (finiteSupport_isLocallyClosed B f U.1 E)).symm (F.obj.map τ.op a₀) with hadef
  have huniq' : ∀ x' : GeometricFiberPoint B f s,
      (fiberPointLift B f s U.1 U.2 x').base default ∈ E.1 → x' = x := fun x' hx' =>
    eq_of_fiberPointLift_mem_of_unique_lift B f s U O p.1 huniq x hp x' hx'
  have hcomp : (colimit.ι (finiteSupportDiagram B f F U.1) E ≫
      (eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F U.1).symm ≫
      colimit.ι (etaleStalkDiagram B Y.obj Y.property s
        ((finiteSupportPushforward B f hsmall).1.obj F)) (op U))) ≫
      finiteSupportStalkToFiberStalks B f s F hsmall = fiberStalkHom B f s F U.1 U.2 E :=
    ((Category.assoc _ _ _).trans
      (congrArg (fun m => colimit.ι (finiteSupportDiagram B f F U.1) E ≫ m)
        (Category.assoc _ _ _))).trans
      (finiteSupportStalkToFiberStalks_generator B f s F hsmall U E)
  refine ⟨(colimit.ι (finiteSupportDiagram B f F U.1) E ≫
    (eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F U.1).symm ≫
    colimit.ι (etaleStalkDiagram B Y.obj Y.property s
      ((finiteSupportPushforward B f hsmall).1.obj F)) (op U))) a, ?_⟩
  have h4 : finiteSupportStalkToFiberStalks B f s F hsmall
      ((colimit.ι (finiteSupportDiagram B f F U.1) E ≫
        (eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F U.1).symm ≫
        colimit.ι (etaleStalkDiagram B Y.obj Y.property s
          ((finiteSupportPushforward B f hsmall).1.obj F)) (op U))) a) =
      fiberStalkHom B f s F U.1 U.2 E a :=
    ConcreteCategory.congr_hom hcomp a
  rw [h4, fiberStalkHom_apply, fiberStalkSum_eq_of_unique B f s F U.1 U.2 E a x huniq']
  exact congrArg (DirectSum.of (fun y : GeometricFiberPoint B f s =>
    ↑(etaleStalk B X.obj X.property (y.toGeometricPoint B f s) F.obj)) x)
    (fiberStalkComponent_openSupport B f s F U.1 U.2 O hO x W q a₀ τ p hτ hp)

/-- **The surjectivity half of Stacks 0F6P.** The germ decomposition map
`(f_{p!}F)_ȳ ⟶ ⊕_{f(x̄) = ȳ} F_x̄` is surjective. -/
@[stacks 0F6P "surjectivity of the germ decomposition"]
public theorem surjective_finiteSupportStalkToFiberStalks
    (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{max u v} (FiniteSupport B f V)) :
    Function.Surjective (finiteSupportStalkToFiberStalks B f s F hsmall) := by
  refine surjective_finiteSupportStalkToFiberStalks_of_exists_preimage B f s F hsmall ?_
  intro x W q a₀
  obtain ⟨U, O, r, t, hfin, hrU, hrN, huniq⟩ :=
    exists_finite_open_neighborhood B f s x (Functor.elementsMk _ W q)
  have hι : O.ι ≫ B.inclusion.map (pullback.snd U.1.obj.hom f) =
      B.inclusion.map (openObject B X.obj X.property (baseChange B f U.1) O).obj.hom := by
    have h := SmallEtale.toScheme_map_comp B X.obj X.property
      (openObjectι B X.obj X.property (baseChange B f U.1) O)
    rwa [openObjectι_map] at h
  have h0 : r ≫ B.inclusion.map
      (openObject B X.obj X.property (baseChange B f U.1) O).obj.hom = x.1 := by
    have ht : (SmallEtale.toScheme B X.obj X.property).map t ≫ B.inclusion.map W.obj.hom =
        B.inclusion.map (openObject B X.obj X.property (baseChange B f U.1) O).obj.hom :=
      SmallEtale.toScheme_map_comp B X.obj X.property t
    rw [← ht, ← Category.assoc, hrN]
    exact q.2
  have hsnd : r ≫ O.ι ≫ B.inclusion.map (pullback.snd U.1.obj.hom f) = x.1 := by
    rwa [hι]
  have hp : r ≫ O.ι = fiberPointLift B f s U.1 U.2 x := by
    refine ((IsPullback.of_hasPullback U.1.obj.hom f).map B.inclusion).hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans
        (hrU.trans (fiberPointLift_comp_fst B f s U.1 U.2 x).symm)
    · exact (Category.assoc _ _ _).trans
        (hsnd.trans (fiberPointLift_comp_snd B f s U.1 U.2 x).symm)
  let p : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).obj
      (openObject B X.obj X.property (baseChange B f U.1) O) := ⟨r, h0⟩
  exact exists_preimage_of_unique_openFiniteSupport B f s F hsmall x W q a₀ U O t p hfin
    huniq (Subtype.ext hrN) hp

end Site

end SmallEtale

end AlgebraicGeometry

end
