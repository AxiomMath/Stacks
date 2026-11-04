module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.FieldTheory.PerfectClosure
public import StacksFrontier.RingTheory.GeometricallyNormal.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE

/-!
# Characterizations of geometrically normal schemes

Geometric normality of a scheme over a field can be tested after arbitrary field extensions,
after finitely generated field extensions, after finite purely inseparable extensions, on the
rings of sections of affine opens, or after extension to the perfect closure of the base field.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.geometricallyNormal_tfae` gives the six equivalent characterizations of a
  geometrically normal scheme.

## Implementation notes

The six entries of the `List.TFAE` are the six numbered conditions in the source. The algebra
structure on the sections of an affine open is induced canonically by the structure morphism.
Finite generation of a field extension is expressed by `Algebra.EssFiniteType`; finiteness is
expressed by `Module.Finite`. Base change is represented by the scheme-theoretic pullback.

The tag's `k^perf` is spelled `perfectClosure k (AlgebraicClosure k)`, the largest purely
inseparable subextension of an algebraic closure of `k`, as recorded on Stacks Tag 046X in
`StacksFrontier.FieldTheory.PerfectClosure`. The reduction of the scheme-level statement to the
algebraic one, `Algebra.isNormalRing_tensorProduct_tfae` (Stacks Tag 037Z), goes through
`AlgebraicGeometry.isNormal_pullback_iff_affineSections`, which identifies the base change of
an affine open of `X` with the spectrum of the corresponding tensor product; that
identification is the content of the private `affineBaseChangeIso`.

## References

* [Stacks Project, Tag 038O](https://stacks.math.columbia.edu/tag/038O)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open CommRingCat
open scoped TensorProduct

universe u

/-- Normality of a scheme is normality, as a ring, of each of its local rings. -/
public lemma isNormal_iff_stalk_isNormalRing (Y : Scheme.{u}) :
    IsNormal Y ↔ ∀ y : Y, IsNormalRing (Y.presheaf.stalk y) := by
  constructor
  · intro h y
    have hy := (isNormal_iff_stalk_normal Y).mp h y
    have : IsDomain (Y.presheaf.stalk y) := hy.choose
    have : IsIntegrallyClosed (Y.presheaf.stalk y) := id hy.choose_spec
    exact IsNormalRing.of_isIntegrallyClosed _
  · refine fun h ↦ (isNormal_iff_stalk_normal Y).mpr fun y ↦ ?_
    obtain ⟨hD, hIC⟩ := (h y).of_isLocalRing
    exact ⟨hD, id hIC⟩

/-- Normality of a scheme transports along an isomorphism. -/
public lemma isNormal_of_iso {Y Z : Scheme.{u}} (e : Y ≅ Z) [IsNormal Z] : IsNormal Y :=
  (isNormal_iff_stalk_isNormalRing Y).2 fun y ↦
    IsNormalRing.congr (asIso (e.hom.stalkMap y)).commRingCatIsoToRingEquiv
      ((isNormal_iff_stalk_isNormalRing Z).mp inferInstance (e.hom y))

/-- An affine scheme is normal exactly when its ring of global sections is a normal ring. -/
public lemma isNormal_spec_iff {A : Type u} [CommRing A] :
    IsNormal (Spec (.of A)) ↔ IsNormalRing A := by
  rw [isNormal_iff_stalk_isNormalRing]
  constructor
  · intro h p hp
    have : p.IsPrime := hp
    exact (IsNormalRing.congr (Spec.stalkIso (.of A) ⟨p, hp⟩).commRingCatIsoToRingEquiv
      (h ⟨p, hp⟩)).of_isLocalRing
  · intro h x
    have : x.asIdeal.IsPrime := x.2
    let e := (Spec.stalkIso (.of A) x).commRingCatIsoToRingEquiv
    obtain ⟨hD, hIC⟩ :=
      (h.isLocalization x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal)).of_isLocalRing
    have : IsDomain ((Spec (.of A)).presheaf.stalk x) := e.isDomain_iff.mpr hD
    have : IsIntegrallyClosed ((Spec (.of A)).presheaf.stalk x) :=
      IsIntegrallyClosed.of_equiv e.symm
    exact IsNormalRing.of_isIntegrallyClosed _

/-- The base change to `K` of an affine open `U` of a scheme `X` over `k` is the spectrum of
`Γ(X, U) ⊗[k] K`. -/
private noncomputable def affineBaseChangeIso (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(X, U) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
    (pullback U.ι (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) : Scheme.{u}) ≅
      Spec (.of (Γ(X, U) ⊗[k] K)) := by
  letI : Algebra k Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have heq : Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) =
      hU.fromSpec ≫ f := by
    change Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫
      f.appLE ⊤ U (by simp)) = hU.fromSpec ≫ f
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU (by simp),
      Spec.map_comp, IsAffineOpen.fromSpec_top]
    congr 1
    rw [← cancel_mono (Spec (.of k)).toSpecΓ]
    simp
  have eU : pullback U.ι (pullback.fst f g) ≅ pullback hU.fromSpec (pullback.fst f g) := by
    let m := pullback.map U.ι (pullback.fst f g) hU.fromSpec (pullback.fst f g)
      hU.isoSpec.hom (𝟙 _) (𝟙 _) hU.isoSpec_hom_fromSpec.symm (by simp)
    let n := pullback.map hU.fromSpec (pullback.fst f g) U.ι (pullback.fst f g)
      hU.isoSpec.inv (𝟙 _) (𝟙 _) hU.isoSpec_inv_ι.symm (by simp)
    have hm : m ≫ n = 𝟙 _ := by
      apply pullback.hom_ext <;> dsimp [m, n, pullback.map] <;>
        simp [pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_snd]
    have hn : n ≫ m = 𝟙 _ := by
      apply pullback.hom_ext <;> dsimp [m, n, pullback.map] <;>
        simp [pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_snd]
    exact ⟨m, n, hm, hn⟩
  exact eU |>.trans
    (pullbackRightPullbackFstIso f g hU.fromSpec) |>.trans
    (pullback.congrHom heq.symm rfl) |>.trans
    (pullbackSpecIso k Γ(X, U) K)

/-- The base change of `X` to a field extension `K` of `k` is normal exactly when the base
change to `K` of the ring of sections of each affine open of `X` is a normal ring. -/
private lemma isNormal_pullback_iff_affineSections (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K] :
    IsNormal (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ↔
      ∀ U : X.affineOpens,
        letI : Algebra k Γ(X, U.1) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra;
        IsNormalRing (K ⊗[k] Γ(X, U.1)) := by
  let Y := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let fst := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  constructor
  · intro h U
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    have : IsNormal Y := h
    have : IsNormal (fst ⁻¹ᵁ (U : X.Opens)).toScheme := isNormal_open _
    let e := (isPullback_morphismRestrict fst U.1).isoPullback |>.trans
      (affineBaseChangeIso k f K U.1 U.2)
    exact IsNormalRing.congr (Algebra.TensorProduct.comm k (Γ(X, U.1)) K).toRingEquiv
      (isNormal_spec_iff.mp (isNormal_of_iso e.symm))
  · intro h
    apply ((isNormal_tfae Y).out 4 1).mp
    refine ⟨X.affineOpens, fun U ↦ fst ⁻¹ᵁ (U : X.Opens),
      fst.iSup_preimage_eq_top (iSup_affineOpens_eq_top X), fun U ↦ ?_⟩
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    let e := (isPullback_morphismRestrict fst U.1).isoPullback |>.trans
      (affineBaseChangeIso k f K U.1 U.2)
    have : IsNormal (Spec (.of (Γ(X, U.1) ⊗[k] K))) :=
      (isNormal_spec_iff).mpr <|
        IsNormalRing.congr (Algebra.TensorProduct.comm k K (Γ(X, U.1))).toRingEquiv (h U)
    exact isNormal_of_iso e

/-- An algebra whose base change along every finite purely inseparable extension is a normal
ring is geometrically normal. -/
private theorem isGeometricallyNormal_of_finitePurelyInseparable
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K]
      [IsPurelyInseparable k K], IsNormalRing (K ⊗[k] A)) :
    Algebra.IsGeometricallyNormal k A := by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  have : ExpChar k p := hp
  have : ExpChar (AlgebraicClosure k) p :=
    expChar_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  have : ExpChar (perfectClosure k (AlgebraicClosure k)) p :=
    expChar_of_injective_algebraMap
      (algebraMap k (perfectClosure k (AlgebraicClosure k))).injective p
  have : IsPerfectClosure (algebraMap k (perfectClosure k (AlgebraicClosure k))) p :=
    IsPurelyInseparable.isPRadical k (perfectClosure k (AlgebraicClosure k)) p
  exact ⟨((Algebra.isNormalRing_tensorProduct_tfae k p A
    (perfectClosure k (AlgebraicClosure k))).out 3 1).mp h⟩

/-- An algebra whose base change to the perfect closure of the base field is a normal ring is
geometrically normal. -/
private theorem isGeometricallyNormal_of_perfectClosure
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (h : IsNormalRing (perfectClosure k (AlgebraicClosure k) ⊗[k] A)) :
    Algebra.IsGeometricallyNormal k A := by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  have : ExpChar k p := hp
  have : ExpChar (AlgebraicClosure k) p :=
    expChar_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  have : ExpChar (perfectClosure k (AlgebraicClosure k)) p :=
    expChar_of_injective_algebraMap
      (algebraMap k (perfectClosure k (AlgebraicClosure k))).injective p
  have : IsPerfectClosure (algebraMap k (perfectClosure k (AlgebraicClosure k))) p :=
    IsPurelyInseparable.isPRadical k (perfectClosure k (AlgebraicClosure k)) p
  exact ⟨((Algebra.isNormalRing_tensorProduct_tfae k p A
    (perfectClosure k (AlgebraicClosure k))).out 4 1).mp h⟩

/-- **Stacks Project, Tag 038O.** The six standard characterizations of geometric normality for
a scheme over a field are equivalent. -/
@[stacks 038O]
public theorem geometricallyNormal_tfae
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    let geometricallyNormalSections := fun U : X.Opens ↦
      letI : Algebra k Γ(X, U) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
      Algebra.IsGeometricallyNormal k Γ(X, U)
    List.TFAE
      [ IsGeometricallyNormal f,
        ∀ (k' : Type u) [Field k'] [Algebra k k'],
          IsNormal (pullback f (Spec.map (ofHom (algebraMap k k')))),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
          IsNormal (pullback f (Spec.map (ofHom (algebraMap k k')))),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [Module.Finite k k']
          [IsPurelyInseparable k k'],
          IsNormal (pullback f (Spec.map (ofHom (algebraMap k k')))),
        ∀ U : X.affineOpens, geometricallyNormalSections U.1,
        IsNormal (pullback f (Spec.map
          (ofHom (algebraMap k (perfectClosure k (AlgebraicClosure k)))))) ] := by
  classical
  tfae_have 1 → 2 := by
    intro h K _ _
    let fst := pullback.fst f (Spec.map (ofHom (algebraMap k K)))
    refine (isNormal_iff_stalk_isNormalRing _).2 fun y ↦ ?_
    exact (isGeometricallyNormalAt_iff f (fst.base y)).mp
      ((isGeometricallyNormal_iff f).mp h (fst.base y)) K y rfl
  tfae_have 2 → 1 := fun h _ K _ _ y _ ↦ (isNormal_iff_stalk_isNormalRing _).mp (h K) y
  tfae_have 2 → 3 := fun h K ↦ h K
  tfae_have 3 → 4 := fun h K ↦ h K
  tfae_have 4 → 5 := by
    intro h U
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    exact isGeometricallyNormal_of_finitePurelyInseparable k Γ(X, U.1) fun K _ _ _ _ ↦
      (isNormal_pullback_iff_affineSections k X f K).mp (h K) U
  tfae_have 5 → 2 := by
    intro h K _ _
    refine (isNormal_pullback_iff_affineSections k X f K).2 fun U ↦ ?_
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    have hU : Algebra.IsGeometricallyNormal k Γ(X, U.1) := h U
    exact hU.isNormalRing_tensorProduct K
  tfae_have 2 → 6 := fun h ↦ h _
  tfae_have 6 → 5 := by
    intro h U
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    exact isGeometricallyNormal_of_perfectClosure k Γ(X, U.1)
      ((isNormal_pullback_iff_affineSections k X f
        (perfectClosure k (AlgebraicClosure k))).mp h U)
  tfae_finish

end AlgebraicGeometry

end
