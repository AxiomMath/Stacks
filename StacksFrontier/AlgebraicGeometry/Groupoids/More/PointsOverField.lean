module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Restriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Points of a groupoid scheme over a field

Every arrow of a groupoid scheme whose object scheme is the spectrum of a field `k` lifts, after
an algebraically closed field extension `k'/k`, to an arrow of the restricted groupoid whose
source and target are geometric points with residue field `k'`.  The arrow `r` gives two
embeddings of `k` into its residue field `E`, one through the source and one through the target;
a large enough algebraically closed extension `k'` of `E` admits an automorphism conjugating the
two, because two algebraically closed fields of the same transcendence degree over `k` are
`k`-isomorphic.  The conjugating automorphism is exactly the datum needed to lift `r` to the
restriction along `k ⟶ k'`.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.extensionMap` is the morphism of schemes over `S` induced by
  a ring homomorphism between fields.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_isIso_source_target_over_isAlgClosed` constructs the
  required lifted arrow after an algebraically closed field extension.

## Implementation notes

The lifted point is represented by a morphism from the spectrum of the extending field.  The
two residue-field conditions are stated using the canonical residue-field maps induced by the
source and target morphisms of the restricted arrow scheme.

## References

* [Stacks Project, Tag 04LR](https://stacks.math.columbia.edu/tag/04LR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

open Cardinal

/-- A transcendence basis of an algebraically closed field which is larger than both its base
and `ℵ₀` has the cardinality of the field. -/
private lemma cardinalMk_eq_of_isTranscendenceBasis_of_large {k K ι : Type u}
    [CommRing k] [Field K] [Algebra k K]
    [IsAlgClosed K] {v : ι → K} (hv : IsTranscendenceBasis k v)
    (h : max #k ℵ₀ < #K) : #ι = #K := by
  have : Nontrivial k := RingHom.domain_nontrivial (algebraMap k K)
  apply le_antisymm (Cardinal.mk_le_of_injective hv.1.injective)
  rcases le_max_iff.mp (IsAlgClosed.cardinal_le_max_transcendence_basis' v hv) with hb | hb
  · exact (le_max_iff.mp hb).resolve_left (not_le_of_gt ((le_max_left _ _).trans_lt h))
  · exact (not_le_of_gt ((le_max_right _ _).trans_lt h) hb).elim

/-- Two algebraically closed extensions of `k` of the same cardinality, large compared with `k`
and `ℵ₀`, are isomorphic over `k`. -/
private lemma nonempty_algEquiv_of_large_cardinal {k K L : Type u}
    [CommRing k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [FaithfulSMul k K] [FaithfulSMul k L] [IsAlgClosed K] [IsAlgClosed L]
    (h : max #k ℵ₀ < #K) (hKL : #K = #L) :
    Nonempty (K ≃ₐ[k] L) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis k L
  have hc : #s = #t := (cardinalMk_eq_of_isTranscendenceBasis_of_large hs h).trans
    (hKL.trans (cardinalMk_eq_of_isTranscendenceBasis_of_large ht (hKL ▸ h)).symm)
  let e : s ≃ t := Classical.choice (Cardinal.eq.mp hc)
  let f : Algebra.adjoin k (Set.range ((↑) : s → K)) ≃ₐ[k]
      Algebra.adjoin k (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv k e).trans ht.1.aevalEquiv)
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let g := IsAlgClosure.equivOfEquiv K L f.toRingEquiv
  refine ⟨{ g with commutes' := fun x => ?_ }⟩
  change IsAlgClosure.equivOfEquiv K L f.toRingEquiv (algebraMap k K x) = algebraMap k L x
  simpa only [AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply] using
    IsAlgClosure.equivOfEquiv_algebraMap K L f.toRingEquiv
      (algebraMap k (Algebra.adjoin k (Set.range ((↑) : s → K))) x)

/-- Every field admits an algebraically closed extension of cardinality larger than any
prescribed cardinal: adjoin that many indeterminates and take an algebraic closure. -/
@[ega "IV 10.10.5"]
private lemma exists_large_algClosed (E : Type u) [Field E] (c : Cardinal.{u}) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : E →+* K), c < #K := by
  let ι := ((2 : Cardinal.{u}) ^ c).out
  let P := MvPolynomial ι E
  let F := FractionRing P
  let K := AlgebraicClosure F
  let j : E →+* K := (algebraMap F K).comp ((algebraMap P F).comp MvPolynomial.C)
  refine ⟨K, inferInstance, inferInstance, j, ?_⟩
  have hi : Function.Injective
      (fun x : ι => algebraMap F K (algebraMap P F (MvPolynomial.X x))) :=
    (algebraMap F K).injective.comp
      ((IsFractionRing.injective P F).comp MvPolynomial.X_injective)
  exact (Cardinal.cantor c).trans_le (by simpa [ι] using Cardinal.mk_le_of_injective hi)

/-- Two embeddings of a field `k` into a field `E` become conjugate in a large enough
algebraically closed extension of `E`. -/
private lemma exists_conjugate_embeddings {k E : Type u} [Field k] [Field E]
    (a b : k →+* E) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (j : E →+* K) (τ : K ≃+* K),
      τ.toRingHom.comp (j.comp a) = j.comp b := by
  obtain ⟨K, _, _, j, hbig⟩ := exists_large_algClosed E (max #k ℵ₀)
  let L := ULift.{0} K
  let e : L ≃+* K := ULift.ringEquiv
  let _ : IsAlgClosed L := IsAlgClosed.of_ringEquiv K L e.symm
  let _ : Algebra k K := (j.comp a).toAlgebra
  let _ : Algebra k L := (e.symm.toRingHom.comp (j.comp b)).toAlgebra
  obtain ⟨f⟩ := nonempty_algEquiv_of_large_cardinal (k := k) (L := L) hbig
    (Cardinal.mk_congr e.toEquiv.symm)
  refine ⟨K, inferInstance, inferInstance, j, f.toRingEquiv.trans e, ?_⟩
  ext x
  exact congrArg e (f.commutes x) |>.trans (e.apply_symm_apply _)

/-- If a composite of two morphisms is an open immersion, then the second factor induces an
isomorphism of residue fields at the image of any point of the source. -/
private lemma isIso_residueFieldMap_of_isIso_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (f : Y ⟶ Z) [IsIso (a ≫ f)] (x : X) :
    IsIso (f.residueFieldMap (a x)) := by
  have hcomp : IsIso (f.residueFieldMap (a x) ≫ a.residueFieldMap x) := by
    rw [← Scheme.residueFieldMap_comp]
    have : IsOpenImmersion (a ≫ f) := inferInstance
    exact Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion (a ≫ f) x
  refine (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(f.residueFieldMap (a x)).hom.injective, fun z => ?_⟩
  obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso
    (f.residueFieldMap (a x) ≫ a.residueFieldMap x)).surjective (a.residueFieldMap x z)
  exact ⟨w, (a.residueFieldMap x).hom.injective hw⟩

/-- If `a ≫ f = w` with `w` an isomorphism, then `f` induces an isomorphism of residue fields at
the image under `a` of any point. -/
private lemma isIso_residueFieldMap_of_comp_eq {X Y Z : Scheme.{u}} {a : X ⟶ Y} {f : Y ⟶ Z}
    {w : X ⟶ Z} (h : a ≫ f = w) [IsIso w] (x : X) :
    IsIso (f.residueFieldMap (a x)) := by
  subst h
  exact isIso_residueFieldMap_of_isIso_comp a f x

/-- An arrow of a groupoid scheme together with lifts of its source and target along `g` is the
same thing as an arrow of the restriction along `g`. -/
private lemma exists_restrictionArrows_lift {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' T : Over S} (g : U' ⟶ G.objects) (p : T ⟶ G.arrows) (a b : T ⟶ U')
    (ha : p ≫ G.source = a ≫ g) (hb : p ≫ G.target = b ≫ g) :
    ∃ q : T ⟶ restrictionArrows G g,
      q ≫ restrictionArrowsToArrows G g = p ∧
      q ≫ restrictionSource G g = a ∧ q ≫ restrictionTarget G g = b := by
  let l := pullback.lift b p hb.symm
  let r := pullback.lift p a ha
  let q : T ⟶ restrictionArrows G g :=
    pullback.lift l r (by simp [l, r])
  refine ⟨q, ?_, ?_, ?_⟩ <;>
    simp [q, l, r, restrictionArrowsToArrows, restrictionSource, restrictionTarget,
      restrictionArrows]

/-- The morphism over `S` between spectra induced contravariantly by a ring homomorphism. -/
public noncomputable def extensionMap {S : Scheme.{u}} {k k' : Type u} [CommRing k] [CommRing k']
    (structureMap : Spec (.of k) ⟶ S) (i : k →+* k') :
    Over.mk (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap) ⟶ Over.mk structureMap :=
  Over.homMk (Scheme.Spec.map (CommRingCat.ofHom i).op) rfl

/-- A point `p` of the arrow scheme over `Spec K`, whose source is the extension `d` and whose
target is `d` precomposed with `z`, lifts to the restriction along the extension. -/
private lemma exists_restrictionArrows_lift_of_point {S : Scheme.{u}} {k K : Type u}
    [CommRing k] [CommRing K] (structureMap : Spec (.of k) ⟶ S) (G : GroupoidScheme S)
    (objects_eq : G.objects = Over.mk structureMap) (i : k →+* K)
    (p : Spec (.of K) ⟶ G.arrows.left) (z : Spec (.of K) ⟶ Spec (.of K))
    (hps : p ≫ (G.source ≫ eqToHom objects_eq).left = Scheme.Spec.map (CommRingCat.ofHom i).op)
    (hpt : p ≫ (G.target ≫ eqToHom objects_eq).left =
      z ≫ Scheme.Spec.map (CommRingCat.ofHom i).op) :
    ∃ q : Over.mk (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap) ⟶
        restrictionArrows G (extensionMap structureMap i ≫ eqToHom objects_eq.symm),
      q.left ≫ (restrictionArrowsToArrows G
          (extensionMap structureMap i ≫ eqToHom objects_eq.symm)).left = p ∧
        q.left ≫ (restrictionSource G
          (extensionMap structureMap i ≫ eqToHom objects_eq.symm)).left = 𝟙 _ ∧
        q.left ≫ (restrictionTarget G
          (extensionMap structureMap i ≫ eqToHom objects_eq.symm)).left = z := by
  let d := Scheme.Spec.map (CommRingCat.ofHom i).op
  have htS : (G.target ≫ eqToHom objects_eq).left ≫ structureMap = G.arrows.hom :=
    Over.w (G.target ≫ eqToHom objects_eq)
  have hsS : (G.source ≫ eqToHom objects_eq).left ≫ structureMap = G.arrows.hom :=
    Over.w (G.source ≫ eqToHom objects_eq)
  have hpS : p ≫ G.arrows.hom = d ≫ structureMap := by rw [← hsS, ← Category.assoc, hps]
  let T : Over S := Over.mk (d ≫ structureMap)
  let g : T ⟶ G.objects := extensionMap structureMap i ≫ eqToHom objects_eq.symm
  let pp : T ⟶ G.arrows := Over.homMk p hpS
  let zz : T ⟶ T := Over.homMk z (by
    change z ≫ (d ≫ structureMap) = d ≫ structureMap
    rw [← Category.assoc, ← hpt, Category.assoc, htS, hpS])
  have hpps : pp ≫ G.source = (𝟙 T) ≫ g := by
    apply (cancel_mono (eqToHom objects_eq)).mp
    apply Over.OverMorphism.ext
    simpa [pp, g, extensionMap, d, Category.assoc] using hps
  have hppt : pp ≫ G.target = zz ≫ g := by
    apply (cancel_mono (eqToHom objects_eq)).mp
    apply Over.OverMorphism.ext
    simpa [pp, zz, g, extensionMap, d, Category.assoc] using hpt
  obtain ⟨q, hq, hqs, hqt⟩ := exists_restrictionArrows_lift G g pp (𝟙 T) zz hpps hppt
  exact ⟨q, congrArg (·.left) hq, congrArg (·.left) hqs, congrArg (·.left) hqt⟩

/-- An arrow over a point of a groupoid scheme on `Spec k` can be lifted after an algebraically
closed extension of `k` so that both its source and target induce isomorphisms from the
extending field to the residue field of the lifted point. -/
@[stacks 04LR]
public theorem exists_isIso_source_target_over_isAlgClosed {S : Scheme.{u}} {k : Type u}
    [Field k] (structureMap : Spec (.of k) ⟶ S) (G : GroupoidScheme S)
    (objects_eq : G.objects = Over.mk structureMap) (r : G.arrows.left) :
    ∃ (k' : Type u) (_ : Field k') (_ : IsAlgClosed k') (i : k →+* k'),
      let g : Over.mk (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap) ⟶ G.objects :=
        extensionMap structureMap i ≫ eqToHom objects_eq.symm
      ∃ (r' : Spec (.of k') ⟶ (restrictionArrows G g).left),
      let rPoint := r' (IsLocalRing.closedPoint k')
      (restrictionArrowsToArrows G g).left rPoint = r ∧
        IsIso ((restrictionSource G g).left.residueFieldMap rPoint) ∧
        IsIso ((restrictionTarget G g).left.residueFieldMap rPoint) := by
  classical
  let E := G.arrows.left.residueField r
  let p₀ : Spec E ⟶ G.arrows.left := G.arrows.left.fromSpecResidueField r
  let s₀ : G.arrows.left ⟶ Spec (.of k) := (G.source ≫ eqToHom objects_eq).left
  let t₀ : G.arrows.left ⟶ Spec (.of k) := (G.target ≫ eqToHom objects_eq).left
  let a : k →+* E := (Scheme.Spec.preimage (p₀ ≫ s₀)).unop.hom
  let b : k →+* E := (Scheme.Spec.preimage (p₀ ≫ t₀)).unop.hom
  have ha : Scheme.Spec.map (CommRingCat.ofHom a).op = p₀ ≫ s₀ :=
    Scheme.Spec.map_preimage _
  have hb : Scheme.Spec.map (CommRingCat.ofHom b).op = p₀ ≫ t₀ :=
    Scheme.Spec.map_preimage _
  obtain ⟨K, _, _, j, τ, hτ⟩ := exists_conjugate_embeddings a b
  let i := j.comp a
  let d : Spec (.of K) ⟶ Spec (.of k) := Scheme.Spec.map (CommRingCat.ofHom i).op
  let p : Spec (.of K) ⟶ G.arrows.left := Scheme.Spec.map (CommRingCat.ofHom j).op ≫ p₀
  let z : Spec (.of K) ⟶ Spec (.of K) := Scheme.Spec.map (CommRingCat.ofHom τ.toRingHom).op
  have hps : p ≫ s₀ = d := by
    rw [show p ≫ s₀ = Scheme.Spec.map (CommRingCat.ofHom j).op ≫ (p₀ ≫ s₀) from
      Category.assoc _ _ _, ← ha]
    exact (Scheme.Spec.map_comp _ _).symm
  have hpt : p ≫ t₀ = z ≫ d := by
    rw [show p ≫ t₀ = Scheme.Spec.map (CommRingCat.ofHom j).op ≫ (p₀ ≫ t₀) from
      Category.assoc _ _ _, ← hb]
    change Scheme.Spec.map (CommRingCat.ofHom j).op ≫
        Scheme.Spec.map (CommRingCat.ofHom b).op =
      Scheme.Spec.map (CommRingCat.ofHom τ.toRingHom).op ≫
        Scheme.Spec.map (CommRingCat.ofHom i).op
    rw [← Scheme.Spec.map_comp, ← Scheme.Spec.map_comp]
    exact congrArg (fun f : k →+* K => Scheme.Spec.map (CommRingCat.ofHom f).op) hτ.symm
  have hz : IsIso z := by
    change IsIso (Scheme.Spec.map (CommRingCat.ofHom τ.toRingHom).op)
    have : IsIso (CommRingCat.ofHom τ.toRingHom) := τ.toCommRingCatIso.isIso_hom
    infer_instance
  obtain ⟨q, hq, hqs, hqt⟩ :=
    exists_restrictionArrows_lift_of_point structureMap G objects_eq i p z hps hpt
  refine ⟨K, inferInstance, inferInstance, i, q.left, ?_, ?_, ?_⟩
  · exact (congrArg (fun f : Spec (.of K) ⟶ G.arrows.left => f (IsLocalRing.closedPoint K))
      hq).trans (Scheme.fromSpecResidueField_apply r _)
  · exact isIso_residueFieldMap_of_comp_eq hqs _
  · exact isIso_residueFieldMap_of_comp_eq hqt _

end AlgebraicGeometry.GroupoidScheme
