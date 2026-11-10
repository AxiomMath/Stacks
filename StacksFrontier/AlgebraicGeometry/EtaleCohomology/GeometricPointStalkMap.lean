module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of geometric points, and the induced isomorphism of étale stalks

A *morphism of geometric points* `s ⟶ t` of a scheme `S` is a morphism of their sources over
`S`.  Such a morphism carries a lift of `t` to an étale scheme over `S` to a lift of `s`, by
precomposition, and that is an equivalence of the two categories of étale neighbourhoods: the
essential point is that a geometric point of an étale scheme over `S` descends along a
morphism of algebraically closed fields, which holds because the residue field extension cut
out by an étale morphism is separably algebraic and therefore embeds into any algebraically
closed field receiving the base.  Consequently the canonical map `s_t ⟶ s_s` of stalk
functors, given by `colimit.pre` along the induced functor of neighbourhood categories, is an
isomorphism: the étale stalk does not depend on the choice of geometric point above a point
of `S`.

The same morphism also induces an isomorphism of the associated points of Mathlib's
unrestricted small étale site.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.Hom` — a morphism of geometric points of a scheme.
* `AlgebraicGeometry.geometricPointFiberMap` — the induced map of geometric fibres, sending a
  lift of `t` to its composite with the morphism.
* `AlgebraicGeometry.neighborhoodFunctor` — the induced functor of étale-neighbourhood
  categories.
* `AlgebraicGeometry.geometricPointStalkMap` — the canonical map of étale stalk functors, from
  the stalk at `t` to the stalk at `s`.
* `AlgebraicGeometry.smallEtalePointHom` — the induced morphism of points of Mathlib's small
  étale site.

## Main results

* `AlgebraicGeometry.geometricPointFiberMap_isIso` — the map of geometric fibres is a natural
  isomorphism.
* `AlgebraicGeometry.neighborhoodFunctor_isEquivalence` — restriction along a morphism of
  geometric points is an equivalence of étale-neighbourhood categories.
* `AlgebraicGeometry.geometricPointStalkMap_germ` — the canonical map sends the germ of a
  section at a lift of `t` to its germ at the composite lift of `s`.
* `AlgebraicGeometry.geometricPointStalkMap_isIso` — the canonical map is a natural
  isomorphism of stalk functors.
* `AlgebraicGeometry.smallEtalePointHom_isIso` — the induced morphism of site points is an
  isomorphism.

## Implementation notes

The map of stalks is `CategoryTheory.Limits.colimit.pre` along the opposite of the
neighbourhood functor, which fixes its direction and makes its naturality in the presheaf
automatic.  Invertibility is then finality of that functor, which follows from its being an
equivalence.  The stalk functor itself is
`AlgebraicGeometry.etaleStalkPresheafFunctor`, so nothing about the stalk is redefined here.

The morphism of points of the unrestricted small étale site is represented by the map of
geometric fibres, in the reverse direction on fibre functors, following the convention of the
source.

## References

* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

private theorem algHom_factor_through_algClosed
    {F E L A : Type u} [Field F] [Field E] [Field L] [Field A]
    [Algebra F E] [Algebra.IsAlgebraic F E] [Algebra F L] [Algebra F A]
    [Algebra L A]
    [IsScalarTower F L A] [IsAlgClosed L] (φ : E →ₐ[F] A) :
    ∃ ψ : E →ₐ[F] L, ∀ x, algebraMap L A (ψ x) = φ x := by
  let h : ∀ x : E, (Polynomial.map (algebraMap F L) (minpoly F x)).Splits :=
    fun x => IsAlgClosed.splits _
  let e := Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits
    (F := F) (K := E) (A := A) (L := L) h
  refine ⟨e.symm φ, fun x => ?_⟩
  calc
    algebraMap L A ((e.symm φ) x) = (e (e.symm φ)) x :=
      (Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply (A := A) (L := L) h
        (e.symm φ) x).symm
    _ = φ x := congrArg (fun f : E →ₐ[F] A => f x) (e.apply_symm_apply φ)

private noncomputable def specResidueFieldRingEquiv (K : Type u) [Field K] :
    K ≃+* (Spec (.of K)).residueField default := by
  let c : Spec (.of K) := IsLocalRing.closedPoint K
  let : c.asIdeal.IsPrime := c.isPrime
  let hcd : c = (default : Spec (.of K)) := Subsingleton.elim _ _
  exact c.asIdeal.algEquivResidueFieldOfField.toRingEquiv.trans
    ((Scheme.Spec.residueFieldIso (.of K) c).commRingCatIsoToRingEquiv.symm.trans
      (Scheme.residueFieldCongr hcd).commRingCatIsoToRingEquiv)

/-- A morphism of spectra of fields can be cancelled on the left. -/
private theorem specFieldHom_cancel {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}}
    (a : Spec (.of k) ⟶ Spec (.of k')) {p q : Spec (.of k') ⟶ X} (h : a ≫ p = a ≫ q) :
    p = q :=
  have : Epi a := AlgebraicGeometry.Flat.epi_of_flat_of_surjective a
  (cancel_epi a).1 h

private theorem descResidueField_stalkClosedPointTo_residueFieldMap
    {Y : Scheme.{u}} {K : Type u} [Field K]
    (g : Spec (.of K) ⟶ Y) :
    Scheme.descResidueField (Scheme.stalkClosedPointTo g) ≫
        CommRingCat.ofHom (specResidueFieldRingEquiv K).toRingHom =
      (Y.residueFieldCongr (by
        have h : IsLocalRing.closedPoint K = (default : Spec (.of K)) :=
          Subsingleton.elim _ _
        exact congrArg g h)).hom ≫ g.residueFieldMap default := by
  let c : Spec (.of K) :=
    IsLocalRing.closedPoint K
  let I : Ideal K := c.asIdeal
  have hc : c = (default : Spec (.of K)) := Subsingleton.elim _ _
  have hid : (stalkClosedPointIso (.of K)).hom ≫
      CommRingCat.ofHom (specResidueFieldRingEquiv K).toRingHom =
      (Spec (.of K)).residue c ≫ ((Spec (.of K)).residueFieldCongr hc).hom := by
    let : c.asIdeal.IsPrime := c.isPrime
    have he : CommRingCat.ofHom (specResidueFieldRingEquiv K).toRingHom =
        CommRingCat.ofHom (algebraMap K c.asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of K) c).inv ≫
            (Scheme.residueFieldCongr hc).hom := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change (Scheme.residueFieldCongr hc).hom
          ((Scheme.Spec.residueFieldIso (.of K) c).inv
            (c.asIdeal.algEquivResidueFieldOfField x)) = _
      rfl
    have hbare : (stalkClosedPointIso (.of K)).hom ≫
        CommRingCat.ofHom (algebraMap K (IsLocalRing.closedPoint K).asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of K) (IsLocalRing.closedPoint K)).inv =
      (Spec (.of K)).residue (IsLocalRing.closedPoint K) := by
      apply (cancel_mono
        (Scheme.Spec.residueFieldIso (.of K) (IsLocalRing.closedPoint K)).hom).1
      dsimp only [stalkClosedPointIso, Iso.trans_hom]
      rw [Scheme.Spec.residue_residueFieldIso_hom
        (R := .of K) (x := IsLocalRing.closedPoint K)]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply (cancel_epi
        (Spec.stalkIso (.of K) (IsLocalRing.closedPoint K)).hom).mpr
      apply CommRingCat.hom_ext
      apply IsLocalization.ringHom_ext (IsLocalRing.closedPoint K).asIdeal.primeCompl
      apply RingHom.ext
      intro x
      simp only [Iso.symm_hom, RingEquiv.toCommRingCatIso_inv, RingEquiv.symm_mk,
        AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm, CommRingCat.hom_comp,
        ConcreteCategory.hom_ofHom, RingHom.coe_comp, RingHom.coe_coe, RingEquiv.coe_mk,
        EquivLike.coe_coe, Function.comp_apply, AlgEquiv.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, IsLocalRing.ResidueField.algebraMap_eq]
      rw [IsScalarTower.algebraMap_apply K
        (Localization.AtPrime (IsLocalRing.closedPoint K).asIdeal)
        (IsLocalRing.closedPoint K).asIdeal.ResidueField x,
        IsLocalRing.ResidueField.algebraMap_eq]
    rw [he]
    exact congrArg (fun h => h ≫ (Scheme.residueFieldCongr hc).hom) hbare
  have hclosed : Scheme.stalkClosedPointTo g =
      g.stalkMap c ≫ (stalkClosedPointIso (.of K)).hom := rfl
  apply (cancel_epi (Y.residue (g c))).1
  rw [← Category.assoc, Scheme.residue_descResidueField]
  rw [hclosed, Category.assoc, hid]
  calc
    _ = Y.residue (g c) ≫ g.residueFieldMap c ≫
        ((Spec (.of K)).residueFieldCongr hc).hom := by
      have hnat := Scheme.residue_residueFieldMap (f := g) c
      simpa only [Category.assoc] using
        congrArg (fun m => m ≫ ((Spec (.of K)).residueFieldCongr hc).hom) hnat.symm
    _ = Y.residue (g c) ≫ (Y.residueFieldCongr (congrArg g hc)).hom ≫
        g.residueFieldMap default := by
      rw [Scheme.Hom.residueFieldMap_congr']

private theorem factor_residueFieldMap
    {X S : Scheme.{u}} {k k' : Type u} [Field k] [Field k']
    [IsAlgClosed k'] (f : X ⟶ S) [Etale f]
    (a : Spec (.of k) ⟶ Spec (.of k')) (t : Spec (.of k') ⟶ S)
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = a ≫ t) :
    ∃ ψ : X.residueField (p default) →+* (Spec (.of k')).residueField default,
      ψ.comp (f.residueFieldMap (p default)).hom =
        (((S.residueFieldCongr
          (congrArg (fun g : Spec (.of k) ⟶ S => g default) hp)).hom ≫
          t.residueFieldMap (a default) ≫
          ((Spec (.of k')).residueFieldCongr
            (Subsingleton.elim (a default) default)).hom).hom) ∧
      (((Spec (.of k')).residueFieldCongr
        (Subsingleton.elim (a default) default)).inv ≫
        a.residueFieldMap default).hom.comp ψ = (p.residueFieldMap default).hom := by
  have hpt : (p ≫ f) default = (a ≫ t) default :=
    congrArg (fun g : Spec (.of k) ⟶ S => g default) hp
  have ha : a default = (default : Spec (.of k')) := Subsingleton.elim _ _
  let e := (Spec (.of k')).residueFieldCongr ha
  let βcat := (S.residueFieldCongr hpt).hom ≫ t.residueFieldMap (a default)
  let β := βcat.hom
  let γ := (a.residueFieldMap default).hom
  let α := (p.residueFieldMap default).hom
  let m := (f.residueFieldMap (p default)).hom
  let F := S.residueField (f (p default))
  let E := X.residueField (p default)
  let L := (Spec (.of k')).residueField (a default)
  let A := (Spec (.of k)).residueField default
  let : Algebra F E := (f.residueFieldMap (p default)).hom.toAlgebra
  let : Algebra.IsSeparable F E := by infer_instance
  let : Algebra F L := β.toAlgebra
  let : Algebra L A := γ.toAlgebra
  let : Algebra F A := (γ.comp β).toAlgebra
  let : IsScalarTower F L A := IsScalarTower.of_algebraMap_eq' rfl
  let : IsAlgClosed L :=
    IsAlgClosed.of_ringEquiv k' L
      ((specResidueFieldRingEquiv k').trans e.symm.commRingCatIsoToRingEquiv)
  let : Algebra.IsAlgebraic F E := inferInstance
  have hcomp : α.comp m = γ.comp β := by
    have hcat := Scheme.Hom.residueFieldMap_congr hp (default : Spec (.of k))
    have hcompMap := Scheme.residueFieldMap_comp (f := a) t default
    have hcat' : (p ≫ f).residueFieldMap default =
        (S.residueFieldCongr hpt).hom ≫
          (t.residueFieldMap (a default) ≫ a.residueFieldMap default) :=
      hcat.trans (congrArg (fun q => (S.residueFieldCongr hpt).hom ≫ q) hcompMap)
    rw [Scheme.residueFieldMap_comp] at hcat'
    exact congrArg CommRingCat.Hom.hom hcat'
  let φ : E →ₐ[F] A := {
    toRingHom := α
    commutes' := fun r => by
      change α (algebraMap F E r) = algebraMap F A r
      change α (m r) = (γ.comp β) r
      exact congrArg (fun g : F →+* A => g r) hcomp }
  obtain ⟨ψ₀, hψ₀⟩ := algHom_factor_through_algClosed
    (F := F) (E := E) (L := L) (A := A) φ
  let ψ : E →+* (Spec (.of k')).residueField default := e.hom.hom.comp ψ₀.toRingHom
  refine ⟨ψ, ?_, ?_⟩
  · exact RingHom.ext fun r => by
      change e.hom.hom (ψ₀ (algebraMap F E r)) = _
      rw [ψ₀.commutes]
      rfl
  · apply RingHom.ext
    intro r
    change a.residueFieldMap default (e.inv.hom (e.hom.hom (ψ₀ r))) = α r
    have heval : e.inv.hom (e.hom.hom (ψ₀ r)) = ψ₀ r := by
      simp
    rw [heval]
    exact hψ₀ r


private theorem factor_etale_point
    {X S : Scheme.{u}} {k k' : Type u} [Field k] [Field k']
    [IsAlgClosed k'] (f : X ⟶ S) [Etale f]
    (a : Spec (.of k) ⟶ Spec (.of k')) (t : Spec (.of k') ⟶ S)
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = a ≫ t) :
    ∃ q : Spec (.of k') ⟶ X, a ≫ q = p ∧ q ≫ f = t := by
  obtain ⟨ψ, _, hψa⟩ := factor_residueFieldMap f a t p hp
  have ha : a default = (default : Spec (.of k')) := Subsingleton.elim _ _
  let e := specResidueFieldRingEquiv k'
  let ψ' : X.residueField (p default) →+* k' := e.symm.toRingHom.comp ψ
  let : CommRing (X.residueField (p default)) := inferInstance
  let : CommRing k' := inferInstance
  let : NonAssocSemiring (X.residueField (p default)) :=
    (inferInstance : CommRing (X.residueField (p default))).toCommSemiring.toNonAssocSemiring
  let : NonAssocSemiring k' :=
    (inferInstance : CommRing k').toCommSemiring.toNonAssocSemiring
  let ψcat : X.residueField (p default) →+* k' := {
    toFun := ψ'
    map_one' := by simp
    map_mul' := by simp
    map_zero' := by simp
    map_add' := by simp }
  let ψobj : X.residueField (p default) ⟶ CommRingCat.of k' :=
    @CommRingCat.ofHom (X.residueField (p default)) k' inferInstance inferInstance ψcat
  let q : Spec (.of k') ⟶ X :=
    (Scheme.SpecToEquivOfField k' X).symm
      ⟨p default, ψobj⟩
  have hq := (Scheme.SpecToEquivOfField k' X).apply_symm_apply
    ⟨p default, ψobj⟩
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hq
  obtain ⟨hqpt', hqdesc⟩ := Scheme.SpecToEquivOfField_eq_iff.mp hq
  dsimp only at hqpt'
  let c : Spec (.of k) :=
    ⟨(IsLocalRing.closedPoint k).asIdeal, (IsLocalRing.closedPoint k).isPrime⟩
  let c' : Spec (.of k') :=
    ⟨(IsLocalRing.closedPoint k').asIdeal, (IsLocalRing.closedPoint k').isPrime⟩
  have hpc : p default = p c := by
    have hc : (default : Spec (.of k)) = c := Subsingleton.elim _ _
    exact congrArg p hc
  have hqpoint : q c' = p default := by
    change q (IsLocalRing.closedPoint k') = p default
    exact congrArg Sigma.fst hq
  have hqdesc' : Scheme.descResidueField (Scheme.stalkClosedPointTo q) =
      (X.residueFieldCongr hqpoint).hom ≫ ψobj :=
    hqdesc
  have hψe : ψobj ≫ CommRingCat.ofHom e.toRingHom = CommRingCat.ofHom ψ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change e.toRingHom (e.symm.toRingHom (ψ x)) = ψ x
    simp
  let hqa : q c' = q default := congrArg q (Subsingleton.elim _ _)
  let hqd : q default = p default := hqa.symm.trans hqpoint
  have hqres : q.residueFieldMap default =
      (X.residueFieldCongr hqd).hom ≫ ψobj ≫ CommRingCat.ofHom e.toRingHom := by
    have hh := descResidueField_stalkClosedPointTo_residueFieldMap q
    rw [hqdesc', Category.assoc] at hh
    have hcong : (X.residueFieldCongr hqpoint).hom =
        (X.residueFieldCongr hqa).hom ≫ (X.residueFieldCongr hqd).hom :=
      (Scheme.residueFieldCongr_trans_hom X hqa hqd).symm
    have hh' :
        (X.residueFieldCongr hqa).hom ≫ q.residueFieldMap default =
          (X.residueFieldCongr hqa).hom ≫
            ((X.residueFieldCongr hqd).hom ≫ ψobj ≫ CommRingCat.ofHom e.toRingHom) := by
      calc
        (X.residueFieldCongr hqa).hom ≫ q.residueFieldMap default =
            (X.residueFieldCongr hqpoint).hom ≫ ψobj ≫
              CommRingCat.ofHom e.toRingHom := hh.symm
        _ = (X.residueFieldCongr hqa).hom ≫
            ((X.residueFieldCongr hqd).hom ≫ ψobj ≫ CommRingCat.ofHom e.toRingHom) := by
          rw [hcong]
          simp
    exact (cancel_epi (X.residueFieldCongr hqa).hom).mp hh'
  have hbase : q (a c) = p c := by
    rw [show a c = c' from Subsingleton.elim _ _]
    exact hqpoint.trans hpc
  have hcompat : a ≫ q = p := by
    apply (Scheme.SpecToEquivOfField k X).injective
    apply Scheme.SpecToEquivOfField_eq_iff.mpr
    refine ⟨?_, ?_⟩
    · exact hbase
    · dsimp only [Scheme.SpecToEquivOfField]
      have hfactor := Scheme.descResidueField_stalkClosedPointTo_comp (f := q) (g := a)
      change Scheme.descResidueField (Scheme.stalkClosedPointTo (a ≫ q)) =
        (X.residueFieldCongr _).hom ≫ Scheme.descResidueField (Scheme.stalkClosedPointTo p)
      refine hfactor.trans ?_
      let : Mono (CommRingCat.ofHom (specResidueFieldRingEquiv k).toRingHom) :=
        ConcreteCategory.mono_of_injective _ (specResidueFieldRingEquiv k).injective
      apply (cancel_mono (CommRingCat.ofHom (specResidueFieldRingEquiv k).toRingHom)).1
      have haBridge := descResidueField_stalkClosedPointTo_residueFieldMap
        (Y := Spec (.of k')) (K := k) a
      have hpBridge := descResidueField_stalkClosedPointTo_residueFieldMap
        (Y := X) (K := k) p
      have hclosed : IsLocalRing.closedPoint k = (default : Spec (.of k)) :=
        Subsingleton.elim _ _
      have hqa : a (IsLocalRing.closedPoint k) = a default := congrArg a hclosed
      have haBridge' :
          Scheme.descResidueField (Scheme.stalkClosedPointTo a) ≫
              CommRingCat.ofHom (specResidueFieldRingEquiv k).toRingHom =
            ((Spec (.of k')).residueFieldCongr hqa).hom ≫
              a.residueFieldMap default := by
        simpa only using haBridge
      let : IsLocalHom (Scheme.stalkClosedPointTo a).hom :=
        Scheme.isLocalHom_stalkClosedPointTo' a
      let : IsLocalHom (Scheme.stalkClosedPointTo p).hom :=
        Scheme.isLocalHom_stalkClosedPointTo' p
      change q.residueFieldMap (a c) ≫
          Scheme.descResidueField (Scheme.stalkClosedPointTo a) ≫
            CommRingCat.ofHom (specResidueFieldRingEquiv k).toRingHom =
        ((X.residueFieldCongr hbase).hom ≫
          Scheme.descResidueField (Scheme.stalkClosedPointTo p)) ≫
            CommRingCat.ofHom (specResidueFieldRingEquiv k).toRingHom
      conv_lhs => rw [haBridge']
      conv_rhs => rw [Category.assoc, hpBridge]
      have hqMapAt := q.residueFieldMap_congr' hqa
      have hqMapDefault := q.residueFieldMap_congr' ha
      have hψaCat :
          (ψobj ≫ CommRingCat.ofHom e.toRingHom) ≫
              (((Spec (.of k')).residueFieldCongr
                (Subsingleton.elim (a default) (default : Spec (.of k')))).inv ≫
                a.residueFieldMap default) = p.residueFieldMap default := by
        rw [hψe]
        exact CommRingCat.hom_ext hψa
      change q.residueFieldMap (a (IsLocalRing.closedPoint k)) ≫
          ((Spec (.of k')).residueFieldCongr hqa).hom ≫ a.residueFieldMap default =
        (X.residueFieldCongr _).hom ≫ (X.residueFieldCongr _).hom ≫
          p.residueFieldMap default
      have hleft :
          q.residueFieldMap (a (IsLocalRing.closedPoint k)) ≫
              ((Spec (.of k')).residueFieldCongr hqa).hom ≫
                a.residueFieldMap default =
            (X.residueFieldCongr (congrArg q hqa)).hom ≫
              q.residueFieldMap (a default) ≫ a.residueFieldMap default := by
        simpa only [Category.assoc] using congrArg
          (fun m => m ≫ a.residueFieldMap default) hqMapAt
      have hMiddle :
          q.residueFieldMap (a default) ≫ a.residueFieldMap default =
            (X.residueFieldCongr (congrArg q ha)).hom ≫
              (X.residueFieldCongr hqd).hom ≫ p.residueFieldMap default := by
        calc
          _ = q.residueFieldMap (a default) ≫
              ((Spec (.of k')).residueFieldCongr ha).hom ≫
                ((Spec (.of k')).residueFieldCongr ha).inv ≫
                  a.residueFieldMap default := by simp
          _ = (X.residueFieldCongr (congrArg q ha)).hom ≫
              q.residueFieldMap default ≫
                ((Spec (.of k')).residueFieldCongr ha).inv ≫
                  a.residueFieldMap default := by
            simpa only [Category.assoc] using congrArg
              (fun m => m ≫ ((Spec (.of k')).residueFieldCongr ha).inv ≫
                a.residueFieldMap default) hqMapDefault
          _ = (X.residueFieldCongr (congrArg q ha)).hom ≫
              (X.residueFieldCongr hqd).hom ≫
                (ψobj ≫ CommRingCat.ofHom e.toRingHom) ≫
                  ((Spec (.of k')).residueFieldCongr ha).inv ≫
                    a.residueFieldMap default := by
            rw [hqres]
            simp [Category.assoc]
          _ = (X.residueFieldCongr (congrArg q ha)).hom ≫
              (X.residueFieldCongr hqd).hom ≫ p.residueFieldMap default := by
            rw [hψaCat]
      calc
        _ = (X.residueFieldCongr (congrArg q hqa)).hom ≫
              q.residueFieldMap (a default) ≫ a.residueFieldMap default := hleft
        _ = (X.residueFieldCongr (congrArg q hqa)).hom ≫
              (X.residueFieldCongr (congrArg q ha)).hom ≫
                (X.residueFieldCongr hqd).hom ≫ p.residueFieldMap default := by
          simpa only [Category.assoc] using congrArg
            (fun m => (X.residueFieldCongr (congrArg q hqa)).hom ≫ m) hMiddle
        _ = _ := by simp
  refine ⟨q, hcompat, ?_⟩
  apply specFieldHom_cancel a
  calc
    a ≫ (q ≫ f) = (a ≫ q) ≫ f := (Category.assoc _ _ _).symm
    _ = p ≫ f := congrArg (fun g => g ≫ f) hcompat
    _ = a ≫ t := hp


namespace GeometricPoint

/-- A morphism of geometric points over the same scheme. -/
@[stacks 04FN "morphism of geometric points"]
public structure Hom {S : Scheme.{u}}
    (s t : GeometricPoint S) where
  hom : s.source ⟶ t.source
  comm : hom ≫ t.hom = s.hom

end GeometricPoint

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {s t : GeometricPoint S} (a : GeometricPoint.Hom s t)

/-- A lift of `t` to an étale scheme yields a lift of `s` by precomposition. -/
@[stacks 04FN "map of geometric fibers"]
public def geometricPointFiberMap (a : GeometricPoint.Hom s t) :
    geometricPointFiber B S hS t ⟶
      geometricPointFiber B S hS s where
  app U := ↾ (fun p => ⟨a.hom ≫ p.1, by
    rw [Category.assoc, p.2]
    exact a.comm⟩)
  naturality := by
    intro U V f
    ext p
    rfl

/-- The contravariant map on geometric fibers of the size-bounded site is a
natural isomorphism. -/
private theorem categoryOfElements_map_isEquivalence
    {C : Type v} [Category.{w} C] {F G : C ⥤ Type u}
    (α : F ⟶ G) (hα : IsIso α) : (NatTrans.mapElements α).IsEquivalence := by
  let E := NatTrans.mapElements α
  have hbij (X : C) : Function.Bijective (α.app X) :=
    (isIso_iff_bijective _).mp ((NatTrans.isIso_iff_isIso_app α).mp hα X)
  refine {
    faithful := {
      map_injective := by
        intro X Y f g h
        ext
        have h' := congrArg Functor.Elements.Hom.hom h
        exact h'
    }
    full := {
      map_surjective := by
        intro X Y g
        refine ⟨Functor.Elements.homMk g.hom ?_, ?_⟩
        · apply (hbij Y.obj).1
          exact (α.naturality_apply g.hom X.val).trans g.map_val
        · ext
          rfl
    }
    essSurj := {
      mem_essImage := by
        intro Y
        obtain ⟨x, hx⟩ := (hbij Y.obj).2 Y.val
        let X : F.Elements := F.elementsMk Y.obj x
        refine ⟨X, ⟨Functor.Elements.isoMk (x := E.obj X) (y := Y) (Iso.refl Y.obj) ?_⟩⟩
        change G.map (𝟙 Y.obj) (α.app Y.obj x) = Y.val
        simpa using hx
    }
  }

/-- For a morphism `a : s ⟶ t` of geometric points of `S`, the map of geometric fibres
`geometricPointFiberMap B S hS a`, given by precomposition with `a`, is an isomorphism. -/
@[stacks 04FN "isomorphism of site points"]
public theorem geometricPointFiberMap_isIso :
    IsIso (geometricPointFiberMap B S hS a) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [isIso_iff_bijective]
  constructor
  · intro p q hpq
    exact Subtype.ext (specFieldHom_cancel a.hom (congrArg Subtype.val hpq))
  · intro p
    obtain ⟨q, hqa, hqf⟩ := factor_etale_point (B.inclusion.map U.obj.hom) a.hom t.hom p.1
      (p.2.trans a.comm.symm)
    exact ⟨⟨q, hqf⟩, Subtype.ext hqa⟩

/-- Restriction of an étale neighborhood of `t` along `a`. -/
@[stacks 04FN "functor on neighborhoods"]
public def neighborhoodFunctor (a : GeometricPoint.Hom s t) :
    (geometricPointFiber B S hS t).Elements ⥤
      (geometricPointFiber B S hS s).Elements :=
  NatTrans.mapElements (geometricPointFiberMap B S hS a)

/-- Restriction along `a` is an equivalence of étale-neighborhood categories. -/
@[stacks 04FN "equivalence of neighborhoods"]
public theorem neighborhoodFunctor_isEquivalence :
    (neighborhoodFunctor B S hS a).IsEquivalence := by
  change (NatTrans.mapElements (geometricPointFiberMap B S hS a)).IsEquivalence
  exact @categoryOfElements_map_isEquivalence
    (SmallEtale B S hS) inferInstance
    (geometricPointFiber B S hS t)
    (geometricPointFiber B S hS s)
    (geometricPointFiberMap B S hS a)
    (geometricPointFiberMap_isIso B S hS a)

/-- The canonical map from the stalk at `t` to the stalk at `s`, natural in
the presheaf. -/
@[stacks 04FN "canonical map of stalk functors"]
public def geometricPointStalkMap (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (geometricPointFiber B S hS t).Elementsᵒᵖ A]
    [HasColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ A] :
    etaleStalkPresheafFunctor B S hS t A ⟶
      etaleStalkPresheafFunctor B S hS s A where
  app F := colimit.pre
    ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ F)
    (neighborhoodFunctor B S hS a).op
  naturality := by
    intro F G α
    exact (colimit.pre_map
      (Functor.whiskerLeft
        (Functor.Elements.π (geometricPointFiber B S hS s)).op α)
      (neighborhoodFunctor B S hS a).op).symm

/-- The canonical map takes the germ of `(U, u', σ)` to the germ of
`(U, u' ∘ a, σ)`. -/
@[stacks 04FN "action on represented sections",
  stacks 04JK "the displayed rule: the germ of (U, u, t) goes to that of (U, u ∘ Spec σ, t)"]
public theorem geometricPointStalkMap_germ
    (F : (SmallEtale B S hS)ᵒᵖ ⥤ Type u)
    (U : (geometricPointFiber B S hS t).Elementsᵒᵖ)
    (σ : F.obj (Opposite.op U.unop.1)) :
    (geometricPointStalkMap B S hS a (Type u)).app F
        ((colimit.ι
          ((Functor.Elements.π (geometricPointFiber B S hS t)).op ⋙ F) U) σ) =
      (colimit.ι
        ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ F)
        ((neighborhoodFunctor B S hS a).op.obj U)) σ := by
  let G := (Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ F
  let E := (neighborhoodFunctor B S hS a).op
  exact congrArg (fun f : G.obj (E.obj U) ⟶ colimit G => f σ)
    (colimit.ι_pre G E U)

/-- A morphism of geometric points induces a canonical natural isomorphism
of étale stalk functors. -/
@[stacks 04FN "isomorphism of stalk functors"]
public theorem geometricPointStalkMap_isIso (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (geometricPointFiber B S hS t).Elementsᵒᵖ A]
    [HasColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ A] :
    IsIso (geometricPointStalkMap B S hS a A) := by
  let : (neighborhoodFunctor B S hS a).IsEquivalence :=
    neighborhoodFunctor_isEquivalence B S hS a
  let : Functor.IsEquivalence (neighborhoodFunctor B S hS a).op := inferInstance
  let : (neighborhoodFunctor B S hS a).op.IsRightAdjoint :=
    (Functor.asEquivalence (neighborhoodFunctor B S hS a).op).symm.isRightAdjoint_inverse
  let : Functor.Final (neighborhoodFunctor B S hS a).op :=
    Functor.final_of_isRightAdjoint _
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  let G := (Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ F
  let E := (neighborhoodFunctor B S hS a).op
  dsimp [geometricPointStalkMap]
  exact Functor.Final.colimit_pre_isIso E

/-- The morphism of points of the unrestricted small étale site induced by
`a`. Its fiber component sends a lift `u'` to `u' ∘ a`. -/
@[stacks 04FN "morphism of associated site points"]
public def smallEtalePointHom :
    Scheme.pointSmallEtale s.hom ⟶ Scheme.pointSmallEtale t.hom where
  hom := {
    app U := ↾ (fun p =>
      (Over.homMk (U := Over.mk s.hom) (V := Over.mk t.hom) a.hom a.comm) ≫ p)
    naturality := by
      intro U V f
      ext p
      let aa : Over.mk s.hom ⟶ Over.mk t.hom :=
        Over.homMk a.hom a.comm
      let pp : Over.mk t.hom ⟶ (Scheme.Etale.forget S).obj U := p
      change aa ≫ (pp ≫ (Scheme.Etale.forget S).map f) =
        (aa ≫ pp) ≫ (Scheme.Etale.forget S).map f
      exact (Category.assoc aa pp ((Scheme.Etale.forget S).map f)).symm }

/-- A morphism of geometric points induces an isomorphism of their associated
points of the small étale site. -/
@[stacks 04FN "isomorphism of associated site points"]
public theorem smallEtalePointHom_isIso : IsIso (smallEtalePointHom S a) := by
  let f := smallEtalePointHom S a
  have hf : IsIso f.hom := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [isIso_iff_bijective]
    constructor
    · intro p q hpq
      exact Over.OverMorphism.ext (specFieldHom_cancel a.hom (congrArg (fun m => m.left) hpq))
    · intro p
      obtain ⟨q, hqa, hqf⟩ := factor_etale_point U.hom a.hom t.hom p.left
        ((Over.w p).trans a.comm.symm)
      exact ⟨Over.homMk q hqf, Over.OverMorphism.ext hqa⟩
  let : IsIso f.hom := hf
  let g : Scheme.pointSmallEtale t.hom ⟶ Scheme.pointSmallEtale s.hom :=
    ⟨(asIso f.hom).inv⟩
  refine ⟨g, ?_, ?_⟩
  · apply CategoryTheory.GrothendieckTopology.Point.hom_ext
    change (asIso f.hom).inv ≫ f.hom = 𝟙 _
    exact (asIso f.hom).inv_hom_id
  · apply CategoryTheory.GrothendieckTopology.Point.hom_ext
    change f.hom ≫ (asIso f.hom).inv = 𝟙 _
    exact (asIso f.hom).hom_inv_id
end AlgebraicGeometry

end
