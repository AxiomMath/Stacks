module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Refinement
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.Canonicity
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.Henselization.EtaleNeighborhood
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback
import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood

/-!
# Henselizations as colimits of elementary étale neighbourhoods

For a point `s` of a scheme `S`, the henselization of the local ring at `s` is the filtered
colimit of the rings of global sections of the elementary étale neighbourhoods of `(S, s)`. The
indexing category is the opposite of the category of elementary étale neighbourhoods, which is
cofiltered because two neighbourhoods are dominated by their fibre product and two morphisms of
neighbourhoods inducing the same map of residue fields are equalized after a refinement.

## Main definitions

* `AlgebraicGeometry.ElementaryEtaleNeighborhood` is the full subcategory of elementary étale
  neighbourhoods.
* `AlgebraicGeometry.globalSections` is the diagram sending a neighbourhood to its ring of
  global sections.
* `AlgebraicGeometry.elementaryEtaleAugmentation` is the canonical map from global sections of a
  neighbourhood to the residue field at the base point.
* `AlgebraicGeometry.henselizationResidueFieldMap` is the residue-field map induced by the given
  stalk-algebra structure on a henselization.
* `AlgebraicGeometry.stalkMap` is the map on local rings induced by a pointed elementary étale
  neighbourhood.
* `AlgebraicGeometry.IsOverStalk` says that a map out of the global sections of a neighbourhood
  factors through its local ring at the distinguished point by a local homomorphism over the
  local ring of `S`.

## Main results

* `AlgebraicGeometry.instIsFilteredOppositeElementaryEtaleNeighborhood`: the opposite category of
  elementary étale neighbourhoods is filtered.
* `AlgebraicGeometry.indEtale_stalkMap_of_etale` and
  `AlgebraicGeometry.indEtale_elementaryStalkMap`: the map on local rings induced by an étale
  morphism, respectively by an elementary étale neighbourhood, is ind-étale.
* `AlgebraicGeometry.isColimit_globalSections`: a henselization of the local ring is the colimit
  of the global-sections diagram.

## Implementation notes

The colimit is expressed by its canonical cocone with vertex an arbitrary model `Rh` of the
henselization. Each leg factors through the local ring at the distinguished point by a local
homomorphism over the local ring of `S`. The residue-field condition specifies the distinguished
point and its residue-field identification. Requiring the local-ring factorization, rather than
the residue condition alone, pins the maps relative to `S`: a residue condition on maps of bare
rings would also allow automorphisms of `Rh` fixing its residue field. The indexing category is
explicitly the opposite of the category of étale neighbourhoods of Tag 02LE.

## References

* [Stacks Project, Tag 05KS](https://stacks.math.columbia.edu/tag/05KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

/-- An étale algebra is ind-étale. -/
theorem indEtale_of_etale {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (h : Algebra.Etale R S) : StacksDraft.IndEtale R S := by
  rw [StacksDraft.indEtale_iff]
  exact CategoryTheory.ObjectProperty.le_ind (CommAlgCat.etale R) (CommAlgCat.of R S) h

/-- The stalk map of an étale morphism of schemes is ind-étale: on affine charts it is a
localization of an étale ring map, and both localizations are ind-étale. -/
theorem indEtale_stalkMap_of_etale {Y X : Scheme.{u}} (f : Y ⟶ X)
    [Etale f] (y : Y) :
    letI : Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
      (f.stalkMap y).hom.toAlgebra
    StacksDraft.IndEtale (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyW (f ⁻¹ᵁ W).isOpen
  let A := Γ(X, W)
  let B := Γ(Y, V)
  let m := (f.appLE W V hVW).hom
  let p : Ideal A := (hW.primeIdealOf ⟨f y, hVW hyV⟩).asIdeal
  let q : Ideal B := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  let K := Localization.AtPrime p
  let L := Localization.AtPrime q
  let : Algebra A B := m.toAlgebra
  let : Algebra.Etale A B := RingHom.etale_algebraMap.mp (f.etale_appLE hW hV hVW)
  have hAL : StacksDraft.IndEtale A L := StacksDraft.indEtale_comp
    (indEtale_of_etale (R := A) (S := B) inferInstance) (StacksDraft.indEtale_atPrime q)
  have hpq : p = q.comap m := by
    simpa [p, q, A, B, m] using
      (congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE W hW V hV hVW hyV)).symm
  let localMap : K →+* L := Localization.localRingHom p q m hpq
  let : Algebra K L := localMap.toAlgebra
  have hmap (a : A) : (algebraMap A L) a = localMap (algebraMap A K a) := by
    change (algebraMap B L) (m a) =
      Localization.localRingHom p q m hpq (algebraMap A K a)
    exact (Localization.localRingHom_to_map p q m hpq a).symm
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq hmap
  have hKL : StacksDraft.IndEtale K L :=
    StacksDraft.indEtale_of_comp (StacksDraft.indEtale_atPrime p) hAL
  let eArrow := hW.arrowStalkMapIso f W V hV hVW hyV
  let eA : X.presheaf.stalk (f y) ≃+* K :=
    (asIso eArrow.hom.left).commRingCatIsoToRingEquiv
  let eB : Y.presheaf.stalk y ≃+* L :=
    (asIso eArrow.hom.right).commRingCatIsoToRingEquiv
  let : Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have hcomm (a : X.presheaf.stalk (f y)) :
      eB ((f.stalkMap y).hom a) = localMap (eA a) := by
    have hw : eArrow.hom.left ≫ CommRingCat.ofHom localMap =
        CommRingCat.ofHom (f.stalkMap y).hom ≫ eArrow.hom.right := by
      simp [eArrow]
    exact (ConcreteCategory.congr_hom hw a).symm
  have hcomm' (a : K) :
      eB.symm (localMap a) = (f.stalkMap y).hom (eA.symm a) := by
    apply eB.injective
    simpa using (hcomm (eA.symm a)).symm
  exact StacksDraft.indEtale_of_equiv
    (A := K) (B := L) (A' := X.presheaf.stalk (f y))
    (B' := Y.presheaf.stalk y) eA.symm eB.symm hcomm' hKL

/-- For an elementary étale neighbourhood the residue field map of the structure morphism at the
distinguished point is an isomorphism. -/
lemma toBase_residueFieldMap_isIso_of_elementary
    {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s)
    (hU : U.IsElementary) : IsIso (U.toBase.residueFieldMap U.point) := by
  have : IsIso ((S.residueFieldCongr U.map_point).inv ≫
      U.toBase.residueFieldMap U.point) := hU
  exact IsIso.of_isIso_comp_left ((S.residueFieldCongr U.map_point).inv)
    (U.toBase.residueFieldMap U.point)

private lemma elementary_of_toBase_residueFieldMap_isIso
    {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s)
    (hU : IsIso (U.toBase.residueFieldMap U.point)) : U.IsElementary := by
  dsimp [EtaleNeighborhood.IsElementary,
    EtaleNeighborhood.residueFieldMap]
  let : IsIso (U.toBase.residueFieldMap U.point) := hU
  infer_instance

private alias pullback_fst_residueFieldMap_isIso_of_elementary :=
  Stacks.Flatness.pullback_fst_residueFieldMap_isIso_of_elementary

private lemma elementary_pullback {S : Scheme.{u}} {s : S}
    (U V : EtaleNeighborhood S s)
    (hU : U.IsElementary) (hV : V.IsElementary)
    (z : (Limits.pullback U.toBase V.toBase : Scheme).carrier)
    (hzU : (Limits.pullback.fst U.toBase V.toBase) z = U.point)
    (hzV : (Limits.pullback.snd U.toBase V.toBase) z = V.point) :
    (⟨Limits.pullback U.toBase V.toBase, z,
      Limits.pullback.fst U.toBase V.toBase ≫ U.toBase,
      by simpa only [Scheme.Hom.comp_apply, hzU] using U.map_point⟩ :
      EtaleNeighborhood S s).IsElementary := by
  have hfst : IsIso ((Limits.pullback.fst U.toBase V.toBase).residueFieldMap z) :=
    pullback_fst_residueFieldMap_isIso_of_elementary U.toBase s V hV z hzV
  have hbase' : IsIso (U.toBase.residueFieldMap
      ((Limits.pullback.fst U.toBase V.toBase) z)) := by
    rw [hzU]
    exact toBase_residueFieldMap_isIso_of_elementary U hU
  have hcomp : IsIso ((Limits.pullback.fst U.toBase V.toBase ≫ U.toBase).residueFieldMap z) := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hbase' hfst
  exact elementary_of_toBase_residueFieldMap_isIso
    ⟨Limits.pullback U.toBase V.toBase, z, Limits.pullback.fst U.toBase V.toBase ≫ U.toBase,
      by simpa only [Scheme.Hom.comp_apply, hzU] using U.map_point⟩ hcomp

private lemma affine_elementary_refinement_over_open {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (V : S.Opens) (hs : s ∈ V) :
    ∃ W : EtaleNeighborhood S s,
      W.IsElementary ∧ IsAffine W.scheme ∧ Nonempty (W ⟶ U) ∧
        ∀ x : W.scheme, W.toBase x ∈ V := by
  obtain ⟨O, hO, hu, hsub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := U.scheme) (x := U.point)
      (U := U.toBase ⁻¹ᵁ V) (by simpa [U.map_point] using hs)
  let W : EtaleNeighborhood S s :=
    { scheme := O
      point := ⟨U.point, hu⟩
      toBase := O.ι ≫ U.toBase
      map_point := U.map_point }
  have hW : W.IsElementary := by
    let : IsIso ((S.residueFieldCongr U.map_point).inv) := inferInstance
    change IsIso ((S.residueFieldCongr W.map_point).inv ≫
      W.toBase.residueFieldMap W.point)
    rw [Scheme.residueFieldMap_comp]
    change IsIso (((S.residueFieldCongr U.map_point).inv ≫
      U.toBase.residueFieldMap U.point) ≫ O.ι.residueFieldMap W.point)
    exact IsIso.comp_isIso' hU (inferInstance : IsIso (O.ι.residueFieldMap W.point))
  exact ⟨W, hW, hO, ⟨⟨O.ι, rfl, rfl⟩⟩, fun x => hsub x.2⟩

private lemma residueFieldMap_naturality {S : Scheme.{u}} {s : S}
    (U V : EtaleNeighborhood S s) (h : U ⟶ V) :
    U.residueFieldMap = V.residueFieldMap ≫
      (V.scheme.residueFieldCongr h.map_point).inv ≫
        h.hom.residueFieldMap U.point := by
  let eS := congrArg V.toBase h.map_point
  let c := S.residueFieldCongr eS
  let d := V.scheme.residueFieldCongr h.map_point
  have hpoint : V.toBase (h.hom U.point) = U.toBase U.point := by
    have hp := congrArg (fun k : U.scheme ⟶ S => k U.point) h.over
    simpa only [Scheme.Hom.comp_apply] using hp
  have he : eS.trans V.map_point = hpoint.trans U.map_point :=
    Subsingleton.elim _ _
  have htransport : V.toBase.residueFieldMap V.point ≫ d.inv =
      c.inv ≫ V.toBase.residueFieldMap (h.hom U.point) := by
    have hcd : V.toBase.residueFieldMap (h.hom U.point) ≫ d.hom =
        c.hom ≫ V.toBase.residueFieldMap V.point :=
      Scheme.Hom.residueFieldMap_congr' h.map_point
    calc
      _ = c.inv ≫ (c.hom ≫ V.toBase.residueFieldMap V.point) ≫ d.inv := by
        simp [Category.assoc]
      _ = c.inv ≫ (V.toBase.residueFieldMap (h.hom U.point) ≫ d.hom) ≫ d.inv := by
        rw [← hcd]
      _ = _ := by simp [Category.assoc]
  have hprefix : (S.residueFieldCongr V.map_point).inv ≫ c.inv =
      (S.residueFieldCongr U.map_point).inv ≫
        (S.residueFieldCongr hpoint).inv := by
    calc
      _ = (c ≪≫ S.residueFieldCongr V.map_point).inv := by simp [c]
      _ = (S.residueFieldCongr (eS.trans V.map_point)).inv := by
        rw [Scheme.residueFieldCongr_trans]
      _ = (S.residueFieldCongr (hpoint.trans U.map_point)).inv := by rw [he]
      _ = _ := by simp
  have hcomp : (h.hom ≫ V.toBase).residueFieldMap U.point =
      (S.residueFieldCongr hpoint).hom ≫ U.toBase.residueFieldMap U.point :=
    Scheme.Hom.residueFieldMap_congr h.over U.point
  dsimp [EtaleNeighborhood.residueFieldMap]
  calc
    _ = (S.residueFieldCongr U.map_point).inv ≫ (S.residueFieldCongr hpoint).inv ≫
        (h.hom ≫ V.toBase).residueFieldMap U.point := by
      rw [hcomp]
      simp
    _ = (S.residueFieldCongr U.map_point).inv ≫ (S.residueFieldCongr hpoint).inv ≫
        V.toBase.residueFieldMap (h.hom U.point) ≫ h.hom.residueFieldMap U.point := by
      rw [Scheme.residueFieldMap_comp]
    _ = (S.residueFieldCongr V.map_point).inv ≫ V.toBase.residueFieldMap V.point ≫
        d.inv ≫ h.hom.residueFieldMap U.point := by
      calc
        _ = ((S.residueFieldCongr U.map_point).inv ≫
            (S.residueFieldCongr hpoint).inv) ≫
              (V.toBase.residueFieldMap (h.hom U.point) ≫ h.hom.residueFieldMap U.point) := by
          simp
        _ = ((S.residueFieldCongr V.map_point).inv ≫ c.inv) ≫
              (V.toBase.residueFieldMap (h.hom U.point) ≫ h.hom.residueFieldMap U.point) := by
          rw [hprefix.symm]
        _ = ((S.residueFieldCongr V.map_point).inv ≫
              (V.toBase.residueFieldMap V.point ≫ d.inv)) ≫
                h.hom.residueFieldMap U.point := by
          calc
            _ = (S.residueFieldCongr V.map_point).inv ≫
                (c.inv ≫ V.toBase.residueFieldMap (h.hom U.point)) ≫
                  h.hom.residueFieldMap U.point := by simp [Category.assoc]
            _ = (S.residueFieldCongr V.map_point).inv ≫
                (V.toBase.residueFieldMap V.point ≫ d.inv) ≫
                  h.hom.residueFieldMap U.point := by rw [htransport.symm]
        _ = _ := by simp [Category.assoc]

/-- The category of elementary étale neighborhoods of a pointed scheme. -/
abbrev ElementaryEtaleNeighborhood (S : Scheme.{u}) (s : S) :=
  CategoryTheory.ObjectProperty.FullSubcategory
    (fun U : EtaleNeighborhood S s ↦
      EtaleNeighborhood.IsElementary U)

/-- The functor which forgets an elementary étale neighborhood down to its
underlying scheme. -/
def ElementaryEtaleNeighborhood.toScheme (S : Scheme.{u}) (s : S) :
    ElementaryEtaleNeighborhood S s ⥤ Scheme.{u} where
  obj U := U.obj.scheme
  map f := f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The diagram of global section rings indexed by the opposite category of
elementary étale neighborhoods. -/
def globalSections (S : Scheme.{u}) (s : S) :
    (ElementaryEtaleNeighborhood S s)ᵒᵖ ⥤ CommRingCat.{u} :=
  (ElementaryEtaleNeighborhood.toScheme S s).op ⋙ Scheme.Γ

/-- Evaluation at the chosen point, followed by the inverse of the residue
field isomorphism, gives the augmentation of an elementary étale neighborhood
to the residue field of the base point. -/
noncomputable def elementaryEtaleAugmentation (S : Scheme.{u}) (s : S)
    (U : ElementaryEtaleNeighborhood S s) :
    ((globalSections S s).obj (op U) : Type u) →+* (S.residueField s : Type u) := by
  letI : IsIso U.obj.residueFieldMap := U.property
  exact (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _) ≫
    U.obj.scheme.residue U.obj.point ≫ inv U.obj.residueFieldMap).hom

/-- The map on residue fields induced by the specified algebra structure of a
henselization over the local ring. -/
noncomputable def henselizationResidueFieldMap (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh] :
    (S.residueField s : Type u) →+* IsLocalRing.ResidueField Rh := by
  letI : IsLocalHom (algebraMap (S.presheaf.stalk s) Rh) :=
    IsLocalRing.IsHenselization.isLocalHom
      (R := S.presheaf.stalk s)
      (L := IsLocalRing.ResidueField (S.presheaf.stalk s)) (Rh := Rh)
  exact IsLocalRing.ResidueField.map (algebraMap (S.presheaf.stalk s) Rh)

/-- The homomorphism on local rings induced by a pointed elementary étale
neighborhood, with its target point identified with `s`. -/
def stalkMap (S : Scheme.{u}) (s : S)
    (U : ElementaryEtaleNeighborhood S s) :
    S.presheaf.stalk s →+* U.obj.scheme.presheaf.stalk U.obj.point := by
  exact (U.obj.toBase.stalkMap U.obj.point).hom.comp
    (S.presheaf.stalkCongr (.of_eq U.obj.map_point.symm)).hom.hom

/-- The map on local rings induced by an elementary étale neighbourhood is ind-étale. -/
theorem indEtale_elementaryStalkMap (S : Scheme.{u}) (s : S)
    (U : ElementaryEtaleNeighborhood S s) :
    letI : Algebra (S.presheaf.stalk s) (U.obj.scheme.presheaf.stalk U.obj.point) :=
      (stalkMap S s U).toAlgebra
    StacksDraft.IndEtale (S.presheaf.stalk s)
      (U.obj.scheme.presheaf.stalk U.obj.point) := by
  classical
  let f := U.obj.toBase
  let eIso := S.presheaf.stalkCongr (Inseparable.of_eq U.obj.map_point.symm)
  let e : S.presheaf.stalk s ≃+* S.presheaf.stalk (f U.obj.point) :=
    eIso.commRingCatIsoToRingEquiv
  let : Algebra (S.presheaf.stalk (f U.obj.point))
      (U.obj.scheme.presheaf.stalk U.obj.point) := (f.stalkMap _).hom.toAlgebra
  let : Algebra (S.presheaf.stalk s)
      (U.obj.scheme.presheaf.stalk U.obj.point) :=
    (stalkMap S s U).toAlgebra
  have hRaw : StacksDraft.IndEtale (S.presheaf.stalk (f U.obj.point))
      (U.obj.scheme.presheaf.stalk U.obj.point) := indEtale_stalkMap_of_etale f U.obj.point
  have hcomm (a : S.presheaf.stalk (f U.obj.point)) :
      (algebraMap (S.presheaf.stalk (f U.obj.point))
        (U.obj.scheme.presheaf.stalk U.obj.point)) a =
        (algebraMap (S.presheaf.stalk s)
        (U.obj.scheme.presheaf.stalk U.obj.point)) (e.symm a) := by
    change (f.stalkMap U.obj.point).hom a = stalkMap S s U (e.symm a)
    change (f.stalkMap U.obj.point).hom a =
      (f.stalkMap U.obj.point).hom (eIso.hom.hom (eIso.inv.hom a))
    simp
  exact StacksDraft.indEtale_of_equiv
    (A := S.presheaf.stalk (f U.obj.point))
    (B := U.obj.scheme.presheaf.stalk U.obj.point)
    (A' := S.presheaf.stalk s) (B' := U.obj.scheme.presheaf.stalk U.obj.point)
    e.symm (RingEquiv.refl _) hcomm hRaw

private theorem residueFieldMap_stalkCongr_eq (S : Scheme.{u}) {x y : S} (h : x = y) :
    CommRingCat.ofHom (IsLocalRing.ResidueField.map
      (S.presheaf.stalkCongr (.of_eq h)).hom.hom) = (S.residueFieldCongr h).hom := by
  let : IsLocalHom (S.presheaf.stalkCongr (.of_eq h)).hom.hom := inferInstance
  apply CommRingCat.hom_ext
  ext z
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  change IsLocalRing.ResidueField.map
      (S.presheaf.stalkCongr (.of_eq h)).hom.hom
      (IsLocalRing.residue (S.presheaf.stalk x) a) =
    (S.residueFieldCongr h).hom (IsLocalRing.residue (S.presheaf.stalk x) a)
  rw [IsLocalRing.ResidueField.map_residue]
  exact (congrArg (fun k : CommRingCat.Hom _ _ => k.hom a)
    (Scheme.residue_residueFieldCongr S h)).symm

private theorem residueFieldMap_stalkMap_eq (S : Scheme.{u}) (s : S)
    (U : ElementaryEtaleNeighborhood S s) (hlocal : IsLocalHom (stalkMap S s U)) :
    CommRingCat.ofHom (IsLocalRing.ResidueField.map (stalkMap S s U)) =
      U.obj.residueFieldMap := by
  let := hlocal
  dsimp [stalkMap, EtaleNeighborhood.residueFieldMap,
    Scheme.Hom.residueFieldMap]
  rw [IsLocalRing.ResidueField.map_comp, CommRingCat.ofHom_comp,
    residueFieldMap_stalkCongr_eq S U.obj.map_point.symm]
  rfl

/-- The unique local `S_s`-algebra map from the local ring at the distinguished point of an
elementary étale neighbourhood to a henselization of `S_s`. -/
private theorem existsUnique_stalkLift (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s) :
    let : Algebra (S.presheaf.stalk s) (U.obj.scheme.presheaf.stalk U.obj.point) :=
      (stalkMap S s U).toAlgebra
    ∃! f : U.obj.scheme.presheaf.stalk U.obj.point →ₐ[S.presheaf.stalk s] Rh,
      IsLocalHom f := by
  let : Algebra (S.presheaf.stalk s) (U.obj.scheme.presheaf.stalk U.obj.point) :=
    (stalkMap S s U).toAlgebra
  have : IsLocalHom (stalkMap S s U) := by
    dsimp [stalkMap]
    infer_instance
  have : IsLocalHom (algebraMap (S.presheaf.stalk s)
      (U.obj.scheme.presheaf.stalk U.obj.point)) := by
    change IsLocalHom (stalkMap S s U)
    infer_instance
  have : IsLocalHom (algebraMap (S.presheaf.stalk s) Rh) :=
    IsLocalRing.IsHenselization.isLocalHom
      (R := S.presheaf.stalk s)
      (L := IsLocalRing.ResidueField (S.presheaf.stalk s)) (Rh := Rh)
  have : HenselianLocalRing Rh :=
    IsLocalRing.IsHenselization.henselian
      (R := S.presheaf.stalk s)
      (L := IsLocalRing.ResidueField (S.presheaf.stalk s)) (Rh := Rh)
  have hres : Function.Surjective (IsLocalRing.ResidueField.map
      (algebraMap (S.presheaf.stalk s) (U.obj.scheme.presheaf.stalk U.obj.point))) := by
    have hmap : IsLocalRing.ResidueField.map (stalkMap S s U) =
        U.obj.residueFieldMap.hom := congrArg CommRingCat.Hom.hom
          (residueFieldMap_stalkMap_eq S s U inferInstance)
    change Function.Surjective (IsLocalRing.ResidueField.map (stalkMap S s U))
    rw [hmap]
    let : IsIso U.obj.residueFieldMap := U.property
    exact (ConcreteCategory.bijective_of_isIso U.obj.residueFieldMap).2
  exact HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale
    (Sh := Rh) (indEtale_elementaryStalkMap S s U) hres

private noncomputable def stalkLift (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s) :
    U.obj.scheme.presheaf.stalk U.obj.point →+* Rh := by
  letI : Algebra (S.presheaf.stalk s) (U.obj.scheme.presheaf.stalk U.obj.point) :=
    (stalkMap S s U).toAlgebra
  exact (existsUnique_stalkLift S s Rh U).choose.toRingHom

private theorem stalkLift_isLocalHom (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s) :
    IsLocalHom (stalkLift S s Rh U) := by
  let : Algebra (S.presheaf.stalk s) (U.obj.scheme.presheaf.stalk U.obj.point) :=
    (stalkMap S s U).toAlgebra
  have : IsLocalHom (existsUnique_stalkLift S s Rh U).choose :=
    (existsUnique_stalkLift S s Rh U).choose_spec.1
  exact isLocalHom_toRingHom (existsUnique_stalkLift S s Rh U).choose

private theorem stalkLift_base (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s) :
    (stalkLift S s Rh U).comp (stalkMap S s U) =
      algebraMap (S.presheaf.stalk s) Rh := by
  let : Algebra (S.presheaf.stalk s) (U.obj.scheme.presheaf.stalk U.obj.point) :=
    (stalkMap S s U).toAlgebra
  exact RingHom.ext fun a => (existsUnique_stalkLift S s Rh U).choose.commutes a

private lemma stalkLift_unique (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s)
    (g : U.obj.scheme.presheaf.stalk U.obj.point →+* Rh) [IsLocalHom g]
    (hg : g.comp (stalkMap S s U) = algebraMap (S.presheaf.stalk s) Rh) :
    g = stalkLift S s Rh U := by
  let : Algebra (S.presheaf.stalk s) (U.obj.scheme.presheaf.stalk U.obj.point) :=
    (stalkMap S s U).toAlgebra
  let g' : U.obj.scheme.presheaf.stalk U.obj.point →ₐ[S.presheaf.stalk s] Rh :=
    { g with commutes' := fun x => RingHom.congr_fun hg x }
  have : IsLocalHom g' := ⟨IsLocalHom.map_nonunit (f := g)⟩
  exact congrArg AlgHom.toRingHom ((existsUnique_stalkLift S s Rh U).choose_spec.2 g' inferInstance)

private theorem stalkMap_neighborhood_naturality {S : Scheme.{u}} {s : S}
    (U V : ElementaryEtaleNeighborhood S s) (h : V.obj ⟶ U.obj) :
    (S.presheaf.stalkCongr (.of_eq U.obj.map_point.symm)).hom ≫
      U.obj.toBase.stalkMap U.obj.point ≫
        (U.obj.scheme.presheaf.stalkCongr (.of_eq h.map_point.symm)).hom ≫
          h.hom.stalkMap V.obj.point =
    (S.presheaf.stalkCongr (.of_eq V.obj.map_point.symm)).hom ≫
      V.obj.toBase.stalkMap V.obj.point := by
  let eU := U.obj.scheme.presheaf.stalkCongr (.of_eq h.map_point)
  let eS := S.presheaf.stalkCongr
    (.of_eq (congrArg U.obj.toBase h.map_point))
  have hp := Scheme.Hom.stalkMap_congr_point U.obj.toBase
    (h.hom V.obj.point) U.obj.point h.map_point
  have hinv : U.obj.toBase.stalkMap (h.hom V.obj.point) ≫ eU.hom =
      eS.hom ≫ U.obj.toBase.stalkMap U.obj.point := by
    simpa [eU, eS] using hp
  have hpoint : U.obj.toBase.stalkMap U.obj.point ≫ eU.inv =
      eS.inv ≫ U.obj.toBase.stalkMap (h.hom V.obj.point) := by
    have hx := congrArg (fun k => eS.inv ≫ k ≫ eU.inv) hinv.symm
    simpa [Category.assoc] using hx
  have hEq : (h.hom ≫ U.obj.toBase) V.obj.point = V.obj.toBase V.obj.point := by
    simpa using congrArg (fun f : V.obj.scheme ⟶ S => f V.obj.point) h.over
  have hEq' : U.obj.toBase (h.hom V.obj.point) = V.obj.toBase V.obj.point := by
    simpa only [Scheme.Hom.comp_apply] using hEq
  have hpointS : U.obj.toBase (h.hom V.obj.point) = s := by
    rw [h.map_point]
    exact U.obj.map_point
  let e₁ : Inseparable s (U.obj.toBase U.obj.point) :=
    Inseparable.of_eq U.obj.map_point.symm
  let e₂ : Inseparable (U.obj.toBase (h.hom V.obj.point))
      (U.obj.toBase U.obj.point) :=
    Inseparable.of_eq (congrArg U.obj.toBase h.map_point)
  let e₃ : Inseparable s (U.obj.toBase (h.hom V.obj.point)) :=
    Inseparable.of_eq hpointS.symm
  have htrans : (S.presheaf.stalkCongr (.of_eq U.obj.map_point.symm)).hom ≫ eS.inv =
      (S.presheaf.stalkCongr (.of_eq hpointS.symm)).hom := by
    have hproof : e₂.specializes.trans e₁.specializes' = e₃.specializes' :=
      Subsingleton.elim _ _
    calc
      _ = S.presheaf.stalkSpecializes e₁.specializes' ≫
          S.presheaf.stalkSpecializes e₂.specializes := by
        rfl
      _ = S.presheaf.stalkSpecializes (e₂.specializes.trans e₁.specializes') := by
        rw [TopCat.Presheaf.stalkSpecializes_comp]
      _ = S.presheaf.stalkSpecializes e₃.specializes' := by rw [hproof]
      _ = _ := by simp [TopCat.Presheaf.stalkCongr]
  let e₄ : Inseparable (U.obj.toBase (h.hom V.obj.point))
      (V.obj.toBase V.obj.point) := Inseparable.of_eq hEq'
  let e₅ : Inseparable s (V.obj.toBase V.obj.point) :=
    Inseparable.of_eq V.obj.map_point.symm
  have htrans₂ :
      (S.presheaf.stalkCongr (.of_eq hpointS.symm)).hom ≫
        (S.presheaf.stalkCongr (.of_eq hEq')).hom =
      (S.presheaf.stalkCongr (.of_eq V.obj.map_point.symm)).hom := by
    have hproof : e₄.specializes'.trans e₃.specializes' = e₅.specializes' :=
      Subsingleton.elim _ _
    calc
      _ = S.presheaf.stalkSpecializes e₃.specializes' ≫
          S.presheaf.stalkSpecializes e₄.specializes' := by rfl
      _ = S.presheaf.stalkSpecializes (e₄.specializes'.trans e₃.specializes') := by
        rw [TopCat.Presheaf.stalkSpecializes_comp]
      _ = S.presheaf.stalkSpecializes e₅.specializes' := by rw [hproof]
      _ = _ := by simp [TopCat.Presheaf.stalkCongr]
  have hcat :
      (S.presheaf.stalkCongr (.of_eq U.obj.map_point.symm)).hom ≫
          U.obj.toBase.stalkMap U.obj.point ≫ eU.inv ≫
            h.hom.stalkMap V.obj.point =
        (S.presheaf.stalkCongr (.of_eq V.obj.map_point.symm)).hom ≫
          V.obj.toBase.stalkMap V.obj.point := by
    calc
      _ = (S.presheaf.stalkCongr (.of_eq U.obj.map_point.symm)).hom ≫
          eS.inv ≫ U.obj.toBase.stalkMap (h.hom V.obj.point) ≫
            h.hom.stalkMap V.obj.point := by
              have hx := congrArg
                (fun k => (S.presheaf.stalkCongr (.of_eq U.obj.map_point.symm)).hom ≫
                  k ≫ h.hom.stalkMap V.obj.point) hpoint
              simpa [Category.assoc] using hx
      _ = _ := by
        rw [← Category.assoc]
        rw [← Scheme.Hom.stalkMap_comp]
        rw [htrans]
        rw [Scheme.Hom.stalkMap_congr_hom (h.hom ≫ U.obj.toBase)
          V.obj.toBase h.over V.obj.point]
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ V.obj.toBase.stalkMap V.obj.point) htrans₂)
  exact hcat

private theorem stalkLift_neighborhood_naturality (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U V : ElementaryEtaleNeighborhood S s) (h : V.obj ⟶ U.obj) :
    (stalkLift S s Rh V).comp
      ((h.hom.stalkMap V.obj.point).hom.comp
        (U.obj.scheme.presheaf.stalkCongr (.of_eq h.map_point.symm)).hom.hom) =
      (stalkLift S s Rh U) := by
  let f : U.obj.scheme.presheaf.stalk U.obj.point →+*
      V.obj.scheme.presheaf.stalk V.obj.point :=
    (h.hom.stalkMap V.obj.point).hom.comp
      (U.obj.scheme.presheaf.stalkCongr (.of_eq h.map_point.symm)).hom.hom
  have hf : IsLocalHom f :=
    RingHom.isLocalHom_comp (h.hom.stalkMap V.obj.point).hom
      (U.obj.scheme.presheaf.stalkCongr (.of_eq h.map_point.symm)).hom.hom
  have hV : IsLocalHom (stalkLift S s Rh V) := stalkLift_isLocalHom S s Rh V
  have hn : f.comp (stalkMap S s U) = stalkMap S s V := by
    refine RingHom.ext fun a => ?_
    have hn := congrArg (fun k : CommRingCat.Hom _ _ => k.hom a)
      (stalkMap_neighborhood_naturality U V h)
    simpa [f, stalkMap, CommRingCat.hom_comp, RingHom.comp_assoc] using hn
  have : IsLocalHom ((stalkLift S s Rh V).comp f) := RingHom.isLocalHom_comp _ _
  exact stalkLift_unique S s Rh U _
    (by rw [RingHom.comp_assoc, hn, stalkLift_base])

/-- A map from the global sections of an elementary étale neighborhood to a
henselization is over the local ring of the base if it extends to a local map
from the local ring at its distinguished point. -/
def IsOverStalk (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    (U : ElementaryEtaleNeighborhood S s)
    (f : ((globalSections S s).obj (op U) : Type u) →+* Rh) : Prop :=
  ∃ g : U.obj.scheme.presheaf.stalk U.obj.point →+* Rh,
    IsLocalHom g ∧
      g.comp (stalkMap S s U) = algebraMap (S.presheaf.stalk s) Rh ∧
      f = g.comp (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom

private noncomputable def sectionLeg (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s) :
    ((globalSections S s).obj (op U) : Type u) →+* Rh :=
  (stalkLift S s Rh U).comp
    (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom

private theorem sectionLeg_naturality (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U V : ElementaryEtaleNeighborhood S s) (h : V ⟶ U) :
    sectionLeg S s Rh U = (sectionLeg S s Rh V).comp
      ((globalSections S s).map (Opposite.op h)).hom := by
  let h₀ : EtaleNeighborhood.Hom V.obj U.obj := h.hom
  apply RingHom.ext
  intro x
  let i := U.obj.scheme.presheaf.stalkCongr (.of_eq h₀.map_point.symm)
  have hstalk := stalkLift_neighborhood_naturality S s Rh U V h₀
  have hgerm :
      (h₀.hom.stalkMap V.obj.point).hom.comp
          (i.hom.hom.comp
            (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom) =
        (V.obj.scheme.presheaf.germ ⊤ V.obj.point (Set.mem_univ _)).hom.comp
          ((globalSections S s).map (Opposite.op h)).hom := by
    let e : Inseparable U.obj.point (h₀.hom V.obj.point) :=
      Inseparable.of_eq h₀.map_point.symm
    have htransport : U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _) ≫
        i.hom = U.obj.scheme.presheaf.germ ⊤ (h₀.hom V.obj.point)
          (Set.mem_univ _) := by
      change _ ≫ U.obj.scheme.presheaf.stalkSpecializes e.specializes' = _
      exact TopCat.Presheaf.germ_stalkSpecializes
        (F := U.obj.scheme.presheaf) (U := ⊤) (y := U.obj.point)
        (hy := Set.mem_univ _) (x := h₀.hom V.obj.point) e.specializes'
    have hh := Scheme.Hom.germ_stalkMap (f := h₀.hom) (U := ⊤)
      V.obj.point (Set.mem_univ _)
    have hc : (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _) ≫
        i.hom) ≫ h₀.hom.stalkMap V.obj.point =
        h₀.hom.app ⊤ ≫
          V.obj.scheme.presheaf.germ ⊤ V.obj.point (Set.mem_univ _) := by
      calc
        _ = U.obj.scheme.presheaf.germ ⊤ (h₀.hom V.obj.point) (Set.mem_univ _) ≫
            h₀.hom.stalkMap V.obj.point := by rw [htransport]
        _ = _ := hh
    exact congrArg CommRingCat.Hom.hom hc
  have hstalk' := congrArg (fun f : _ →+* Rh =>
    f.comp (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom) hstalk
  have h' := congrArg (fun f : _ →+* _ =>
    (stalkLift S s Rh V).comp f) hgerm
  have hx' := congrArg (fun f : _ →+* Rh => f x) (hstalk'.symm.trans h')
  change ((stalkLift S s Rh U).comp
    (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom) x =
    ((stalkLift S s Rh V).comp
      ((V.obj.scheme.presheaf.germ ⊤ V.obj.point (Set.mem_univ _)).hom.comp
        ((globalSections S s).map (Opposite.op h)).hom)) x
  exact hx'

private theorem sectionLeg_residue (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s) (x : (globalSections S s).obj (op U)) :
    IsLocalRing.residue Rh ((sectionLeg S s Rh U) x) =
      henselizationResidueFieldMap S s Rh
        (elementaryEtaleAugmentation S s U x) := by
  let L := stalkLift S s Rh U
  let a := stalkMap S s U
  let q := U.obj.residueFieldMap
  let q' : CommRingCat.of (IsLocalRing.ResidueField (S.presheaf.stalk s)) ⟶
      CommRingCat.of (IsLocalRing.ResidueField
        (U.obj.scheme.presheaf.stalk U.obj.point)) := q
  let : IsLocalHom L := stalkLift_isLocalHom S s Rh U
  let : IsLocalHom a := by
    dsimp [a, stalkMap]
    infer_instance
  let : IsLocalHom (algebraMap (S.presheaf.stalk s) Rh) :=
    IsLocalRing.IsHenselization.isLocalHom
      (R := S.presheaf.stalk s)
      (L := IsLocalRing.ResidueField (S.presheaf.stalk s)) (Rh := Rh)
  let : IsLocalHom (L.comp a) := RingHom.isLocalHom_comp L a
  have hbase : L.comp a = algebraMap (S.presheaf.stalk s) Rh := by
    simpa [L, a] using stalkLift_base S s Rh U
  have hcomp : IsLocalRing.ResidueField.map (algebraMap (S.presheaf.stalk s) Rh) =
      (IsLocalRing.ResidueField.map L).comp (IsLocalRing.ResidueField.map a) := by
    have hmap : IsLocalRing.ResidueField.map (algebraMap (S.presheaf.stalk s) Rh) =
        IsLocalRing.ResidueField.map (L.comp a) := by
      apply RingHom.ext
      intro z
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
      rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
        hbase]
    exact hmap.trans (IsLocalRing.ResidueField.map_comp a L)
  have hq : CommRingCat.ofHom (IsLocalRing.ResidueField.map a) = q' := by
    simpa [q'] using residueFieldMap_stalkMap_eq S s U inferInstance
  let : IsIso q' := U.property
  have hcat : q' ≫ CommRingCat.ofHom (IsLocalRing.ResidueField.map L) =
      CommRingCat.ofHom (IsLocalRing.ResidueField.map
        (algebraMap (S.presheaf.stalk s) Rh)) := by
    rw [← hq, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom hcomp.symm
  have hmap : CommRingCat.ofHom (IsLocalRing.ResidueField.map L) =
      inv q' ≫ CommRingCat.ofHom
        (IsLocalRing.ResidueField.map (algebraMap (S.presheaf.stalk s) Rh)) := by
    calc
      _ = 𝟙 _ ≫ CommRingCat.ofHom (IsLocalRing.ResidueField.map L) := by simp
      _ = inv q' ≫ (q' ≫ CommRingCat.ofHom (IsLocalRing.ResidueField.map L)) := by
        simp
      _ = _ := congrArg (fun f : CommRingCat.Hom _ _ => inv q' ≫ f) hcat
  have hmap' := congrArg (fun f : CommRingCat.Hom _ _ => f.hom
    (U.obj.scheme.residue U.obj.point
      ((U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom x))) hmap
  have hgoal : IsLocalRing.residue Rh
        (L ((U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom x)) =
      IsLocalRing.ResidueField.map (algebraMap (S.presheaf.stalk s) Rh)
        ((inv q').hom (U.obj.scheme.residue U.obj.point
          ((U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom x))) := by
    rw [← IsLocalRing.ResidueField.map_residue]
    exact hmap'
  exact hgoal

private lemma exists_elementary_common_refinement {S : Scheme.{u}} {s : S}
    (U V : ElementaryEtaleNeighborhood S s) :
    ∃ W : ElementaryEtaleNeighborhood S s, Nonempty ((W ⟶ U) × (W ⟶ V)) := by
  obtain ⟨z, hzU, hzV⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := U.obj.toBase) (g := V.obj.toBase) U.obj.point V.obj.point
      (U.obj.map_point.trans V.obj.map_point.symm)
  let W₀ : EtaleNeighborhood S s :=
    ⟨Limits.pullback U.obj.toBase V.obj.toBase, z,
      Limits.pullback.fst U.obj.toBase V.obj.toBase ≫ U.obj.toBase,
      by simpa only [Scheme.Hom.comp_apply, hzU] using U.obj.map_point⟩
  have hW₀ : W₀.IsElementary :=
    elementary_pullback U.obj V.obj U.property V.property z hzU hzV
  let W : ElementaryEtaleNeighborhood S s := ⟨W₀, hW₀⟩
  refine ⟨W, ⟨?_, ?_⟩⟩
  · exact ⟨⟨Limits.pullback.fst U.obj.toBase V.obj.toBase, rfl, hzU⟩⟩
  · exact ⟨⟨Limits.pullback.snd U.obj.toBase V.obj.toBase,
      (Limits.pullback.condition (f := U.obj.toBase) (g := V.obj.toBase)).symm, hzV⟩⟩

-- The pointwise residue-field comparison uses a large dependent Spec equivalence.
private lemma exists_elementary_equalizing_refinement {S : Scheme.{u}} {s : S}
    {U V : EtaleNeighborhood S s} (hU : U.IsElementary)
    (f g : U ⟶ V)
    (hκ : (V.scheme.residueFieldCongr f.map_point).inv ≫
        f.hom.residueFieldMap U.point =
      (V.scheme.residueFieldCongr g.map_point).inv ≫
        g.hom.residueFieldMap U.point) :
    ∃ W : EtaleNeighborhood S s, ∃ h : W ⟶ U,
      h ≫ f = h ≫ g ∧ W.IsElementary := by
  let i : Spec (.of (↑(U.scheme.residueField U.point))) ⟶ U.scheme :=
    U.scheme.fromSpecResidueField U.point
  let p₀ : Spec (U.scheme.residueField U.point) := default
  have hipoint : i p₀ = U.point := Scheme.fromSpecResidueField_apply U.point p₀
  have hfg : i ≫ f.hom = i ≫ g.hom := fromSpecResidueField_comp_eq f g hκ
  let D := Limits.pullback V.toBase V.toBase
  let q : U.scheme ⟶ D := Limits.pullback.lift (f := V.toBase) (g := V.toBase)
    f.hom g.hom (f.over.trans g.over.symm)
  have hqfst : q ≫ Limits.pullback.fst V.toBase V.toBase = f.hom :=
    Limits.pullback.lift_fst _ _ _
  have hqsnd : q ≫ Limits.pullback.snd V.toBase V.toBase = g.hom :=
    Limits.pullback.lift_snd _ _ _
  have hfac : i ≫ q = (i ≫ f.hom) ≫ Limits.pullback.diagonal V.toBase := by
    apply Limits.pullback.hom_ext <;> cat_disch
  have hqpoint : q U.point = Limits.pullback.diagonal V.toBase V.point := by
    have hp := congrArg (fun k : Spec (.of (U.scheme.residueField U.point)) ⟶ D => k p₀) hfac
    simpa only [Scheme.Hom.comp_apply, hipoint, f.map_point] using hp
  let : Etale q := by
    apply MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale)
      q (Limits.pullback.fst V.toBase V.toBase ≫ V.toBase)
    · infer_instance
    · simpa only [← Category.assoc, hqfst, f.over] using
        (inferInstance : Etale U.toBase)
  have : Etale (Limits.pullback.diagonal V.toBase) := by infer_instance
  have : IsOpenImmersion (Limits.pullback.diagonal V.toBase) := by infer_instance
  let P := Limits.pullback q (Limits.pullback.diagonal V.toBase)
  obtain ⟨z, hzU, hzV⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := q) (g := Limits.pullback.diagonal V.toBase) U.point V.point hqpoint
  let W : EtaleNeighborhood S s :=
    ⟨P, z, Limits.pullback.fst q (Limits.pullback.diagonal V.toBase) ≫ U.toBase,
      by
        change U.toBase ((Limits.pullback.fst q (Limits.pullback.diagonal V.toBase)) z) = s
        rw [hzU]
        exact U.map_point⟩
  let h : W ⟶ U := ⟨Limits.pullback.fst q (Limits.pullback.diagonal V.toBase), rfl, hzU⟩
  have hfg' : h ≫ f = h ≫ g := by
    apply EtaleNeighborhood.Hom.ext
    change Limits.pullback.fst q (Limits.pullback.diagonal V.toBase) ≫ f.hom =
      Limits.pullback.fst q (Limits.pullback.diagonal V.toBase) ≫ g.hom
    simp only [← hqfst, ← hqsnd, ← Category.assoc]
    rw [Limits.pullback.condition]
    simp
  have : IsOpenImmersion h.hom := by
    dsimp [h]
    infer_instance
  have hbase : IsIso (U.toBase.residueFieldMap (h.hom W.point)) := by
    rw [h.map_point]
    exact toBase_residueFieldMap_isIso_of_elementary U hU
  have hres : IsIso ((h.hom ≫ U.toBase).residueFieldMap W.point) := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hbase (by infer_instance)
  have hres' : IsIso (W.toBase.residueFieldMap W.point) := by
    rw [← h.over]
    exact hres
  exact ⟨W, h, hfg', elementary_of_toBase_residueFieldMap_isIso W hres'⟩

private lemma spec_stalkMap_fromSpecStalk (S : Scheme.{u}) (s : S)
    (U : ElementaryEtaleNeighborhood S s) :
    Spec.map (CommRingCat.ofHom (stalkMap S s U)) ≫ S.fromSpecStalk s =
      U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase := by
  change Spec.map ((S.presheaf.stalkCongr (.of_eq U.obj.map_point.symm)).hom ≫
    U.obj.toBase.stalkMap U.obj.point) ≫ _ = _
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (U.obj.toBase.stalkMap U.obj.point) ≫
    (Spec.map (S.presheaf.stalkSpecializes
      (Inseparable.of_eq U.obj.map_point.symm).specializes') ≫ _) = _
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk _

/-- A morphism out of the spectrum of a local ring, precomposed with the spectrum of a local
ring map, sends the closed point to the image of the closed point. -/
private lemma specMap_comp_closedPoint_apply {R T : CommRingCat.{u}} [IsLocalRing R]
    [IsLocalRing T] (f : R ⟶ T) [IsLocalHom f.hom] {X : Scheme.{u}} (g : Spec R ⟶ X) :
    (Spec.map f ≫ g) (IsLocalRing.closedPoint T) = g (IsLocalRing.closedPoint R) :=
  (Scheme.Hom.comp_apply _ _ _).trans
    (congrArg (fun z : Spec R => g z) Spec_closedPoint)

private def henselizationTo (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh] :
    Spec (.of Rh) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh)) ≫ S.fromSpecStalk s

private def neighborhoodLift (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s) : Spec (.of Rh) ⟶ U.obj.scheme :=
  Spec.map (CommRingCat.ofHom (stalkLift S s Rh U)) ≫
    U.obj.scheme.fromSpecStalk U.obj.point

private lemma neighborhoodLift_point (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s) :
    neighborhoodLift S s Rh U (IsLocalRing.closedPoint Rh) = U.obj.point := by
  have := stalkLift_isLocalHom S s Rh U
  exact (specMap_comp_closedPoint_apply (CommRingCat.ofHom (stalkLift S s Rh U))
    (U.obj.scheme.fromSpecStalk U.obj.point)).trans Scheme.fromSpecStalk_closedPoint

private lemma neighborhoodLift_base (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s) :
    neighborhoodLift S s Rh U ≫ U.obj.toBase = henselizationTo S s Rh := by
  rw [neighborhoodLift, Category.assoc, ← spec_stalkMap_fromSpecStalk,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, stalkLift_base]
  rfl

private lemma neighborhoodLift_toSpecΓ (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s) :
    neighborhoodLift S s Rh U ≫ U.obj.scheme.toSpecΓ =
      Spec.map (CommRingCat.ofHom (sectionLeg S s Rh U)) := by
  rw [neighborhoodLift, Category.assoc, Scheme.fromSpecStalk_toSpecΓ,
    ← Spec.map_comp]
  rfl

private lemma neighborhoodLift_unique (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : ElementaryEtaleNeighborhood S s) (f : Spec (.of Rh) ⟶ U.obj.scheme)
    (hp : f (IsLocalRing.closedPoint Rh) = U.obj.point)
    (hf : f ≫ U.obj.toBase = henselizationTo S s Rh) :
    f = neighborhoodLift S s Rh U := by
  obtain ⟨⟨x, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing U.obj.scheme (.of Rh)).symm.surjective f
  have : x = U.obj.point := by
    have hp' : (Spec.map g ≫ U.obj.scheme.fromSpecStalk x)
        (IsLocalRing.closedPoint Rh) = U.obj.point := hp
    have := hg
    exact Scheme.fromSpecStalk_closedPoint.symm.trans
      ((specMap_comp_closedPoint_apply g (U.obj.scheme.fromSpecStalk x)).symm.trans hp')
  subst x
  change (Spec.map g ≫ U.obj.scheme.fromSpecStalk U.obj.point) ≫ U.obj.toBase = _ at hf
  rw [Category.assoc, ← spec_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc] at hf
  have he : g.hom.comp (stalkMap S s U) = algebraMap (S.presheaf.stalk s) Rh := by
    apply (show Function.Injective (CommRingCat.ofHom : (_ →+* _) → _) from
        fun _ _ h => congrArg CommRingCat.Hom.hom h)
    apply Spec.map_injective
    exact (cancel_mono (S.fromSpecStalk s)).mp hf
  have he' := stalkLift_unique S s Rh U g.hom he
  change Spec.map g ≫ _ = Spec.map (CommRingCat.ofHom (stalkLift S s Rh U)) ≫ _
  rw [← he']
  rfl

/-- If the residue field map of `f ≫ g` at `x` is invertible, so is that of `g` at `f x`. -/
lemma residueFieldMap_isIso_of_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (h : IsIso ((f ≫ g).residueFieldMap x)) :
    IsIso (g.residueFieldMap (f x)) := by
  rw [Scheme.residueFieldMap_comp] at h
  have hj := (ConcreteCategory.isIso_iff_bijective _).mp h
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(g.residueFieldMap (f x)).hom.injective, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hj.2 ((f.residueFieldMap x).hom y)
  exact ⟨z, (f.residueFieldMap x).hom.injective hz⟩

private lemma henselizationTo_point (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh] :
    henselizationTo S s Rh (IsLocalRing.closedPoint Rh) = s := by
  have := IsLocalRing.IsHenselization.isLocalHom
    (R := S.presheaf.stalk s) (L := IsLocalRing.ResidueField (S.presheaf.stalk s)) (Rh := Rh)
  exact (specMap_comp_closedPoint_apply
    (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh)) (S.fromSpecStalk s)).trans
    Scheme.fromSpecStalk_closedPoint

private lemma henselizationTo_residueFieldMap (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh] :
    IsIso ((henselizationTo S s Rh).residueFieldMap (IsLocalRing.closedPoint Rh)) := by
  have := IsLocalRing.IsHenselization.isLocalHom
    (R := S.presheaf.stalk s) (L := IsLocalRing.ResidueField (S.presheaf.stalk s)) (Rh := Rh)
  let a : S.presheaf.stalk s ⟶ CommRingCat.of Rh :=
    CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh)
  have h := (SpecToEquivOfLocalRing S (.of Rh)).apply_symm_apply ⟨s, a, inferInstance⟩
  obtain ⟨hp, hg⟩ := SpecToEquivOfLocalRing_eq_iff.mp h
  change henselizationTo S s Rh (IsLocalRing.closedPoint Rh) = s at hp
  change Scheme.stalkClosedPointTo (henselizationTo S s Rh) =
    (S.presheaf.stalkCongr (.of_eq hp)).hom ≫ a at hg
  have hs : Function.Surjective (IsLocalRing.ResidueField.map
      (Scheme.stalkClosedPointTo (henselizationTo S s Rh)).hom) := by
    have hg' : IsLocalRing.ResidueField.map
        (Scheme.stalkClosedPointTo (henselizationTo S s Rh)).hom =
        (IsLocalRing.ResidueField.map (algebraMap (S.presheaf.stalk s) Rh)).comp
          (IsLocalRing.ResidueField.map
            (S.presheaf.stalkCongr (.of_eq hp)).hom.hom) := by
      ext x
      obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
      simp only [IsLocalRing.ResidueField.map_residue, RingHom.comp_apply]
      exact congrArg (IsLocalRing.residue Rh) (ConcreteCategory.congr_hom hg y)
    rw [hg']
    exact (IsLocalRing.IsHenselization.residueField_map_bijective
      (R := S.presheaf.stalk s) (Rh := Rh)).2.comp
        (IsLocalRing.ResidueField.mapEquiv
          (S.presheaf.stalkCongr (.of_eq hp)).commRingCatIsoToRingEquiv).surjective
  have : IsLocalHom (stalkClosedPointIso (.of Rh)).hom.hom :=
    isLocalHom_of_leftInverse (stalkClosedPointIso (.of Rh)).inv.hom
      (fun x => ConcreteCategory.congr_hom (stalkClosedPointIso (.of Rh)).hom_inv_id x)
  simp only [Scheme.stalkClosedPointTo, CommRingCat.hom_comp] at hs
  have : IsLocalRing ((Spec (CommRingCat.of Rh)).presheaf.stalk
      (IsLocalRing.closedPoint ↑(CommRingCat.of Rh) : Spec (CommRingCat.of Rh))) :=
    (Spec (CommRingCat.of Rh)).toLocallyRingedSpace.isLocalRing _
  have hlocStalk : IsLocalHom ((henselizationTo S s Rh).stalkMap
      (IsLocalRing.closedPoint Rh)).hom :=
    (henselizationTo S s Rh).toLRSHom.prop _
  have : IsLocalHom ((stalkClosedPointIso (.of Rh)).hom.hom.comp
      ((henselizationTo S s Rh).stalkMap (IsLocalRing.closedPoint Rh)).hom) :=
    RingHom.isLocalHom_comp _ _
  have hmc : IsLocalRing.ResidueField.map
      ((stalkClosedPointIso (.of Rh)).hom.hom.comp
        ((henselizationTo S s Rh).stalkMap (IsLocalRing.closedPoint Rh)).hom) =
      (IsLocalRing.ResidueField.map (stalkClosedPointIso (.of Rh)).hom.hom).comp
        (IsLocalRing.ResidueField.map
          ((henselizationTo S s Rh).stalkMap (IsLocalRing.closedPoint Rh)).hom) :=
    IsLocalRing.ResidueField.map_comp _ _
  rw [hmc] at hs
  have hinjIso : Function.Injective (IsLocalRing.ResidueField.map
      (stalkClosedPointIso (.of Rh)).hom.hom) :=
    (IsLocalRing.ResidueField.mapEquiv
      (stalkClosedPointIso (.of Rh)).commRingCatIsoToRingEquiv).injective
  have hsurj : Function.Surjective (IsLocalRing.ResidueField.map
      ((henselizationTo S s Rh).stalkMap (IsLocalRing.closedPoint Rh)).hom) := by
    intro y
    obtain ⟨x, hx⟩ := hs (IsLocalRing.ResidueField.map
      (stalkClosedPointIso (.of Rh)).hom.hom y)
    exact ⟨x, hinjIso hx⟩
  have hlr : IsLocalRing ((Spec (CommRingCat.of Rh)).presheaf.stalk
      (IsLocalRing.closedPoint Rh : Spec (CommRingCat.of Rh))) :=
    (Spec (CommRingCat.of Rh)).toLocallyRingedSpace.isLocalRing _
  have : Nontrivial ((Spec (CommRingCat.of Rh)).residueField
      (IsLocalRing.closedPoint Rh : Spec (CommRingCat.of Rh))) :=
    let := hlr
    (IsLocalRing.ResidueField.field
      ((Spec (CommRingCat.of Rh)).presheaf.stalk
        (IsLocalRing.closedPoint Rh : Spec (CommRingCat.of Rh)))).toNontrivial
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨RingHom.injective _, hsurj⟩

private def neighborhoodOfFactorization (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    {X : Scheme.{u}} (f : Spec (.of Rh) ⟶ X) (g : X ⟶ S) [Etale g]
    (h : f ≫ g = henselizationTo S s Rh) : ElementaryEtaleNeighborhood S s := by
  let U : EtaleNeighborhood S s :=
    ⟨X, f (IsLocalRing.closedPoint Rh), g,
      (congrArg (fun k : Spec (.of Rh) ⟶ S => k (IsLocalRing.closedPoint Rh)) h).trans
        (henselizationTo_point S s Rh)⟩
  refine ⟨U, elementary_of_toBase_residueFieldMap_isIso U ?_⟩
  apply residueFieldMap_isIso_of_comp f g
  rw [h]
  exact henselizationTo_residueFieldMap S s Rh

private lemma isColimit_of_neighborhood_presentation
    {S : Scheme.{u}} {s : S} {R : CommRingCat.{u}}
    (ι : globalSections S s ⟶ (Functor.const _).obj R)
    {J : Type u} [SmallCategory J] {D : J ⥤ CommRingCat.{u}}
    (c : Cocone D) (hc : IsColimit c) (hR : c.pt = R)
    (obj : J → ElementaryEtaleNeighborhood S s)
    (e : ∀ j, (globalSections S s).obj (op (obj j)) ≅ D.obj j)
    (he : ∀ j, (e j).hom ≫ c.ι.app j ≫ eqToHom hR = ι.app (op (obj j)))
    (hm : ∀ {i j} (f : i ⟶ j), ∃ g : obj j ⟶ obj i,
      (globalSections S s).map g.op ≫ (e j).hom = (e i).hom ≫ D.map f)
    (hcover : ∀ U : ElementaryEtaleNeighborhood S s, ∃ j, Nonempty (obj j ⟶ U)) :
    Nonempty (IsColimit (Cocone.mk R ι)) := by
  subst R
  simp only [eqToHom_refl, Category.comp_id] at he
  let d (t : Cocone (globalSections S s)) : Cocone D := {
    pt := t.pt
    ι := {
      app j := (e j).inv ≫ t.ι.app (op (obj j))
      naturality i j f := by
        obtain ⟨g, hg⟩ := hm f
        dsimp
        simp only [Category.comp_id]
        apply (cancel_epi (e i).hom).1
        rw [← Category.assoc, ← hg, Category.assoc, Iso.hom_inv_id_assoc,
          Iso.hom_inv_id_assoc]
        exact t.w g.op } }
  refine ⟨{ desc t := hc.desc (d t), fac t U := ?_, uniq t m hm' := ?_ }⟩
  · obtain ⟨j, ⟨f⟩⟩ := hcover U.unop
    change ι.app U ≫ hc.desc (d t) = t.ι.app U
    have hi : (globalSections S s).map f.op ≫ ι.app (op (obj j)) = ι.app U := by
      simp
    rw [← hi, Category.assoc, ← he j]
    rw [Category.assoc, hc.fac]
    simp only [d, Iso.hom_inv_id_assoc]
    exact t.w f.op
  · apply hc.hom_ext
    intro j
    rw [hc.fac]
    apply (cancel_epi (e j).hom).1
    simpa [d, ← Category.assoc, he] using hm' (op (obj j))

attribute [local instance] Cardinal.fact_isRegular_aleph0

private lemma isFinitelyPresentable_etale_algebra {A : Type u} [CommRing A]
    (B : CommAlgCat.{u} A) [Algebra.Etale A B] : IsFinitelyPresentable.{u} B := by
  rw [IsFinitelyPresentable, ← isCardinalPresentable_iff_of_isEquivalence B _
    (commAlgCatEquivUnder (CommRingCat.of A)).functor]
  exact CommRingCat.isFinitelyPresentable_under (CommRingCat.of A) _
    ((RingHom.finitePresentation_algebraMap (A := A) (B := B)).mpr inferInstance)

private lemma isColimit_sectionLeg (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (ι : globalSections S s ⟶ (Functor.const _).obj (CommRingCat.of Rh))
    (hι : ∀ U, ι.app (op U) = CommRingCat.ofHom (sectionLeg S s Rh U)) :
    Nonempty (IsColimit (Cocone.mk _ ι)) := by
  classical
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (x := s)
    (U := ⊤) (by simp)
  let A := Γ(S, V)
  let a : Spec A ⟶ S := hV.fromSpec
  let : Algebra A (S.presheaf.stalk s) :=
    (S.presheaf.germ V s hs).hom.toAlgebra
  let : Algebra A Rh := Algebra.compHom Rh (S.presheaf.germ V s hs).hom
  let : IsScalarTower A (S.presheaf.stalk s) Rh := IsScalarTower.of_algebraMap_eq' rfl
  have hα : Spec.map (CommRingCat.ofHom (algebraMap A Rh)) ≫ a =
      henselizationTo S s Rh := by
    have h1 : (CommRingCat.ofHom (algebraMap A Rh) : A ⟶ CommRingCat.of Rh) =
        S.presheaf.germ V s hs ≫
          CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh) := rfl
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap A Rh)) =
        Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh)) ≫
          Spec.map (S.presheaf.germ V s hs) := by
      rw [h1]; exact Spec.map_comp _ _
    rw [h2, Category.assoc]
    change Spec.map _ ≫ hV.fromSpecStalk hs = _
    rw [hV.fromSpecStalk_eq_fromSpecStalk]
    rfl
  have : IsLocalization.AtPrime (S.presheaf.stalk s)
      (hV.primeIdealOf ⟨s, hs⟩).asIdeal := hV.isLocalization_stalk ⟨s, hs⟩
  obtain ⟨J, _, _, pres, hpres⟩ := CommAlgCat.ind_etale_comp
    (CommAlgCat.ind_etale_atPrime A (S.presheaf.stalk s) (hV.primeIdealOf ⟨s, hs⟩).asIdeal)
    (IsLocalRing.IsHenselization.ind_etale_of_universe_le
      (R := S.presheaf.stalk s) (L := IsLocalRing.ResidueField (S.presheaf.stalk s)) (Rh := Rh))
  let F := (commAlgCatEquivUnder A).functor ⋙ Under.forget A
  let D := pres.diag ⋙ F
  let c := F.mapCocone pres.cocone
  have hc : IsColimit c := isColimitOfPreserves F pres.isColimit
  let toS (j : J) : Spec (.of (pres.diag.obj j)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap A (pres.diag.obj j))) ≫ a
  have het (j : J) : Etale (toS j) := by
    have : Algebra.Etale A (pres.diag.obj j) := hpres j
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap A (pres.diag.obj j)))) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).2
        (RingHom.etale_algebraMap.mpr inferInstance)
    dsimp [toS]
    infer_instance
  let liftj (j : J) : Spec (.of Rh) ⟶ Spec (.of (pres.diag.obj j)) :=
    Spec.map (CommRingCat.ofHom (pres.ι.app j).hom.toRingHom)
  have hfac (j : J) : liftj j ≫ toS j = henselizationTo S s Rh := by
    dsimp [liftj, toS]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
    exact hα
  let obj (j : J) : ElementaryEtaleNeighborhood S s :=
    @neighborhoodOfFactorization S s Rh _ _ _ _ _ (liftj j) (toS j) (het j) (hfac j)
  let e (j : J) : (globalSections S s).obj (op (obj j)) ≅ D.obj j :=
    Scheme.ΓSpecIso (.of (pres.diag.obj j))
  have hpt : c.pt = CommRingCat.of Rh := by with_unfolding_all rfl
  have he (j : J) : (e j).hom ≫ c.ι.app j ≫ eqToHom hpt =
      ι.app (op (obj j)) := by
    rw [hι]
    rw [show (e j).hom ≫ c.ι.app j ≫ eqToHom hpt = (e j).hom ≫ c.ι.app j from
      congrArg (fun k => (e j).hom ≫ k)
        (show c.ι.app j ≫ eqToHom hpt = c.ι.app j from Category.comp_id _)]
    have hl := neighborhoodLift_unique S s Rh (obj j) (liftj j) rfl (hfac j)
    have hh := neighborhoodLift_toSpecΓ S s Rh (obj j)
    rw [← hl] at hh
    apply Spec.map_injective
    change Spec.map ((Scheme.ΓSpecIso (.of (pres.diag.obj j))).hom ≫
      CommRingCat.ofHom (pres.ι.app j).hom.toRingHom) = _
    rw [Spec.map_comp]
    change liftj j ≫ (Spec (.of (pres.diag.obj j))).toSpecΓ = _ at hh
    rw [← Scheme.isoSpec_hom, Scheme.isoSpec_Spec_hom] at hh
    exact hh
  apply isColimit_of_neighborhood_presentation ι c hc rfl obj e he
  · intro i j f
    let g : obj j ⟶ obj i := ⟨{
      hom := Spec.map (CommRingCat.ofHom (pres.diag.map f).hom.toRingHom)
      over := by
        change Spec.map _ ≫ (Spec.map _ ≫ a) = Spec.map _ ≫ a
        rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
        congr 2
        apply CommRingCat.hom_ext
        exact (pres.diag.map f).hom.comp_algebraMap
      map_point := by
        change (liftj j ≫ Spec.map (CommRingCat.ofHom
          (pres.diag.map f).hom.toRingHom)) (IsLocalRing.closedPoint Rh) = _
        have hh : liftj j ≫ Spec.map (CommRingCat.ofHom
            (pres.diag.map f).hom.toRingHom) = liftj i := by
          dsimp only [liftj]
          rw [← Spec.map_comp]
          exact congrArg (fun k => Spec.map (F.map k)) (pres.w f)
        rw [hh]
        rfl }⟩
    refine ⟨g, ?_⟩
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (pres.diag.map f).hom.toRingHom)
  · intro U
    obtain ⟨W₀, hW₀, hWa, ⟨wU⟩, hWr⟩ :=
      affine_elementary_refinement_over_open U.obj U.property V hs
    let W : ElementaryEtaleNeighborhood S s := ⟨W₀, hW₀⟩
    let : IsAffine W.obj.scheme := hWa
    have hr : Set.range W.obj.toBase ⊆ Set.range a := by
      rw [show Set.range a = (V : Set S) from hV.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      exact hWr x
    let w : W.obj.scheme ⟶ Spec A := IsOpenImmersion.lift a W.obj.toBase hr
    have hw : w ≫ a = W.obj.toBase := IsOpenImmersion.lift_fac _ _ _
    have : Etale (w ≫ a) := by rw [hw]; infer_instance
    have : Etale w := Etale.of_comp w a
    let t : A ⟶ Γ(W.obj.scheme, ⊤) := (Scheme.ΓSpecIso A).inv ≫ w.appTop
    have ht : W.obj.scheme.toSpecΓ ≫ Spec.map t = w := by
      dsimp only [t]
      rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
        Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    have ht' : Spec.map t = W.obj.scheme.isoSpec.inv ≫ w := by
      rw [← ht, Scheme.isoSpec_inv_toSpecΓ_assoc]
    let : Algebra A Γ(W.obj.scheme, ⊤) := t.hom.toAlgebra
    have : Algebra.Etale A Γ(W.obj.scheme, ⊤) := by
      apply RingHom.etale_algebraMap.mp
      apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
      rw [ht']
      infer_instance
    have hlin : (sectionLeg S s Rh W).comp t.hom = algebraMap A Rh := by
      suffices h : CommRingCat.ofHom ((sectionLeg S s Rh W).comp t.hom) =
          CommRingCat.ofHom (algebraMap A Rh) from congrArg CommRingCat.Hom.hom h
      apply Spec.map_injective
      apply (cancel_mono a).mp
      have hsplit : Spec.map (CommRingCat.ofHom ((sectionLeg S s Rh W).comp t.hom)) =
          Spec.map (CommRingCat.ofHom (sectionLeg S s Rh W)) ≫ Spec.map t := by
        rw [show (CommRingCat.ofHom ((sectionLeg S s Rh W).comp t.hom) :
            A ⟶ CommRingCat.of Rh) = t ≫ CommRingCat.ofHom (sectionLeg S s Rh W) from rfl,
          Spec.map_comp]
        rfl
      rw [hsplit, Category.assoc, ← neighborhoodLift_toSpecΓ]
      calc
        _ = neighborhoodLift S s Rh W ≫ (W.obj.scheme.toSpecΓ ≫ Spec.map t) ≫ a :=
          Category.assoc _ _ _
        _ = henselizationTo S s Rh := by rw [ht, hw, neighborhoodLift_base]
        _ = _ := hα.symm
    let β : CommAlgCat.of A Γ(W.obj.scheme, ⊤) ⟶ CommAlgCat.of A Rh :=
      CommAlgCat.ofHom
        { toRingHom := sectionLeg S s Rh W
          commutes' := fun x => RingHom.congr_fun hlin x }
    have : IsFinitelyPresentable.{u} (CommAlgCat.of A Γ(W.obj.scheme, ⊤)) :=
      isFinitelyPresentable_etale_algebra _
    obtain ⟨j, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit β
    let k : obj j ⟶ W := ⟨{
      hom := Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ W.obj.scheme.isoSpec.inv
      over := by
        change (Spec.map _ ≫ W.obj.scheme.isoSpec.inv) ≫ W.obj.toBase = toS j
        rw [← hw, Category.assoc, ← Category.assoc W.obj.scheme.isoSpec.inv,
          ← ht', ← Spec.map_comp_assoc]
        change Spec.map (CommRingCat.ofHom (g.hom.toRingHom.comp t.hom)) ≫ a = _
        have hgA : g.hom.toRingHom.comp t.hom = algebraMap A (pres.diag.obj j) :=
          g.hom.comp_algebraMap
        rw [hgA]
      map_point := by
        change (liftj j ≫ (Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
          W.obj.scheme.isoSpec.inv)) (IsLocalRing.closedPoint Rh) = _
        have hh : liftj j ≫ Spec.map (CommRingCat.ofHom g.hom.toRingHom) =
            Spec.map (CommRingCat.ofHom (sectionLeg S s Rh W)) := by
          dsimp only [liftj]
          rw [← Spec.map_comp]
          exact congrArg (fun k => Spec.map (F.map k)) hg
        rw [← Category.assoc, hh, ← neighborhoodLift_toSpecΓ,
          Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
        exact neighborhoodLift_point S s Rh W }⟩
    exact ⟨j, ⟨k ≫ ⟨wU⟩⟩⟩

/-- **Stacks Project, Tag 05KS.** The opposite of the category of elementary
étale neighborhoods of a point is filtered. -/
@[stacks 05KS "the indexing category is filtered",
  stacks 04HY "the henselization is the colimit of O(U) over the étale neighbourhoods with κ(s)",
  ega "IV 18.6.3" "more general"]
instance instIsFilteredOppositeElementaryEtaleNeighborhood
    (S : Scheme.{u}) (s : S) :
    IsFiltered (ElementaryEtaleNeighborhood S s)ᵒᵖ := by
  let C := ElementaryEtaleNeighborhood S s
  let : IsCofiltered C := {
    nonempty := by
      let U : EtaleNeighborhood S s := ⟨S, s, 𝟙 S, rfl⟩
      have hU : U.IsElementary := by
        change IsIso ((S.residueFieldCongr rfl).inv ≫
          Scheme.Hom.residueFieldMap (𝟙 S) s)
        rw [Scheme.residueFieldMap_id]
        simpa using (inferInstance : IsIso (𝟙 (S.residueField s)))
      exact ⟨⟨U, hU⟩⟩
    cone_objs U V := by
      obtain ⟨W, ⟨f, g⟩⟩ := exists_elementary_common_refinement U V
      exact ⟨W, f, g, trivial⟩
    cone_maps U V f g := by
      let : IsIso V.obj.residueFieldMap := V.property
      let f₀ : EtaleNeighborhood.Hom U.obj V.obj := f.hom
      let g₀ : EtaleNeighborhood.Hom U.obj V.obj := g.hom
      have hf := residueFieldMap_naturality U.obj V.obj f₀
      have hg := residueFieldMap_naturality U.obj V.obj g₀
      have hκ : (V.obj.scheme.residueFieldCongr f₀.map_point).inv ≫
          f₀.hom.residueFieldMap U.obj.point =
        (V.obj.scheme.residueFieldCongr g₀.map_point).inv ≫
          g₀.hom.residueFieldMap U.obj.point :=
        (cancel_epi V.obj.residueFieldMap).1 (hf.symm.trans hg)
      obtain ⟨W, h, hfg, hW⟩ :=
        exists_elementary_equalizing_refinement U.property f₀ g₀ hκ
      refine ⟨⟨W, hW⟩, ⟨h⟩, ?_⟩
      apply InducedCategory.hom_ext
      change h ≫ f.hom = h ≫ g.hom
      exact hfg
  }
  exact (isFiltered_op_iff_isCofiltered C).2 inferInstance

/-- The canonical map from the ring of global sections of each elementary étale neighbourhood of
`(S, s)` to a henselization `Rh` of the local ring at `s`: it is the composite of the germ at the
distinguished point with the lift of that local ring to `Rh`. -/
private def sectionLegCocone (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh] :
    globalSections S s ⟶ (Functor.const _).obj (CommRingCat.of Rh) where
  app U := CommRingCat.ofHom (sectionLeg S s Rh U.unop)
  naturality := by
    intro U V f
    apply CommRingCat.hom_ext
    change (sectionLeg S s Rh V.unop).comp
        ((globalSections S s).map (Opposite.op f.unop)).hom =
          sectionLeg S s Rh U.unop
    exact (sectionLeg_naturality S s Rh U.unop V.unop f.unop).symm

/-- Each leg of `AlgebraicGeometry.sectionLegCocone` factors through the local ring at the
distinguished point by a local homomorphism over the local ring of the base. -/
private lemma sectionLegCocone_isOverStalk (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (U : (ElementaryEtaleNeighborhood S s)ᵒᵖ) :
    IsOverStalk S s Rh U.unop ((sectionLegCocone S s Rh).app U).hom :=
  ⟨stalkLift S s Rh U.unop, stalkLift_isLocalHom S s Rh U.unop,
    stalkLift_base S s Rh U.unop, rfl⟩

/-- `AlgebraicGeometry.sectionLegCocone` is the only map which factors through the local rings at
the distinguished points: such a factorization is unique by the universal property of the
henselization. -/
private lemma sectionLegCocone_unique (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (ι' : globalSections S s ⟶ (Functor.const _).obj (CommRingCat.of Rh))
    (hover : ∀ U, IsOverStalk S s Rh U.unop (ι'.app U).hom) :
    ι' = sectionLegCocone S s Rh := by
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  obtain ⟨g, hg, hbase, hfac⟩ := hover U
  have : IsLocalHom g := hg
  rwa [stalkLift_unique S s Rh U.unop g hbase] at hfac

/-- `AlgebraicGeometry.sectionLegCocone` is a colimit cocone. -/
private lemma nonempty_isColimit_sectionLegCocone (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh] :
    Nonempty (IsColimit (Cocone.mk _ (sectionLegCocone S s Rh))) :=
  isColimit_sectionLeg S s Rh (sectionLegCocone S s Rh) (fun _ => rfl)

-- The index binder of each stalk-factorization condition carries its type explicitly: left to
-- inference, `U.unop` blocks on a metavariable, and unifying `op ?U` with `U` then unfolds the
-- whole `Scheme.Γ` forgetful chain, which costs about 135000 heartbeats per occurrence.
/-- **Stacks Project, Tag 05KS.** A henselization of the local ring of a
scheme at a point is a colimit of the rings of global sections of its
elementary étale neighborhoods. -/
@[stacks 05KS "the henselization is the colimit",
  stacks 04HY "the henselization is the colimit of O(U) over the étale neighbourhoods with κ(s)"]
lemma isColimit_globalSections (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh] :
    ∃ ι : globalSections S s ⟶
        (Functor.const _).obj (CommRingCat.of Rh),
      (∀ U x, IsLocalRing.residue Rh ((ι.app U).hom x) =
        henselizationResidueFieldMap S s Rh
          (elementaryEtaleAugmentation S s U.unop x)) ∧
      (∀ U : (ElementaryEtaleNeighborhood S s)ᵒᵖ,
        IsOverStalk S s Rh U.unop (ι.app U).hom) ∧
      (∀ ι' : globalSections S s ⟶ (Functor.const _).obj (CommRingCat.of Rh),
        (∀ U x, IsLocalRing.residue Rh ((ι'.app U).hom x) =
          henselizationResidueFieldMap S s Rh
            (elementaryEtaleAugmentation S s U.unop x)) →
        (∀ U : (ElementaryEtaleNeighborhood S s)ᵒᵖ,
          IsOverStalk S s Rh U.unop (ι'.app U).hom) → ι' = ι) ∧
      Nonempty (IsColimit (Cocone.mk _ ι)) :=
  ⟨sectionLegCocone S s Rh,
    fun U x => sectionLeg_residue S s Rh U.unop x,
    sectionLegCocone_isOverStalk S s Rh,
    fun ι' _ hover => sectionLegCocone_unique S s Rh ι' hover,
    nonempty_isColimit_sectionLegCocone S s Rh⟩

end AlgebraicGeometry
