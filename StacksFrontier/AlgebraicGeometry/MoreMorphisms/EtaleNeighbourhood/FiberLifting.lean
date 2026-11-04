module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.ColimitPresentation.FinitePresentation
public import StacksFrontier.RingTheory.Etale.Lifting

/-!
# Lifting an étale neighbourhood of a point of a fibre

Let `f : X ⟶ S` and let `x` be a point of `X`. An étale neighbourhood of the point `f.asFiber x`
of the scheme-theoretic fibre `f.fiber (f x)` is, after shrinking, the fibre of an étale
neighbourhood of `x` in `X`: there are an étale neighbourhood `U` of `x` and an open immersion
from the fibre of `U.toBase ≫ f` over `f x` into the given neighbourhood, compatible with the
maps down to `f.fiber (f x)`.

## Main results

* `AlgebraicGeometry.exists_etaleNeighborhood_fiber_openImmersion`: an étale neighbourhood of a
  point of a fibre admits an open subneighbourhood lifted from the total space.

## Implementation notes

The point of the fibre of the lifted neighbourhood and its canonical map to the original fibre
are included explicitly. The equality after composing with the fibre inclusion characterises
this canonical map, because the fibre inclusion is a monomorphism. The resulting map to the
given neighbourhood is an open immersion over the original fibre.

The affine argument first lifts the étale algebra from the fibre to the localisation at the base
point, across the surjection onto the residue field. It then descends this lift to a principal
localisation, which is why the filtered system of principal localisations of a ring at a
submonoid and its colimit are built here. The resulting pushout squares identify the chosen
affine neighbourhood with the fibre of the lifted étale scheme.

## References

* [Stacks Project, Tag 0CAS](https://stacks.math.columbia.edu/tag/0CAS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Algebra TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### The principal localisations of a ring as a filtered system -/

namespace LocalizationAwayCocone

variable (R : Type u) [CommRing R] (M : Submonoid R)

/-- The index type of the system of principal localisations: the elements of the submonoid. -/
private abbrev Idx := M

/-- The index type is ordered by divisibility. -/
@[instance_reducible]
private def indexPreorder : Preorder (Idx R M) where
  le a b := (a : R) ∣ (b : R)
  le_refl a := dvd_refl _
  le_trans a b c := dvd_trans

attribute [local instance] indexPreorder

/-- Divisibility on the submonoid is directed, since the submonoid is closed under products. -/
private theorem indexDirected : IsDirected (Idx R M) (· ≤ ·) := by
  constructor; intro a b
  exact ⟨⟨(a : R) * (b : R), M.mul_mem a.property b.property⟩,
    dvd_mul_right _ _, dvd_mul_left _ _⟩

attribute [local instance] indexDirected

/-- The index type is nonempty: it contains `1`. -/
private theorem indexNonempty : Nonempty (Idx R M) := ⟨⟨1, M.one_mem⟩⟩

attribute [local instance] indexNonempty

/-- A divisor of `b` becomes a unit in the localisation away from `b`. -/
private theorem unit_of_le (a b : Idx R M) (h : a ≤ b) :
    IsUnit (algebraMap R (Localization.Away (b : R)) (a : R)) := by
  have hb : IsUnit (algebraMap R (Localization.Away (b : R)) (b : R)) :=
    IsLocalization.Away.algebraMap_isUnit (b : R)
  obtain ⟨c, hc⟩ := h
  have heq : algebraMap R (Localization.Away (b : R)) (b : R) =
      algebraMap R (Localization.Away (b : R)) (a : R) *
        algebraMap R (Localization.Away (b : R)) c := by
    rw [← map_mul, ← hc]
  exact isUnit_of_mul_isUnit_left (heq ▸ hb)

/-- The transition map of the system, from the localisation away from `a` to the localisation
away from a multiple `b` of `a`. -/
private noncomputable def trans (a b : Idx R M) (h : a ≤ b) :
    Localization.Away (a : R) →+* Localization.Away (b : R) :=
  IsLocalization.Away.lift (S := Localization.Away (a : R)) (a : R)
    (unit_of_le R M a b h)

/-- The transition maps are maps of `R`-algebras. -/
private theorem trans_algebraMap (a b : Idx R M) (h : a ≤ b) (r : R) :
    trans R M a b h (algebraMap R (Localization.Away (a : R)) r) =
      algebraMap R (Localization.Away (b : R)) r := by
  unfold trans
  rw [IsLocalization.Away.lift_eq]

/-- Two maps out of a principal localisation which agree on `R` are equal. -/
private theorem away_ringHom_ext {a : R} {T : Type*} [CommRing T]
    {φ ψ : Localization.Away a →+* T}
    (h : ∀ r, φ (algebraMap R (Localization.Away a) r) = ψ (algebraMap R (Localization.Away a) r)) :
    φ = ψ :=
  IsLocalization.ringHom_ext (Submonoid.powers a) (RingHom.ext h)

/-- The filtered system of principal localisations of `R` at the elements of `M`. -/
private noncomputable def diag : (Idx R M) ⥤ CommRingCat.{u} where
  obj a := CommRingCat.of (Localization.Away (a : R))
  map {a b} h := CommRingCat.ofHom (trans R M a b h.le)
  map_id a := CommRingCat.hom_ext <| away_ringHom_ext R fun r => by
    change trans R M a a le_rfl _ = _
    rw [trans_algebraMap]
    rfl
  map_comp {a b c} f g := CommRingCat.hom_ext <| away_ringHom_ext R fun r => by
    change trans R M a c (f.le.trans g.le) _ = (trans R M b c g.le) ((trans R M a b f.le) _)
    rw [trans_algebraMap, trans_algebraMap, trans_algebraMap]

/-- The leg of the cocone at `a`: the map from the localisation away from `a` to the localisation
at `M`. -/
private noncomputable def leg (a : Idx R M) :
    Localization.Away (a : R) →+* Localization M :=
  IsLocalization.Away.lift (S := Localization.Away (a : R)) (a : R)
    (IsLocalization.map_units (Localization M) a)

/-- The legs of the cocone are maps of `R`-algebras. -/
private theorem leg_algebraMap (a : Idx R M) (r : R) :
    leg R M a (algebraMap R (Localization.Away (a : R)) r) =
      algebraMap R (Localization M) r := by
  unfold leg
  rw [IsLocalization.Away.lift_eq]

/-- The cocone on the system of principal localisations with vertex the localisation at `M`. -/
private noncomputable def coc : Cocone (diag R M) where
  pt := CommRingCat.of (Localization M)
  ι :=
    { app := fun a => CommRingCat.ofHom (leg R M a)
      naturality := by
        intro a b h
        apply CommRingCat.hom_ext
        change (leg R M b).comp (trans R M a b h.le) =
          (leg R M a).comp (RingHom.id _)
        refine away_ringHom_ext R fun r => ?_
        change (leg R M b) ((trans R M a b h.le)
          (algebraMap R (Localization.Away (a : R)) r)) =
          (leg R M a) ((RingHom.id _) (algebraMap R (Localization.Away (a : R)) r))
        rw [trans_algebraMap, leg_algebraMap, RingHom.id_apply, leg_algebraMap] }

/-- The structure map from `R` to the vertex of an arbitrary cocone on the system. -/
private noncomputable def coconeStr {s : Cocone (diag R M)} : R →+* s.pt :=
  (s.ι.app ⟨1, M.one_mem⟩).hom.comp
    (algebraMap R (Localization.Away ((⟨1, M.one_mem⟩ : Idx R M) : R)))

/-- Every leg of a cocone on the system restricts to the same structure map on `R`. -/
private theorem leg_app_str {s : Cocone (diag R M)} (a : Idx R M) (r : R) :
    (s.ι.app a).hom (algebraMap R (Localization.Away (a : R)) r) = coconeStr R M r := by
  set o : Idx R M := ⟨1, M.one_mem⟩ with ho
  let : CommRing (Localization.Away (o : R)) := CommRingCat.commRing ((diag R M).obj o)
  let : CommRing (Localization.Away (a : R)) := CommRingCat.commRing ((diag R M).obj a)
  have hoa : o ≤ a := one_dvd _
  have hnat : (s.ι.app a).hom.comp (trans R M o a hoa) = (s.ι.app o).hom := by
    have hn := s.ι.naturality (CategoryTheory.homOfLE hoa)
    simp only [CategoryTheory.Functor.const_obj_obj, CategoryTheory.Functor.const_obj_map,
      CategoryTheory.Category.comp_id] at hn
    exact congrArg CommRingCat.Hom.hom hn
  have hr := RingHom.congr_fun hnat (algebraMap R (Localization.Away (o : R)) r)
  change (s.ι.app a).hom ((trans R M o a hoa)
    (algebraMap R (Localization.Away (o : R)) r)) =
    (s.ι.app o).hom (algebraMap R (Localization.Away (o : R)) r) at hr
  show (s.ι.app a).hom (algebraMap R (Localization.Away (a : R)) r) =
    (s.ι.app o).hom (algebraMap R (Localization.Away (o : R)) r)
  rw [← trans_algebraMap R M o a hoa r]
  exact hr

/-- The elements of `M` become units under the structure map of any cocone on the system. -/
private theorem coconeStr_units {s : Cocone (diag R M)} (a : M) :
    IsUnit (coconeStr R M (s := s) (a : R)) := by
  rw [← leg_app_str R M a (a : R)]
  exact IsUnit.map (s.ι.app a).hom
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a : R)) (a : R))

/-- The map from the localisation at `M` to the vertex of an arbitrary cocone on the system. -/
private noncomputable def descMap (s : Cocone (diag R M)) :
    Localization M →+* s.pt :=
  IsLocalization.lift (M := M) (g := coconeStr R M (s := s)) (coconeStr_units R M (s := s))

/-- The descent map is a map of `R`-algebras. -/
private theorem descMap_algebraMap (s : Cocone (diag R M)) (r : R) :
    descMap R M s (algebraMap R (Localization M) r) = coconeStr R M (s := s) r := by
  unfold descMap
  rw [IsLocalization.lift_eq]

/-- The localisation at `M` is the colimit of the principal localisations at the elements
of `M`. -/
private noncomputable def cocIsColimit : IsColimit (coc R M) :=
  IsColimit.mk (fun s => CommRingCat.ofHom (descMap R M s))
    (by
      intro s a
      apply CommRingCat.hom_ext
      change (descMap R M s).comp (leg R M a) = (s.ι.app a).hom
      refine away_ringHom_ext R fun r => ?_
      change (descMap R M s) ((leg R M a) (algebraMap R (Localization.Away (a : R)) r)) =
        (s.ι.app a).hom (algebraMap R (Localization.Away (a : R)) r)
      rw [leg_algebraMap, descMap_algebraMap, leg_app_str])
    (by
      intro s m hm
      apply CommRingCat.hom_ext
      change m.hom = descMap R M s
      apply IsLocalization.ringHom_ext (M := M) (S := Localization M)
      ext r
      change m.hom (algebraMap R (Localization M) r) =
        descMap R M s (algebraMap R (Localization M) r)
      rw [descMap_algebraMap]
      have hmo := hm ⟨1, M.one_mem⟩
      have hmr := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hmo)
        (algebraMap R (Localization.Away ((⟨1, M.one_mem⟩ : Idx R M) : R)) r)
      change m.hom (leg R M ⟨1, M.one_mem⟩ _) = _ at hmr
      rw [leg_algebraMap] at hmr
      rw [hmr]
      rfl)

end LocalizationAwayCocone

attribute [local instance] LocalizationAwayCocone.indexPreorder
  LocalizationAwayCocone.indexDirected LocalizationAwayCocone.indexNonempty

/-! ### Lifting an étale algebra across a localisation and a surjection -/

/-- **An étale algebra over a localisation of `R` descends to an étale algebra over `R`.** Given
`L` a localisation of `R` at a submonoid `M` and `T` an étale `L`-algebra, there is an étale
`R`-algebra `E` with `T = E ⊗_R L`, exhibited as a pushout square.

This is the ring-theoretic content of the step the Stacks proofs in this area take without
comment — "we may replace `S` by an elementary étale neighbourhood finitely many times, and we
may also replace `S` by `Spec 𝒪_{S,s}` at any point of the proof". Composing those two moves
needs exactly this descent. -/
public lemma exists_etale_pushout_of_localization
    (R L T : Type u) [CommRing R] [CommRing L] [CommRing T]
    [Algebra R L] (M : Submonoid R) [IsLocalization M L]
    (f : L →+* T) (hf : f.Etale) :
    ∃ (E : CommRingCat.{u}) (a : CommRingCat.of R ⟶ E)
      (b : E ⟶ CommRingCat.of T),
      CommRingCat.etale a ∧ IsPushout (CommRingCat.ofHom (algebraMap R L)) a
        (CommRingCat.ofHom f) b := by
  let e := IsLocalization.algEquiv M (Localization M) L
  let c := (LocalizationAwayCocone.coc R M).extend e.toRingEquiv.toCommRingCatIso.hom
  have hc : IsColimit c :=
    IsColimit.ofIsoColimit (LocalizationAwayCocone.cocIsColimit R M)
      (Cocone.ext e.toRingEquiv.toCommRingCatIso (by intro j; rfl))
  obtain ⟨j, E, a, b, hpo, ha⟩ :=
    exists_isPushout_etale hc (CommRingCat.ofHom f) hf
  let r : R := j
  let t : Localization.Away r →+* L := (c.ι.app j).hom
  have ht (y : R) : t (algebraMap R (Localization.Away r) y) = algebraMap R L y := by
    show e (LocalizationAwayCocone.leg R M j (algebraMap R (Localization.Away r) y)) = _
    rw [LocalizationAwayCocone.leg_algebraMap, e.commutes]
  have hunits : (Submonoid.powers r).map (algebraMap R L) ≤ IsUnit.submonoid L := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [map_pow]
    exact (IsLocalization.map_units L j).pow n
  have : IsLocalization ((Submonoid.powers r).map (algebraMap R L)) L :=
    IsLocalization.self hunits
  have hbase := CommRingCat.isPushout_of_isLocalization (algebraMap R L) t
    (by ext y; exact ht y) (Submonoid.powers r)
  have hfull := hbase.flip.paste_horiz hpo.flip
  refine ⟨E, CommRingCat.ofHom (algebraMap R (Localization.Away r)) ≫ a, b, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway r)) ha
  · simpa using hfull.flip

/-- An étale algebra over a quotient of `R` lifts to an étale algebra over `R`. -/
private lemma exists_etale_pushout_of_surjective
    {R S T : CommRingCat.{u}} (q : R ⟶ S) (hq : Function.Surjective q.hom)
    (f : S ⟶ T) (hf : CommRingCat.etale f) :
    ∃ (E : CommRingCat.{u}) (a : R ⟶ E) (b : E ⟶ T),
      CommRingCat.etale a ∧ IsPushout q a f b := by
  algebraize [q.hom, f.hom, (q ≫ f).hom]
  have : IsScalarTower R S T := .of_algebraMap_eq fun _ => rfl
  have : Algebra.Etale S T := hf
  obtain ⟨E, _, _, hE, b, hb, hker⟩ := etale_lift_along_surjection R S T hq
  refine ⟨CommRingCat.of E, CommRingCat.ofHom (algebraMap R E),
    CommRingCat.ofHom b.toRingHom, RingHom.etale_algebraMap.mpr hE, ?_⟩
  apply Stacks.ColimitPresentation.FiniteStage.isPushout_of_surjective _ _ _ _ _ hq hb hker
  ext r
  exact (b.commutes r).symm

/-- An étale algebra over a quotient of a localisation of `R` lifts to an étale algebra
over `R`. -/
private lemma exists_etale_pushout_of_localization_surjective
    (R L : Type u) [CommRing R] [CommRing L] [Algebra R L]
    (M : Submonoid R) [IsLocalization M L]
    {S T : CommRingCat.{u}} (q : CommRingCat.of L ⟶ S)
    (hq : Function.Surjective q.hom) (f : S ⟶ T) (hf : CommRingCat.etale f) :
    ∃ (E : CommRingCat.{u}) (a : CommRingCat.of R ⟶ E) (b : E ⟶ T),
      CommRingCat.etale a ∧
      IsPushout (CommRingCat.ofHom (algebraMap R L) ≫ q) a f b := by
  obtain ⟨E', a', b', ha', hp'⟩ := exists_etale_pushout_of_surjective q hq f hf
  obtain ⟨E, a, b, ha, hp⟩ := exists_etale_pushout_of_localization R L E' M a'.hom ha'
  exact ⟨E, a, b ≫ b', ha, hp.paste_horiz hp'⟩

/-- An étale algebra over `B ⊗[R] K`, with `K` a quotient of a localisation `L` of `R`, comes by
base change from an étale algebra over `B`. -/
private lemma exists_etale_pushout_of_tensor_localization_surjective
    (R B L K : Type u) [CommRing R] [CommRing B] [CommRing L] [CommRing K]
    [Algebra R B] [Algebra R L] [Algebra R K] [Algebra L K] [IsScalarTower R L K]
    (M : Submonoid R) [IsLocalization M L]
    (hq : Function.Surjective (algebraMap L K))
    {C : CommRingCat.{u}} (f : CommRingCat.of (B ⊗[R] K) ⟶ C)
    (hf : CommRingCat.etale f) :
    ∃ (E : CommRingCat.{u}) (a : CommRingCat.of B ⟶ E) (b : E ⟶ C),
      CommRingCat.etale a ∧
      IsPushout (CommRingCat.ofHom (algebraMap B (B ⊗[R] K))) a f b := by
  let q : B ⊗[R] L →ₐ[R] B ⊗[R] K :=
    Algebra.TensorProduct.map (AlgHom.id R B) (IsScalarTower.toAlgHom R L K)
  have hq' : Function.Surjective q :=
    Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hq
  obtain ⟨E, a, b, ha, hp⟩ := exists_etale_pushout_of_localization_surjective
    B (B ⊗[R] L) (Algebra.algebraMapSubmonoid B M) (CommRingCat.ofHom q.toRingHom)
      hq' f hf
  have heq : CommRingCat.ofHom (algebraMap B (B ⊗[R] L)) ≫
      CommRingCat.ofHom q.toRingHom = CommRingCat.ofHom (algebraMap B (B ⊗[R] K)) := by
    ext y
    simp [q, Algebra.TensorProduct.algebraMap_apply]
  exact ⟨E, a, b, ha, heq ▸ hp⟩

/-! ### Lifting the neighbourhood -/

/-- A pullback square stays a pullback square after composing both legs on the right with a
monomorphism. -/
private lemma isPullback_comp_mono {P X Y Z T : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (i : Z ⟶ T) [Mono i] :
    IsPullback a b (f ≫ i) (g ≫ i) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono f g i h.cone h.isLimit)

/-- The affine heart of the lifting: an étale morphism to the fibre `f.fiber s` is, on an affine
open, the fibre of an étale morphism to `X`. -/
private lemma exists_etale_fiber_pullback
    {X S V : Scheme.{u}} (f : X ⟶ S) (s : S)
    (p : V ⟶ f.fiber s) [Etale p] (v : V) :
    ∃ (U : Scheme.{u}) (g : U ⟶ X) (W : Scheme.{u}) (j : W ⟶ V)
      (w : W) (b : W ⟶ U) (t : W ⟶ Spec (S.residueField s)),
      Etale g ∧ IsOpenImmersion j ∧ j w = v ∧
      b ≫ g = j ≫ p ≫ f.fiberι s ∧
      IsPullback b t (g ≫ f) (S.fromSpecResidueField s) := by
  let x : X := f.fiberι s (p v)
  have hx : f x = s := by
    show f (f.fiberι s (p v)) = s
    rw [← Scheme.Hom.comp_apply, f.fiber_fac]
    simp
  obtain ⟨SA, hSA, hsA, _⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (x := s) (U := ⊤) trivial
  obtain ⟨XB, hXB, hxB, hBA⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := x) (U := f ⁻¹ᵁ SA) (by change f x ∈ SA; rwa [hx])
  let A := Γ(S, SA)
  let B := Γ(X, XB)
  let L := S.presheaf.stalk s
  let K := S.residueField s
  let a : A ⟶ B := f.appLE SA XB hBA
  let l : A ⟶ L := S.presheaf.germ SA s hsA
  let q : L ⟶ K := S.residue s
  let : Algebra A B := a.hom.toAlgebra
  let : Algebra A L := l.hom.toAlgebra
  let : Algebra L K := q.hom.toAlgebra
  let : Algebra A K := (l ≫ q).hom.toAlgebra
  have : IsScalarTower A L K := .of_algebraMap_eq fun _ => rfl
  let M := (hSA.primeIdealOf ⟨s, hsA⟩).asIdeal.primeCompl
  have : IsLocalization M L := hSA.isLocalization_stalk ⟨s, hsA⟩
  let F := B ⊗[A] K
  let α : Spec (.of F) ⟶ Spec B := Spec.map (CommRingCat.ofHom (algebraMap B F))
  let β : Spec (.of F) ⟶ Spec K :=
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := K)).toRingHom)
  have hTensor : IsPullback α β (Spec.map a) (Spec.map (l ≫ q)) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B K)
  have ha : Spec.map a ≫ hSA.fromSpec = hXB.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hSA hXB hBA
  have hq : Spec.map (l ≫ q) ≫ hSA.fromSpec = S.fromSpecResidueField s := by
    rw [Spec.map_comp, Category.assoc]
    show Spec.map (S.residue s) ≫ hSA.fromSpecStalk hsA = _
    rw [hSA.fromSpecStalk_eq_fromSpecStalk hsA]
    rfl
  have hF : IsPullback α β (hXB.fromSpec ≫ f) (S.fromSpecResidueField s) := by
    simpa only [ha, hq] using isPullback_comp_mono hTensor hSA.fromSpec
  let k : Spec (.of F) ⟶ f.fiber s :=
    pullback.lift (α ≫ hXB.fromSpec) β (by simpa only [Category.assoc] using hF.w)
  have hkι : k ≫ f.fiberι s = α ≫ hXB.fromSpec := pullback.lift_fst ..
  have hkβ : k ≫ f.fiberToSpecResidueField s = β := pullback.lift_snd ..
  have hk : IsPullback α k hXB.fromSpec (f.fiberι s) := by
    apply IsPullback.of_bot (h₃₁ := S.fromSpecResidueField s)
      (v₂₁ := f.fiberToSpecResidueField s)
    · simpa only [hkβ] using hF
    · exact hkι.symm
    · exact IsPullback.of_hasPullback _ _
  have : IsOpenImmersion k :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hk inferInstance
  obtain ⟨xB, hxB'⟩ : ∃ xB, hXB.fromSpec xB = x := by
    show x ∈ Set.range hXB.fromSpec
    rw [hXB.range_fromSpec]
    exact hxB
  obtain ⟨z, hzB, hzx⟩ := Scheme.exists_preimage_of_isPullback hk xB (p v) hxB'
  have hv : v ∈ p ⁻¹ᵁ k.opensRange := ⟨z, hzx⟩
  obtain ⟨C, j, hj, hvj, hjrange⟩ := Scheme.exists_affine_mem_range_and_range_subset hv
  have : IsOpenImmersion j := hj
  obtain ⟨w, hw⟩ := hvj
  have hjp : Set.range (j ≫ p) ⊆ Set.range k := by
    rintro _ ⟨c, rfl⟩
    exact hjrange ⟨c, rfl⟩
  let η : Spec C ⟶ Spec (.of F) := IsOpenImmersion.lift k (j ≫ p) hjp
  have hη : η ≫ k = j ≫ p := IsOpenImmersion.lift_fac ..
  have : Etale (η ≫ k) := hη ▸ inferInstance
  have : Etale η := Etale.of_comp η k
  let c : CommRingCat.of F ⟶ C := Spec.preimage η
  have hc : CommRingCat.etale c := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    simpa only [c, Spec.map_preimage] using (inferInstance : Etale η)
  obtain ⟨E, e, d, he, hpush⟩ := exists_etale_pushout_of_tensor_localization_surjective
    A B L K M (S.residue_surjective s) c hc
  have : Etale (Spec.map e) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he
  have hC : IsPullback (Spec.map d) η (Spec.map e) α := by
    simpa only [c, Spec.map_preimage] using
      (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).flip
  refine ⟨Spec E, Spec.map e ≫ hXB.fromSpec, Spec C, j, w, Spec.map d,
    η ≫ β, inferInstance, hj, hw, ?_, ?_⟩
  · calc
      Spec.map d ≫ Spec.map e ≫ hXB.fromSpec = η ≫ α ≫ hXB.fromSpec := by
        rw [← Category.assoc, hC.w, Category.assoc]
      _ = η ≫ k ≫ f.fiberι s := by rw [hkι]
      _ = j ≫ p ≫ f.fiberι s := by rw [← Category.assoc, hη, Category.assoc]
  · simpa only [Category.assoc] using hC.paste_vert hF

/-- **Stacks Project, Tag 0CAS.** An étale neighborhood on a fiber can be
refined by an open immersion from the fiber of an étale neighborhood on the
total space. -/
@[stacks 0CAS]
public theorem exists_etaleNeighborhood_fiber_openImmersion
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (V : EtaleNeighborhood (f.fiber (f x)) (f.asFiber x)) :
    ∃ (U : EtaleNeighborhood X x)
      (u : (U.toBase ≫ f).fiber (f x))
      (p : (U.toBase ≫ f).fiber (f x) ⟶ f.fiber (f x))
      (h : (U.toBase ≫ f).fiber (f x) ⟶ V.scheme),
      (U.toBase ≫ f).fiberι (f x) u = U.point ∧
      p ≫ f.fiberι (f x) = (U.toBase ≫ f).fiberι (f x) ≫ U.toBase ∧
      Etale p ∧
      p u = f.asFiber x ∧
      h ≫ V.toBase = p ∧
      h u = V.point ∧
      IsOpenImmersion h := by
  obtain ⟨T, g, W, j, w, b, t, hg, hj, hw, hb, hpb⟩ :=
    exists_etale_fiber_pullback f (f x) V.toBase V.point
  have : Etale g := hg
  have : IsOpenImmersion j := hj
  have hpoint : g (b w) = x := by
    rw [← Scheme.Hom.comp_apply, hb]
    simp only [Scheme.Hom.comp_apply, hw, V.map_point, Scheme.Hom.fiberι_asFiber]
  let U : EtaleNeighborhood X x :=
    { scheme := T, point := b w, toBase := g, map_point := hpoint }
  let e : W ≅ (U.toBase ≫ f).fiber (f x) := hpb.isoPullback
  let u : (U.toBase ≫ f).fiber (f x) := e.hom w
  let h : (U.toBase ≫ f).fiber (f x) ⟶ V.scheme := e.inv ≫ j
  let p : (U.toBase ≫ f).fiber (f x) ⟶ f.fiber (f x) := h ≫ V.toBase
  have hleft : e.hom ≫ (U.toBase ≫ f).fiberι (f x) = b :=
    hpb.isoPullback_hom_fst
  have hright : e.inv ≫ b = (U.toBase ≫ f).fiberι (f x) :=
    hpb.isoPullback_inv_fst
  refine ⟨U, u, p, h, ?_, ?_, inferInstance, ?_, rfl, ?_, inferInstance⟩
  · show (U.toBase ≫ f).fiberι (f x) (e.hom w) = b w
    rw [← Scheme.Hom.comp_apply, hleft]
  · show (e.inv ≫ j ≫ V.toBase) ≫ f.fiberι (f x) = _
    rw [Category.assoc, Category.assoc, ← hb, ← Category.assoc, hright]
  · show (e.inv ≫ j ≫ V.toBase) (e.hom w) = _
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    simp only [Scheme.Hom.comp_apply, hw, V.map_point]
  · show (e.inv ≫ j) (e.hom w) = _
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    exact hw

end AlgebraicGeometry

end
