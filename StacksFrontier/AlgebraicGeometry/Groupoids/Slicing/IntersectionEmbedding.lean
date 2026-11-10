module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.FunctionsOnIntersection
public import StacksFrontier.AlgebraicGeometry.Properties.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Scheme.OpensTopIsoNaturality
public import StacksFrontier.Topology.Spectral.QuasiCompactOpenInter

/-!
# Intersections of quasi-compact opens in ind-quasi-affine schemes

An intersection of a nonempty family of quasi-compact open subsets of an ind-quasi-affine
scheme embeds canonically in the spectrum of its ring of sections. Its image is again an
intersection of quasi-compact opens, and the embedding identifies the two restricted locally
ringed spaces.

## Main definitions

* `AlgebraicGeometry.subsetLocallyRingedSpace` is the inverse-image locally ringed space on an
  arbitrary subset of a locally ringed space.
* `AlgebraicGeometry.ofSubset` is its canonical map to the ambient presheafed space.
* `AlgebraicGeometry.Scheme.openToSubset` is the restriction of the functions on an open to the
  sections on a subset contained in it.
* `AlgebraicGeometry.stalkIsoOfPullbackSheaf` identifies the stalk of the inverse image of a sheaf
  of commutative rings with the stalk of the sheaf at the image point.

## Main results

* `AlgebraicGeometry.isIso_ofSubset_stalkMap` : the canonical morphism
  `AlgebraicGeometry.ofSubset` from a restriction to the ambient space is an isomorphism on
  stalks.
* `AlgebraicGeometry.exists_iInter_iso_iInter_in_specΓ` gives the canonical identification of
  the intersection with an intersection of quasi-compact opens in the spectrum of its ring of
  sections, compatibly with every quasi-compact open stage, each comparison map to the spectrum
  of a stage being the spectrum of `AlgebraicGeometry.Scheme.openToSubset`.
* `AlgebraicGeometry.isOpen_image_toΓSpec_of_isOpen` says that the canonical map sends subsets
  of the intersection which are open in the ambient scheme to open subsets.

## Implementation notes

Restriction to a subset uses the inverse image of sheaves along the subtype inclusion. The
compatibility equation says that, after composing the displayed isomorphism with the inclusion
into the spectrum, its morphism of presheafed spaces is exactly the unit of the locally ringed
space `Γ`--`Spec` adjunction. The stage maps identify each displayed quasi-compact open with
the inverse image of the corresponding stage's canonical open image, and their pointwise
compatibility with the canonical map identifies images of ambient-open subsets of the
intersection with inverse images of their open images at every stage.  Each stage map is
moreover the spectrum of `AlgebraicGeometry.Scheme.openToSubset`, the restriction of the
functions on that stage to the intersection; naming it through the open rather than through the
family of opens keeps the statement available for an index type in any universe, and is
legitimate because `AlgebraicGeometry.Scheme.stageToSubset` depends on the family only through
the member it restricts from.

That the canonical map is an isomorphism onto its image is checked on stalks: the stalk of the
restricted structure sheaf is a filtered colimit of the stalks at the stages, and each of those
is the localization of the ring of functions on the stage.

## References

* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- A ring map out of a filtered colimit is a localization at a prime as soon as it is a
localization at the pulled-back prime at every stage. -/
@[ega "IV 5.13.3" "(ii), special case"]
private lemma isLocalization_of_filtered_colimit
    {J : Type u} [Preorder J] [Nonempty J]
    (F : J ⥤ CommRingCat.{u})
    (hdir : ∀ i j : J, ∃ k : J, i ≤ k ∧ j ≤ k)
    (p : Ideal ((colimit F : CommRingCat.{u}) : Type u)) [p.IsPrime]
    {S : Type u} [CommRing S]
    (f : ((colimit F : CommRingCat.{u}) : Type u) →+* S)
    (hloc : ∀ i, letI : Algebra ((F.obj i : CommRingCat.{u}) : Type u) S :=
      (f.comp (colimit.ι F i).hom).toAlgebra
      IsLocalization ((p.comap (colimit.ι F i).hom).primeCompl) S) :
    letI : Algebra ((colimit F : CommRingCat.{u}) : Type u) S := f.toAlgebra
    IsLocalization p.primeCompl S := by
  let : Algebra ((colimit F : CommRingCat.{u}) : Type u) S := f.toAlgebra
  let : IsDirectedOrder J := ⟨fun i j => by
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, hik, hjk⟩⟩
  let : IsFiltered J := inferInstance
  apply (isLocalization_iff p.primeCompl S).2
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro s
    obtain ⟨i, a, haR⟩ := CategoryTheory.Limits.Concrete.colimit_exists_rep F s.1
    let : Algebra ((F.obj i : CommRingCat.{u}) : Type u) S :=
      (f.comp (colimit.ι F i).hom).toAlgebra
    have ha : a ∉ (p.comap (colimit.ι F i).hom) := by
      intro h
      change (colimit.ι F i).hom a ∈ p at h
      rw [haR] at h
      exact s.2 h
    let : IsLocalization ((p.comap (colimit.ι F i).hom).primeCompl) S := hloc i
    have hu := IsLocalization.map_units (R := (F.obj i : Type u))
      (M := (p.comap (colimit.ι F i).hom).primeCompl) S ⟨a, ha⟩
    change IsUnit (f ((colimit.ι F i).hom a)) at hu
    change IsUnit (f s.1)
    rw [← haR]
    exact hu
  · intro z
    obtain ⟨i⟩ := ‹Nonempty J›
    let : Algebra ((F.obj i : CommRingCat.{u}) : Type u) S :=
      (f.comp (colimit.ι F i).hom).toAlgebra
    let : IsLocalization ((p.comap (colimit.ι F i).hom).primeCompl) S := hloc i
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj
      (M := (p.comap (colimit.ι F i).hom).primeCompl) z
    refine ⟨⟨(colimit.ι F i).hom a,
      ⟨(colimit.ι F i).hom s.1, ?_⟩⟩, ?_⟩
    · change (colimit.ι F i).hom s.1 ∉ p
      exact s.2
    · change z * f ((colimit.ι F i).hom s.1) = f ((colimit.ι F i).hom a)
      change z * (f.comp (colimit.ι F i).hom) s.1 =
        (f.comp (colimit.ι F i).hom) a at hs
      exact hs
  · intro a b hab
    obtain ⟨i, ai, hai⟩ := CategoryTheory.Limits.Concrete.colimit_exists_rep F a
    obtain ⟨j, bj, hbj⟩ := CategoryTheory.Limits.Concrete.colimit_exists_rep F b
    obtain ⟨k, hik, hjk⟩ := hdir i j
    let ak := F.map (homOfLE hik) ai
    let bk := F.map (homOfLE hjk) bj
    let : Algebra ((F.obj k : CommRingCat.{u}) : Type u) S :=
      (f.comp (colimit.ι F k).hom).toAlgebra
    have haR : (colimit.ι F i).hom ai = (colimit.ι F k).hom ak := by
      have h := congrArg (fun g : F.obj i ⟶ colimit F => g.hom ai)
        (colimit.w F (homOfLE hik))
      simp [ak]
    have hbR : (colimit.ι F j).hom bj = (colimit.ι F k).hom bk := by
      have h := congrArg (fun g : F.obj j ⟶ colimit F => g.hom bj)
        (colimit.w F (homOfLE hjk))
      simp [bk]
    have hab0 : f ((colimit.ι F i).hom ai) = f ((colimit.ι F j).hom bj) := by
      rw [hai, hbj]
      exact hab
    have habk : f ((colimit.ι F k).hom ak) = f ((colimit.ι F k).hom bk) := by
      rw [haR, hbR] at hab0
      exact hab0
    let : IsLocalization ((p.comap (colimit.ι F k).hom).primeCompl) S := hloc k
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq
      (M := (p.comap (colimit.ι F k).hom).primeCompl)
      (show (f.comp (colimit.ι F k).hom) ak = (f.comp (colimit.ι F k).hom) bk from habk)
    refine ⟨⟨(colimit.ι F k).hom c.1, ?_⟩, ?_⟩
    · intro hcP
      apply c.2
      change (colimit.ι F k).hom c.1 ∈ p at hcP
      exact hcP
    · have hc' := congrArg (fun r => (colimit.ι F k).hom r) hc
      change (colimit.ι F k).hom c.1 * a =
        (colimit.ι F k).hom c.1 * b
      rw [← hai, ← hbj, haR, hbR]
      rw [← (colimit.ι F k).hom.map_mul, ← (colimit.ι F k).hom.map_mul]
      exact hc'

/-- Transport of a localization along an isomorphism of the base ring. -/
private lemma isLocalization_of_ringEquiv_domain
    {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    (e : A ≃+* B) (P : Ideal A) [P.IsPrime] (f : A →+* S)
    (hLoc : letI : Algebra A S := f.toAlgebra; IsLocalization P.primeCompl S)
    (Q : Ideal B) [Q.IsPrime]
    (hQ : Q = Ideal.comap e.symm.toRingHom P) :
    letI : Algebra B S := (f.comp e.symm.toRingHom).toAlgebra
    IsLocalization Q.primeCompl S := by
  let : Algebra A S := f.toAlgebra
  let : IsLocalization P.primeCompl S := hLoc
  let : Algebra B S := (f.comp e.symm.toRingHom).toAlgebra
  have hmem (b : B) : b ∈ Q ↔ e.symm b ∈ P := by
    rw [hQ]
    exact Ideal.mem_comap
  have hQe (a : A) (ha : a ∉ P) : e a ∉ Q := fun h => ha (by simpa using (hmem (e a)).1 h)
  apply (isLocalization_iff Q.primeCompl S).2
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro b
    have hb : e.symm b.1 ∉ P := fun h => b.2 ((hmem b.1).2 h)
    have hu := IsLocalization.map_units (R := A) (M := P.primeCompl) S ⟨e.symm b.1, hb⟩
    change IsUnit (f (e.symm b.1))
    exact hu
  · intro z
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (M := P.primeCompl) z
    refine ⟨⟨e a, ⟨e s.1, hQe _ s.2⟩⟩, ?_⟩
    change z * f (e.symm (e s.1)) = f (e.symm (e a))
    change z * f s.1 = f a at hs
    simpa using hs
  · intro a b hab
    change f (e.symm a) = f (e.symm b) at hab
    have hab' := hab
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) hab'
    refine ⟨⟨e c.1, hQe _ c.2⟩, ?_⟩
    · have hc' := congrArg e hc
      simpa using hc'

/-- Transport of a localization along an isomorphism of the localized ring. -/
private lemma isLocalization_of_ringEquiv_codomain
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (M : Submonoid R) (f : R →+* S)
    (hLoc : letI : Algebra R S := f.toAlgebra; IsLocalization M S)
    (e : S ≃+* T) (g : R →+* T)
    (hg : g = e.toRingHom.comp f) :
    letI : Algebra R T := g.toAlgebra
    IsLocalization M T := by
  let : Algebra R S := f.toAlgebra
  let : IsLocalization M S := hLoc
  let : Algebra R T := g.toAlgebra
  apply (isLocalization_iff M T).2
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro a
    change IsUnit (g a.1)
    rw [hg]
    exact (IsLocalization.map_units (R := R) (M := M) S a).map e.toRingHom
  · intro z
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (M := M) (e.symm z)
    refine ⟨⟨a, s⟩, ?_⟩
    change z * g s.1 = g a
    rw [hg]
    change z * e (algebraMap R S s.1) = e (algebraMap R S a)
    calc
      z * e (algebraMap R S s.1) = e (e.symm z * algebraMap R S s.1) := by
        simp only [map_mul, e.apply_symm_apply]
      _ = e (algebraMap R S a) := congrArg e hs
  · intro a b hab
    have habE : e (algebraMap R S a) = e (algebraMap R S b) := by
      change g a = g b at hab
      rw [hg] at hab
      exact hab
    have hab' : algebraMap R S a = algebraMap R S b := e.injective habE
    exact IsLocalization.exists_of_eq (M := M) hab'

/-- The quasi-compact open neighbourhoods of a subset of a scheme. -/
private def compactOpenNeighborhoods {X : Scheme.{u}} (E : Set X) :=
  {U : X.Opens // IsCompact (U : Set X) ∧ E ⊆ U}

/-- A subset presented as an intersection of a nonempty family of quasi-compact opens has a
quasi-compact open neighbourhood. -/
private lemma compactOpenNeighborhoods_nonempty {X : Scheme.{u}} {I : Type v}
    [Nonempty I] (U : I → X.Opens) (hU : ∀ i, IsCompact (U i : Set X))
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) :
    Nonempty (compactOpenNeighborhoods E) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  refine ⟨⟨U i, hU i, ?_⟩⟩
  rw [hE]
  exact Set.iInter_subset _ i

/-- On an ind-quasi-affine scheme the quasi-compact open neighbourhoods of a subset are directed
under reverse inclusion. -/
private lemma compactOpenNeighborhoods_directed {X : Scheme.{u}}
    [AlgebraicGeometry.IsIndQuasiAffine X] (E : Set X) :
    ∀ i j : compactOpenNeighborhoods E,
      ∃ k : compactOpenNeighborhoods E, (k.1 : Set X) ⊆ i.1 ∩ j.1 := by
  intro i j
  refine ⟨⟨i.1 ⊓ j.1, ?_, Set.subset_inter i.2.2 j.2.2⟩, ?_⟩
  · have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_isIndQuasiAffine X
    exact i.2.1.inter_of_isOpen j.2.1 i.1.isOpen j.1.isOpen
  · exact fun _ hx ↦ ⟨hx.1, hx.2⟩

/-- A subset presented as an intersection of a nonempty family of quasi-compact opens is the
intersection of all of its quasi-compact open neighbourhoods. -/
private lemma compactOpenNeighborhoods_iInter {X : Scheme.{u}} {I : Type v}
    [Nonempty I] (U : I → X.Opens) (hU : ∀ i, IsCompact (U i : Set X))
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) :
    E = ⋂ j : compactOpenNeighborhoods E, (j.1 : Set X) := by
  refine Set.Subset.antisymm (fun x hx ↦ Set.mem_iInter.mpr fun j ↦ j.2.2 hx) fun x hx ↦ ?_
  rw [hE]
  exact Set.mem_iInter.mpr fun i ↦
    Set.mem_iInter.mp hx ⟨U i, hU i, hE ▸ Set.iInter_subset (fun k ↦ (U k : Set X)) i⟩

/-- The locally ringed space obtained by restricting the structure sheaf to an
arbitrary subset, using inverse image of sheaves along the subtype inclusion. -/
noncomputable def subsetLocallyRingedSpace (X : LocallyRingedSpace.{u}) (E : Set X) :
    LocallyRingedSpace.{u} where
  toSheafedSpace :=
    { carrier := TopCat.of E
      presheaf :=
        ((TopCat.Sheaf.pullback CommRingCat.{u}
          (Stacks.subsetInclusion X.toTopCat E)).obj X.sheaf).obj
      IsSheaf :=
        ((TopCat.Sheaf.pullback CommRingCat.{u}
          (Stacks.subsetInclusion X.toTopCat E)).obj X.sheaf).2 }
  isLocalRing x := by
    let f := Stacks.subsetInclusion X.toTopCat E
    let P := (TopCat.Presheaf.pullback CommRingCat f).obj X.presheaf
    let e₁ := TopCat.Presheaf.stalkPullbackIso CommRingCat f X.presheaf x
    let eS := (TopCat.Sheaf.pullbackIso CommRingCat f).app X.sheaf
    let eS' := (TopCat.Sheaf.forget CommRingCat (TopCat.of E)).mapIso eS
    let mS := (TopCat.Presheaf.stalkFunctor CommRingCat x).map eS'.hom
    let mP := (TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of E)) P)
    have hmP : IsIso mP :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat P
    have hmS : IsIso mS := Functor.map_isIso _ _
    apply @RingEquiv.isLocalRing _ _ _ (X.isLocalRing x.1)
    exact (e₁ ≪≫ (@asIso _ _ _ _ mP hmP) ≪≫
      (@asIso _ _ _ _ mS hmS).symm).commRingCatIsoToRingEquiv

/-- The canonical morphism of presheafed spaces from the inverse-image structure
sheaf on a subset to the ambient locally ringed space. -/
noncomputable def ofSubset (X : LocallyRingedSpace.{u}) (E : Set X) :
    (subsetLocallyRingedSpace X E).toPresheafedSpace ⟶ X.toPresheafedSpace :=
  { base := Stacks.subsetInclusion X.toTopCat E
    c := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
      (Stacks.subsetInclusion X.toTopCat E)).unit.app X.sheaf).hom }

/-- The stalk of the inverse image of a sheaf of commutative rings is the stalk of the sheaf at
the image point. -/
noncomputable def stalkIsoOfPullbackSheaf {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf CommRingCat.{u}) (z : Z) :
    ((TopCat.Sheaf.pullback CommRingCat g).obj F).presheaf.stalk z ≅
      F.presheaf.stalk (g z) := by
  let P := (TopCat.Presheaf.pullback CommRingCat g).obj F.presheaf
  let η := toSheafify (Opens.grothendieckTopology Z) P
  let eS := (TopCat.Sheaf.forget CommRingCat Z).mapIso
    ((TopCat.Sheaf.pullbackIso CommRingCat g).app F)
  let mP := (TopCat.Presheaf.stalkFunctor CommRingCat z).map η
  have hmP : IsIso mP :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso z CommRingCat P
  exact (TopCat.Presheaf.stalkFunctor CommRingCat z).mapIso eS ≪≫
    (@asIso _ _ _ _ mP hmP).symm ≪≫
      (TopCat.Presheaf.stalkPullbackIso CommRingCat g F.presheaf z).symm

/-- The comparison of the two constructions of the inverse-image sheaf matches their adjunction
units. -/
lemma pullbackSheafIso_unit_app {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf CommRingCat.{u}) (V : Opens Y) (s : F.obj.obj (op V)) :
    ((TopCat.Sheaf.pullbackIso CommRingCat g).app F).hom.hom.app
      (op ((Opens.map g).obj V))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app F).hom.app
        (op V) s) =
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map g) CommRingCat (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology Z)).unit.app F).hom.app (op V)) s := by
  let adj₁ := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g
  let adj₂ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map g) CommRingCat (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology Z)
  have h := adj₁.unit_leftAdjointUniq_hom_app adj₂ F
  have h' := congrArg (fun m : F ⟶ (TopCat.Sheaf.pushforward CommRingCat g).obj
      ((presheafToSheaf (Opens.grothendieckTopology Z) CommRingCat).obj
        ((TopCat.Presheaf.pullback CommRingCat g).obj F.presheaf)) ↦
      m.hom.app (op V) s) h
  exact h'

/-- The unit of the site-theoretic inverse-image adjunction is the sheafification of the
presheaf-level unit. -/
lemma pullbackSheafConstruction_unit_app {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf CommRingCat.{u}) (V : Opens Y) (s : F.obj.obj (op V)) :
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map g) CommRingCat (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology Z)).unit.app F).hom.app (op V)) s =
      (toSheafify (Opens.grothendieckTopology Z)
        ((TopCat.Presheaf.pullback CommRingCat g).obj F.presheaf)).app
        (op ((Opens.map g).obj V))
          (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app
            F.presheaf).app (op V) s) := rfl

/-- `AlgebraicGeometry.stalkIsoOfPullbackSheaf` carries a germ to the germ of the image of the
section under the adjunction unit. -/
lemma stalkIsoOfPullbackSheaf_inv_germ {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf CommRingCat.{u}) (z : Z) (V : Opens Y) (hz : g z ∈ V)
    (s : F.obj.obj (op V)) :
    (stalkIsoOfPullbackSheaf g F z).inv (F.presheaf.germ V (g z) hz s) =
      ((TopCat.Sheaf.pullback CommRingCat g).obj F).presheaf.germ
        ((Opens.map g).obj V) z hz
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app F).hom.app
          (op V) s) := by
  let W := (Opens.map g).obj V
  let P := (TopCat.Presheaf.pullback CommRingCat g).obj F.presheaf
  let Q := (presheafToSheaf (Opens.grothendieckTopology Z) CommRingCat).obj P
  let H := (TopCat.Sheaf.pullback CommRingCat g).obj F
  let η := toSheafify (Opens.grothendieckTopology Z) P
  let e : H.presheaf ≅ Q.obj :=
    (TopCat.Sheaf.forget CommRingCat Z).mapIso
      ((TopCat.Sheaf.pullbackIso CommRingCat g).app F)
  have hzW : z ∈ W := hz
  let t := ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app
    F.presheaf).app (op V) s
  let t' := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app F).hom.app
    (op V) s
  have hu : e.hom.app (op W) t' = η.app (op W) t :=
    (pullbackSheafIso_unit_app g F V s).trans (pullbackSheafConstruction_unit_app g F V s)
  have hu' : e.inv.app (op W) (η.app (op W) t) = t' := by
    rw [← hu]
    exact congrArg (fun f : H.presheaf ⟶ H.presheaf ↦ f.app (op W) t') e.hom_inv_id
  have h₁ : (TopCat.Presheaf.stalkPullbackIso CommRingCat g F.presheaf z).hom
      (F.presheaf.germ V (g z) hz s) = P.germ W z hzW t :=
    congrArg (fun f : F.obj.obj (op V) ⟶ P.stalk z ↦ f s)
      (TopCat.Presheaf.germ_stalkPullbackHom CommRingCat g F.presheaf z V hz)
  have h₂ := TopCat.Presheaf.stalkFunctor_map_germ_apply W z hzW η t
  have h₃ := TopCat.Presheaf.stalkFunctor_map_germ_apply W z hzW e.inv
    (η.app (op W) t)
  change ((TopCat.Presheaf.stalkFunctor CommRingCat z).map e.inv)
      (((TopCat.Presheaf.stalkFunctor CommRingCat z).map η)
        ((TopCat.Presheaf.stalkPullbackIso CommRingCat g F.presheaf z).hom
          (F.presheaf.germ V (g z) hz s))) = H.presheaf.germ W z hzW t'
  rw [h₁, h₂, h₃, hu']

/-- The canonical morphism from the restriction of a locally ringed space to a subset is an
isomorphism on stalks. -/
lemma isIso_ofSubset_stalkMap (Y : LocallyRingedSpace.{u}) (E : Set Y)
    (x : ↑(subsetLocallyRingedSpace Y E).toTopCat) :
    IsIso ((ofSubset Y E).stalkMap x) := by
  let i : (subsetLocallyRingedSpace Y E).toPresheafedSpace.carrier ⟶ Y.toTopCat :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let e := stalkIsoOfPullbackSheaf i Y.sheaf x
  have he : (ofSubset Y E).stalkMap x = e.inv := by
    apply TopCat.Presheaf.stalk_hom_ext Y.presheaf
    intro V hx
    ext s
    have hq := PresheafedSpace.stalkMap_germ (ofSubset Y E) V x hx
    have hg := stalkIsoOfPullbackSheaf_inv_germ i Y.sheaf x V hx s
    change (Y.presheaf.germ V (i x) hx ≫ (ofSubset Y E).stalkMap x) s = _
    have hq' : Y.presheaf.germ V (i x) hx ≫ (ofSubset Y E).stalkMap x =
        (ofSubset Y E).c.app (op V) ≫
          (subsetLocallyRingedSpace Y E).presheaf.germ
            ((Opens.map i).obj V) x hx := by
      change Y.presheaf.germ V (i x) hx ≫ (ofSubset Y E).stalkMap x = _ at hq
      exact hq
    rw [hq']
    exact hg.symm
  rw [he]
  exact ⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩

/-- The map of underlying spaces carrying a morphism of locally ringed spaces whose image lies in
a subset of the target into the restriction of the target to that subset. -/
private def subsetFactorBase {X Y : LocallyRingedSpace.{u}}
    (E : Set Y) (f : X ⟶ Y) (h : ∀ x, f.base x ∈ E) :
    (X.toPresheafedSpace : TopCat) ⟶
      ((subsetLocallyRingedSpace Y E).toPresheafedSpace : TopCat) :=
  TopCat.ofHom ⟨fun x => ⟨f.base x, h x⟩, f.base.hom.2.subtype_mk h⟩

/-- A morphism of locally ringed spaces whose image lies in a subset factors through the
restriction of the target to that subset. -/
private noncomputable def subsetFactorHom {X Y : LocallyRingedSpace.{u}}
    (E : Set Y) (f : X ⟶ Y) (h : ∀ x, f.base x ∈ E) :
    X.toPresheafedSpace ⟶ (subsetLocallyRingedSpace Y E).toPresheafedSpace := by
  let i := (ofSubset Y E).base
  let g := subsetFactorBase E f h
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat i
  let cF : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat i).obj
      ((TopCat.Sheaf.pushforward CommRingCat g).obj X.sheaf) :=
    (TopCat.Sheaf.forget CommRingCat Y.toTopCat).preimage f.toHom.c
  let c := (adj.homEquiv Y.sheaf ((TopCat.Sheaf.pushforward CommRingCat g).obj X.sheaf)).symm cF
  let raw : X.toPresheafedSpace.Hom (subsetLocallyRingedSpace Y E).toPresheafedSpace :=
    ⟨g, c.hom⟩
  exact raw

/-- On underlying spaces, `subsetFactorHom` composed with the canonical morphism from the
restriction is the given morphism. -/
private lemma subsetFactorHom_base_comp {X Y : LocallyRingedSpace.{u}}
    (E : Set Y) (f : X ⟶ Y) (h : ∀ x, f.base x ∈ E) :
    (subsetFactorHom E f h).base ≫ (ofSubset Y E).base = f.base := by
  ext x
  rfl

/-- The factorization of `subsetFactorHom` through the canonical morphism from the restriction. -/
private lemma subsetFactorHom_comp {X Y : LocallyRingedSpace.{u}}
    (E : Set Y) (f : X ⟶ Y) (h : ∀ x, f.base x ∈ E) :
    subsetFactorHom E f h ≫ ofSubset Y E = f.toHom := by
  let i := (ofSubset Y E).base
  let g := subsetFactorBase E f h
  have hbase : (subsetFactorHom E f h ≫ ofSubset Y E).base = f.base := by
    rw [PresheafedSpace.comp_base]
    exact subsetFactorHom_base_comp E f h
  refine PresheafedSpace.hext (subsetFactorHom E f h ≫ ofSubset Y E) f.toHom hbase
    (heq_of_eq ?_)
  dsimp only [subsetFactorHom]
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat i
  let cF : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat i).obj
      ((TopCat.Sheaf.pushforward CommRingCat g).obj X.sheaf) :=
    (TopCat.Sheaf.forget CommRingCat Y.toTopCat).preimage f.toHom.c
  let c := (adj.homEquiv Y.sheaf ((TopCat.Sheaf.pushforward CommRingCat g).obj X.sheaf)).symm cF
  have hc : cF = adj.unit.app Y.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat i).map c := by
    dsimp [c]
    rw [← adj.homEquiv_unit]
    exact (Equiv.apply_symm_apply _ _).symm
  have hc' := congrArg
    (fun q => (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map q) hc
  ext V s
  have hc'' := congrArg (fun q => q.app (op V)) hc'
  have hcV := congrArg (fun q => q s) hc''
  have hmapCF : (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map
      ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).preimage
        (X := Y.sheaf)
        (Y := (TopCat.Sheaf.pushforward CommRingCat i).obj
          ((TopCat.Sheaf.pushforward CommRingCat g).obj X.sheaf)) f.toHom.c) = f.toHom.c :=
    (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map_preimage
      (X := Y.sheaf)
      (Y := (TopCat.Sheaf.pushforward CommRingCat i).obj
        ((TopCat.Sheaf.pushforward CommRingCat g).obj X.sheaf)) f.toHom.c
  convert hcV.symm using 1 <;>
    simp [cF, ofSubset, Functor.map_comp, hmapCF]
  all_goals rfl

/-- A morphism of locally ringed spaces which is a homeomorphism onto a subset of the target and
an isomorphism on stalks identifies its source with the restriction of the target to that
subset. -/
private theorem exists_iso_subsetLocallyRingedSpace {Z Y : LocallyRingedSpace.{u}} (S : Set Y)
    (f : Z ⟶ Y) (hfS : ∀ z, f.base z ∈ S) (hinj : Function.Injective f.base)
    (hsurj : ∀ y ∈ S, ∃ z, f.base z = y)
    (hopen : IsOpenMap fun z ↦ (⟨f.base z, hfS z⟩ : S))
    (hstalk : ∀ z, IsIso (f.stalkMap z)) :
    ∃ e : Z ≅ subsetLocallyRingedSpace Y S, e.hom.toHom ≫ ofSubset Y S = f.toHom := by
  let gP := subsetFactorHom S f hfS
  have hfac := subsetFactorHom_comp S f hfS
  let iS := ofSubset Y S
  have hPt (x : Z) : iS.base (gP.base x) = f.base x := by
    have hbase := congrArg (fun q : PresheafedSpace.Hom _ _ => q.base) hfac
    rw [PresheafedSpace.comp_base] at hbase
    have hp := congrArg (fun q : TopCat.Hom _ _ => q.hom x) hbase
    change iS.base.hom (gP.base.hom x) = f.base.hom x at hp
    exact hp
  let gS : Z.toSheafedSpace ⟶ (subsetLocallyRingedSpace Y S).toSheafedSpace :=
    SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage gP
  have hiso (x : Z) : IsIso (gS.hom.stalkMap x) := by
    let ePt := asIso (eqToHom (show Y.presheaf.stalk (iS.base (gP.base x)) =
      Y.presheaf.stalk (f.base x) by
        exact congrArg (fun y : Y => Y.presheaf.stalk y) (hPt x)))
    have hfacStalk := PresheafedSpace.stalkMap.congr_hom
      (subsetFactorHom S f hfS ≫ ofSubset Y S) f.toHom hfac x
    rw [PresheafedSpace.stalkMap.comp] at hfacStalk
    have hmap : iS.stalkMap (gP.base x) ≫ gS.hom.stalkMap x =
        ePt.hom ≫ f.toHom.stalkMap x := by
      change PresheafedSpace.Hom.stalkMap (ofSubset Y S)
          ((ConcreteCategory.hom (subsetFactorHom S f hfS).base) x) ≫
        PresheafedSpace.Hom.stalkMap (subsetFactorHom S f hfS) x =
          eqToHom (show Y.presheaf.stalk
            ((ConcreteCategory.hom (ofSubset Y S).base)
              ((ConcreteCategory.hom (subsetFactorHom S f hfS).base) x)) =
            Y.presheaf.stalk ((ConcreteCategory.hom f.base) x) by
              exact congrArg (fun y : Y => Y.presheaf.stalk y) (hPt x)) ≫
              f.toHom.stalkMap x
      exact hfacStalk
    have : IsIso (iS.stalkMap (gP.base x)) := isIso_ofSubset_stalkMap Y S (gP.base x)
    have : IsIso (f.toHom.stalkMap x) := hstalk x
    have : IsIso (iS.stalkMap (gP.base x) ≫ gS.hom.stalkMap x) := by
      rw [hmap]
      infer_instance
    exact IsIso.of_isIso_comp_left (iS.stalkMap (gP.base x)) (gS.hom.stalkMap x)
  let g : Z ⟶ subsetLocallyRingedSpace Y S := LocallyRingedSpace.homMk gS fun x ↦ by
    have := hiso x
    exact isLocalHom_of_isIso _
  have hbaseSurj : Function.Surjective g.base := fun y ↦
    (hsurj y.1 y.2).imp fun _ hx ↦ Subtype.ext hx
  have hbaseInj : Function.Injective g.base := by
    intro x y hxy
    have hxyP : gP.base x = gP.base y := hxy
    exact hinj ((hPt x).symm.trans ((congrArg iS.base hxyP).trans (hPt y)))
  have hbaseOpen : Topology.IsOpenEmbedding g.base.hom :=
    .of_continuous_injective_isOpenMap g.base.hom.2 hbaseInj hopen
  let : ∀ x, IsIso (g.stalkMap x) := hiso
  have : Epi g.base := (TopCat.epi_iff_surjective g.base).2 hbaseSurj
  let : LocallyRingedSpace.IsOpenImmersion g :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso g hbaseOpen
  let : IsIso g := LocallyRingedSpace.IsOpenImmersion.to_iso g
  exact ⟨asIso g, hfac⟩

/-- On a quasi-affine scheme the stalk at a point is the localization of the ring of global
sections at the corresponding prime. -/
private lemma isLocalization_toSpecΓ_stalk {U : Scheme.{u}} [U.IsQuasiAffine]
    (x : U) :
    let y : Spec Γ(U, ⊤) := U.toSpecΓ.base x
    letI : y.asIdeal.IsPrime := y.2
    letI : Algebra Γ(U, ⊤) (U.presheaf.stalk x) :=
      (U.presheaf.Γgerm x).hom.toAlgebra
    IsLocalization y.asIdeal.primeCompl (U.presheaf.stalk x) := by
  let y : Spec Γ(U, ⊤) := U.toSpecΓ.base x
  let : y.asIdeal.IsPrime := y.2
  have hstalk : IsIso (U.toSpecΓ.toPshHom.stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (show IsOpenImmersion U.toSpecΓ from inferInstance)).2 x
  let e : (Spec.toLocallyRingedSpace.obj (op Γ(U, ⊤))).presheaf.stalk y ≅
      U.toLocallyRingedSpace.presheaf.stalk x :=
    @asIso _ _ _ _ (U.toSpecΓ.toPshHom.stalkMap x) hstalk
  let : Algebra Γ(U, ⊤)
      ((Spec.toLocallyRingedSpace.obj (op Γ(U, ⊤))).presheaf.stalk y) :=
    StructureSheaf.stalkAlgebra (Γ(U, ⊤)) y
  let : IsLocalization.AtPrime
      ((Spec.toLocallyRingedSpace.obj (op Γ(U, ⊤))).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (R := Γ(U, ⊤)) y
  let : Algebra Γ(U, ⊤) (U.presheaf.stalk x) := (U.presheaf.Γgerm x).hom.toAlgebra
  have hmap : StructureSheaf.toStalk Γ(U, ⊤) y ≫ e.hom = U.presheaf.Γgerm x := by
    change StructureSheaf.toStalk (U.presheaf.obj (op ⊤)) (U.toSpecΓ.base x) ≫
      U.toSpecΓ.toPshHom.stalkMap x = U.presheaf.Γgerm x
    exact LocallyRingedSpace.toStalk_stalkMap_toΓSpec U.toLocallyRingedSpace x
  let ee : ((Spec.toLocallyRingedSpace.obj (op Γ(U, ⊤))).presheaf.stalk y) ≃ₐ[Γ(U, ⊤)]
      (U.presheaf.stalk x) := AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) fun r =>
    congrArg (fun q : CommRingCat.of Γ(U, ⊤) ⟶ CommRingCat.of (U.presheaf.stalk x) => q r) hmap
  exact IsLocalization.isLocalization_of_algEquiv y.asIdeal.primeCompl ee

/-- The canonical map from a stage to the sections on a subset induces, on stalks, the germ of
the given section. -/
private lemma stageToSubset_germ {X : Scheme.{u}} {J : Type u}
    (W : J → X.Opens) (E : Set X) (hE : ∀ j, E ⊆ W j) (j : J)
    (x : E) (r : Γ(X, W j)) :
    let Z := subsetLocallyRingedSpace X.toLocallyRingedSpace E
    (stalkIsoOfPullbackSheaf (Stacks.subsetInclusion (TopCat.of X) E)
      X.toLocallyRingedSpace.sheaf ⟨x.1, x.2⟩).hom
      (Z.presheaf.Γgerm ⟨x.1, x.2⟩
        (Scheme.stageToSubset X W E hE ⟨j⟩ r)) =
      X.toLocallyRingedSpace.presheaf.germ (W j) x.1 (hE j x.2) r := by
  dsimp only
  let z : ↑(TopCat.of E) := x
  let f := Stacks.subsetInclusion (TopCat.of X) E
  let H := (TopCat.Sheaf.pullback CommRingCat f).obj X.toLocallyRingedSpace.sheaf
  let t := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f).unit.app
    X.toLocallyRingedSpace.sheaf).hom.app (op (W j)) r
  let iTop : (⊤ : Opens E) ⟶ (Opens.map f).obj (W j) := homOfLE
    (by intro y hy; exact hE j y.2)
  let e := stalkIsoOfPullbackSheaf f X.toLocallyRingedSpace.sheaf z
  have hstageGerm :
      (subsetLocallyRingedSpace X.toLocallyRingedSpace E).presheaf.Γgerm z
          (Scheme.stageToSubset X W E hE ⟨j⟩ r) =
        H.presheaf.germ ((Opens.map f).obj (W j)) z
          (show z ∈ (Opens.map f).obj (W j) from hE j x.2) t := by
    have hres := H.presheaf.germ_res_apply iTop z (by trivial) t
    change H.presheaf.germ ⊤ z (by trivial) (H.presheaf.map iTop.op t) = _
    exact hres
  have hpull := stalkIsoOfPullbackSheaf_inv_germ f X.toLocallyRingedSpace.sheaf
    z (W j) (show f z ∈ W j from hE j x.2) r
  have h1 := congrArg e.hom hstageGerm
  have h2 := congrArg e.hom hpull.symm
  change e.hom (H.presheaf.germ ((Opens.map f).obj (W j)) z
      (show z ∈ (Opens.map f).obj (W j) from hE j x.2) t) =
    e.hom (e.inv (X.toLocallyRingedSpace.presheaf.germ (W j) (f z)
      (hE j x.2) r)) at h2
  have hIsoPoint : e.hom (e.inv
      (X.toLocallyRingedSpace.presheaf.germ (W j) (f z) (hE j x.2) r)) =
      X.toLocallyRingedSpace.presheaf.germ (W j) (f z) (hE j x.2) r :=
    CategoryTheory.Iso.inv_hom_id_apply e _
  convert h1.trans (h2.trans hIsoPoint) using 1
  rfl

/-- A function on a stage restricts to a unit in the stalk of the restriction to a contained
subset at a point exactly when it is a unit in the stalk of the stage at that point. -/
private lemma isUnit_Γgerm_stageToSubset_iff {X : Scheme.{u}} {J : Type u} (W : J → X.Opens)
    (E : Set X) (hE : ∀ j, E ⊆ W j) (j : J) (x : E) (r : Γ(X, W j)) :
    IsUnit ((subsetLocallyRingedSpace X.toLocallyRingedSpace E).presheaf.Γgerm ⟨x.1, x.2⟩
        (X.stageToSubset W E hE ⟨j⟩ r)) ↔
      IsUnit ((W j).toScheme.toLocallyRingedSpace.presheaf.Γgerm
        (⟨x.1, hE j x.2⟩ : (W j).toScheme) ((W j).topIso.inv r)) := by
  let zUpt : W j := ⟨x.1, hE j x.2⟩
  let eZ := stalkIsoOfPullbackSheaf (Stacks.subsetInclusion (TopCat.of X) E)
    X.toLocallyRingedSpace.sheaf ⟨x.1, x.2⟩
  let eU := (W j).stalkIso zUpt
  have hU := congrArg (fun g ↦ g ((W j).topIso.inv r))
    ((W j).germ_stalkIso_hom zUpt (V := ⊤) trivial)
  have hxImgU : zUpt.1 ∈ (W j).ι ''ᵁ ⊤ := ⟨zUpt, trivial, rfl⟩
  let iTopU : ((W j).ι ''ᵁ ⊤) ⟶ W j := eqToHom (W j).ι_image_top
  have htop :
      X.toLocallyRingedSpace.presheaf.germ ((W j).ι ''ᵁ ⊤) zUpt.1 hxImgU
        ((W j).topIso.inv r) =
      X.toLocallyRingedSpace.presheaf.germ (W j) zUpt.1 (hE j x.2) r := by
    change X.toLocallyRingedSpace.presheaf.germ ((W j).ι ''ᵁ ⊤) zUpt.1 hxImgU
        (X.presheaf.map iTopU.op r) = _
    exact X.presheaf.germ_res_apply iTopU zUpt.1 hxImgU r
  have hgerm := (stageToSubset_germ W E hE j x r).trans (htop.symm.trans hU.symm)
  exact (isUnit_map_iff eZ.commRingCatIsoToRingEquiv _).symm.trans
    ((congrArg IsUnit hgerm).to_iff.trans (isUnit_map_iff eU.commRingCatIsoToRingEquiv _))

/-- The spectrum of the restriction from a stage to a contained subset carries the canonical
image of a point of the subset to the canonical image of that point in the stage. -/
private lemma Scheme.spec_stageToSubset_base_toΓSpec {X : Scheme.{u}} {J : Type u} (W : J → X.Opens)
    (E : Set X) (hE : ∀ j, E ⊆ W j) (i : intersectionIndex W) (x : E) :
    (Scheme.Spec.map (X.stageToSubset W E hE i).op).base
        ((subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec.base x) =
      (W i.val).toSpecΓ.base ⟨x.1, hE i.val x.2⟩ := by
  let Z := subsetLocallyRingedSpace X.toLocallyRingedSpace E
  have hR : LocallyRingedSpace.Γ.obj (op Z) = Scheme.sectionsRingOnSubset X E := rfl
  let j := i.val
  let z : ↑Z.toTopCat := ⟨x.1, x.2⟩
  let zU : ↑(W j).toScheme.toTopCat := ⟨x.1, hE j x.2⟩
  change (Scheme.Spec.map (X.stageToSubset W E hE i).op).base (hR ▸ Z.toΓSpec.base z) =
    (W j).toSpecΓ.base zU
  apply PrimeSpectrum.ext
  ext r
  change r ∈ (PrimeSpectrum.comap (X.stageToSubset W E hE i).hom
      (hR ▸ Z.toΓSpec.base z)).asIdeal ↔ r ∈ ((W j).toSpecΓ.base zU).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, ← not_iff_not]
  change (hR.symm ▸ (X.stageToSubset W E hE i) r) ∉ (Z.toΓSpecFun z).asIdeal ↔
      r ∉ (Ideal.comap (W j).topIso.inv.hom ((W j).toScheme.toΓSpecFun zU).asIdeal)
  simp only []
  rw [LocallyRingedSpace.notMem_prime_iff_unit_in_stalk]
  let rU : LocallyRingedSpace.Γ.obj (op (W j).toScheme.toLocallyRingedSpace) :=
    (W j).topIso.inv r
  change IsUnit ((Z.presheaf.Γgerm z) (hR.symm ▸ X.stageToSubset W E hE i r)) ↔
      rU ∉ ((W j).toScheme.toLocallyRingedSpace.toΓSpecFun zU).asIdeal
  rw [LocallyRingedSpace.notMem_prime_iff_unit_in_stalk]
  exact isUnit_Γgerm_stageToSubset_iff W E hE i.val x r

/-- For two quasi-affine opens of a scheme, one contained in the other, the canonical morphism of
the smaller one to the spectrum of its functions is the base change of that of the larger. -/
private lemma isPullback_opens_toSpecΓ {X : Scheme.{u}} {U V : X.Opens}
    (h : U ≤ V) [U.toScheme.IsQuasiAffine] [V.toScheme.IsQuasiAffine] :
    IsPullback (𝟙 U.toScheme) U.toSpecΓ
      (X.homOfLE h ≫ V.toSpecΓ)
      (Scheme.Spec.map (X.presheaf.map (homOfLE h).op).op) := by
  let f := X.homOfLE h
  let eU := Scheme.Spec.mapIso U.topIso.symm.op
  let eV := Scheme.Spec.mapIso V.topIso.symm.op
  have H := isPullback_id_toSpecΓ_of_isOpenImmersion
    U.toScheme V.toScheme f
  have hring : V.topIso.inv ≫ f.appTop =
      X.presheaf.map (homOfLE h).op ≫ U.topIso.inv := by
    calc
      V.topIso.inv ≫ f.appTop =
          (V.topIso.inv ≫ f.appTop ≫ U.topIso.hom) ≫ U.topIso.inv := by
            simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = X.presheaf.map (homOfLE h).op ≫ U.topIso.inv := by
        rw [AlgebraicGeometry.opens_topIso_naturality h]
  have hcomm : Scheme.Spec.map f.appTop.op ≫ eV.hom =
      eU.hom ≫ Scheme.Spec.map (X.presheaf.map (homOfLE h).op).op := by
    dsimp [eU, eV]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  exact H.of_iso (Iso.refl _) (Iso.refl _) eU eV rfl rfl rfl hcomm

/-- For quasi-affine opens `V ≤ U` of a scheme, restricting functions from `U` to `V` is
compatible with the canonical maps of `U` and `V` to the spectra of their functions. -/
private lemma spec_map_res_toSpecΓ_base {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U)
    [U.toScheme.IsQuasiAffine] [V.toScheme.IsQuasiAffine] (x : V) :
    (Scheme.Spec.map (X.presheaf.map (homOfLE h).op).op).base (V.toSpecΓ.base x) =
      U.toSpecΓ.base ⟨x.1, h x.2⟩ := by
  let f := X.homOfLE h
  let xS : V.toScheme := ⟨x.1, x.2⟩
  let xU : U.toScheme := ⟨x.1, h x.2⟩
  have hsquare := congrArg (fun q : V.toScheme ⟶ Spec Γ(X, U) => q.base xS)
    (isPullback_opens_toSpecΓ h).w
  have hsquare' : (f ≫ U.toSpecΓ).base xS =
      (V.toSpecΓ ≫ Scheme.Spec.map (X.presheaf.map (homOfLE h).op).op).base xS := by
    change (𝟙 V.toScheme ≫ f ≫ U.toSpecΓ).base xS = _
    rwa [Category.id_comp] at hsquare
  have hfx : f xS = xU := by
    change (X.homOfLE h).base xS = _
    rw [Scheme.homOfLE_base]
    rfl
  calc
    _ = (f ≫ U.toSpecΓ).base xS := by
          change (V.toSpecΓ ≫ Scheme.Spec.map
            (X.presheaf.map (homOfLE h).op).op).base xS = _
          exact hsquare'.symm
    _ = U.toSpecΓ.base (f xS) := by
          rw [Scheme.Hom.comp_base]
          rfl
    _ = U.toSpecΓ.base xU := by rw [hfx]

/-- Two points of a quasi-compact open of an ind-quasi-affine scheme with the same canonical image
in the spectrum of its functions are the same point of the scheme. -/
private lemma val_eq_of_toSpecΓ_base_eq {X : Scheme.{u}} [IsIndQuasiAffine X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) {x y : U} (h : U.toSpecΓ.base x = U.toSpecΓ.base y) :
    x.1 = y.1 := by
  have := isOpenImmersion_toSpecΓ_of_isIndQuasiAffine X U hU
  exact congrArg (fun z : U => (z : X)) (U.toSpecΓ.isOpenEmbedding.injective h)

/-- For quasi-compact opens `V ≤ U` of an ind-quasi-affine scheme, a point of the spectrum of the
functions on `V` whose restriction to `U` comes from a point of `V` comes from that point. -/
private lemma exists_toSpecΓ_eq_of_spec_map_res {X : Scheme.{u}} [IsIndQuasiAffine X]
    {U V : X.Opens}
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X)) (h : V ≤ U)
    (a : Spec Γ(X, V)) (x : U)
    (hax : (Scheme.Spec.map (X.presheaf.map (homOfLE h).op).op).base a = U.toSpecΓ.base x)
    (hx : (x : X) ∈ V) :
    ∃ x' : V, a = V.toSpecΓ.base x' ∧ x'.1 = x.1 := by
  let f := X.homOfLE h
  let : V.toScheme.IsQuasiAffine := AlgebraicGeometry.IsIndQuasiAffine.isQuasiAffine V hV
  let : U.toScheme.IsQuasiAffine := AlgebraicGeometry.IsIndQuasiAffine.isQuasiAffine U hU
  let : IsOpenImmersion f := inferInstance
  let : IsOpenImmersion V.toSpecΓ := isOpenImmersion_toSpecΓ_of_isIndQuasiAffine X V hV
  let : IsOpenImmersion U.toSpecΓ := isOpenImmersion_toSpecΓ_of_isIndQuasiAffine X U hU
  let : IsOpenImmersion (f ≫ U.toSpecΓ) := inferInstance
  have hset : Set.range V.toSpecΓ.base =
      (Scheme.Spec.map (X.presheaf.map (homOfLE h).op).op).base ⁻¹'
        (U.toSpecΓ.base '' (U.ι).base ⁻¹' (V : Set X)) := by
    have hh := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (isPullback_opens_toSpecΓ (X := X) h) (⊤ : Opens V)
    have hs := congrArg (fun O : Opens (Spec Γ(X, V)) => (O : Set (Spec Γ(X, V)))) hh
    simpa [f, Scheme.homOfLE_base] using hs
  have hmem : a ∈ Set.range V.toSpecΓ.base := by
    rw [hset, Set.mem_preimage, hax]
    exact ⟨x, hx, rfl⟩
  obtain ⟨x', hx'⟩ := hmem
  have heq : U.toSpecΓ.base ⟨x'.1, h x'.2⟩ = U.toSpecΓ.base x := by
    rw [← spec_map_res_toSpecΓ_base h x', hx', hax]
  exact ⟨x', hx'.symm, val_eq_of_toSpecΓ_base_eq hU heq⟩

/-- The restriction of the functions on an open subset of a scheme to the sections on a subset
contained in that open. -/
def Scheme.openToSubset (X : Scheme.{u}) (V : X.Opens) (E : Set X) (hE : E ⊆ (V : Set X)) :
    Γ(X, V) ⟶ X.sectionsRingOnSubset E :=
  X.stageToSubset (fun _ : PUnit.{u + 1} ↦ V) E (fun _ ↦ hE) ⟨PUnit.unit⟩

/-- The restriction from a stage of a family of opens to a contained subset is the restriction
from that member of the family: the stage map depends on the family only through it. -/
lemma Scheme.stageToSubset_eq_openToSubset (X : Scheme.{u}) {I : Type u} (U : I → X.Opens)
    (E : Set X) (hE : ∀ i, E ⊆ (U i : Set X)) (i : I) :
    X.stageToSubset U E hE ⟨i⟩ = X.openToSubset (U i) E (hE i) := rfl

/-- The restriction maps from the stages of a directed family of quasi-compact opens to their
intersection are compatible with the restriction maps between the stages. -/
private lemma Scheme.sectionsRingDiagram_map_comp_stageToSubset {X : Scheme.{u}}
    [QuasiSeparatedSpace X]
    {J : Type u} [Nonempty J] (W : J → X.Opens) (hW : ∀ j, IsCompact (W j : Set X))
    (hdir : ∀ i j, ∃ k, (W k : Set X) ⊆ W i ∩ W j) (E : Set X) (hEq : E = ⋂ j, (W j : Set X))
    (hE : ∀ j, E ⊆ W j) {i j : intersectionIndex W} (f : i ⟶ j) :
    (Scheme.sectionsRingDiagram X W).map f ≫ X.stageToSubset W E hE j =
      X.stageToSubset W E hE i := by
  obtain ⟨e, he⟩ := colimit_sectionsRing_iso_sectionsRingOnSubset X W hW hdir E hEq
  rw [← he i, ← he j, colimit.w_assoc]

/-- Restricting functions along `W j ≤ W i` carries the image of a point under the spectrum of
the stage map at `j` to its image under the spectrum of the stage map at `i`. -/
private lemma Scheme.spec_map_res_spec_stageToSubset_base {X : Scheme.{u}} [QuasiSeparatedSpace X]
    {J : Type u} [Nonempty J] (W : J → X.Opens) (hW : ∀ j, IsCompact (W j : Set X))
    (hdir : ∀ i j, ∃ k, (W k : Set X) ⊆ W i ∩ W j) (E : Set X) (hEq : E = ⋂ j, (W j : Set X))
    (hE : ∀ j, E ⊆ W j) {i j : J} (h : W j ≤ W i) (y : Spec (X.sectionsRingOnSubset E)) :
    (Scheme.Spec.map (X.presheaf.map (homOfLE h).op).op).base
        ((Scheme.Spec.map (X.stageToSubset W E hE ⟨j⟩).op).base y) =
      (Scheme.Spec.map (X.stageToSubset W E hE ⟨i⟩).op).base y := by
  have h' : (Scheme.Spec.map ((Scheme.sectionsRingDiagram X W).map
      (homOfLE h : (⟨i⟩ : intersectionIndex W) ⟶ ⟨j⟩) ≫ X.stageToSubset W E hE ⟨j⟩).op).base y =
      (Scheme.Spec.map (X.stageToSubset W E hE ⟨i⟩).op).base y := by
    rw [Scheme.sectionsRingDiagram_map_comp_stageToSubset W hW hdir E hEq]
  rw [op_comp, Functor.map_comp, Scheme.Hom.comp_base] at h'
  exact h'

/-- Two points of the spectrum of the functions on the intersection of a directed family of
quasi-compact opens coincide as soon as their images under every stage map do. -/
private lemma Scheme.eq_of_spec_stageToSubset_base_eq {X : Scheme.{u}} [QuasiSeparatedSpace X]
    {J : Type u} [Nonempty J] (W : J → X.Opens) (hW : ∀ j, IsCompact (W j : Set X))
    (hdir : ∀ i j, ∃ k, (W k : Set X) ⊆ W i ∩ W j) (E : Set X) (hEq : E = ⋂ j, (W j : Set X))
    (hE : ∀ j, E ⊆ W j) {y y' : Spec (X.sectionsRingOnSubset E)}
    (h : ∀ j, (Scheme.Spec.map (X.stageToSubset W E hE ⟨j⟩).op).base y =
      (Scheme.Spec.map (X.stageToSubset W E hE ⟨j⟩).op).base y') :
    y = y' := by
  have := filtered_intersectionIndex W hdir
  obtain ⟨e, he⟩ := colimit_sectionsRing_iso_sectionsRingOnSubset X W hW hdir E hEq
  apply PrimeSpectrum.ext
  ext r
  obtain ⟨j, s, hs⟩ := Concrete.colimit_exists_rep (Scheme.sectionsRingDiagram X W) (e.inv r)
  have hr : r = X.stageToSubset W E hE j s :=
    calc
      r = e.hom (e.inv r) := (Iso.inv_hom_id_apply e r).symm
      _ = e.hom ((colimit.ι (Scheme.sectionsRingDiagram X W) j) s) := by rw [hs]
      _ = _ := congrArg (fun g ↦ g s) (he j)
  have hmem (z : Spec (X.sectionsRingOnSubset E)) :
      s ∈ ((Scheme.Spec.map (X.stageToSubset W E hE j).op).base z).asIdeal ↔
        X.stageToSubset W E hE j s ∈ z.asIdeal := Iff.rfl
  rw [hr]
  exact (hmem y).symm.trans ((Iff.of_eq
    (congrArg (fun q ↦ s ∈ q.asIdeal) (h j.val))).trans (hmem y'))

/-- If the spectrum of the stage map at `k` sends a point to the canonical image of a point of
`W k`, then for `W k ≤ W j` the stage map at `j` sends it to the canonical image of that point
of `W j`. -/
private lemma Scheme.spec_stageToSubset_base_eq_of_le {X : Scheme.{u}} [IsIndQuasiAffine X]
    {J : Type u} [Nonempty J] (W : J → X.Opens) (hW : ∀ j, IsCompact (W j : Set X))
    (hdir : ∀ i j, ∃ k, (W k : Set X) ⊆ W i ∩ W j) (E : Set X) (hEq : E = ⋂ j, (W j : Set X))
    (hE : ∀ j, E ⊆ W j) {j k : J} (h : W k ≤ W j) (y : Spec (X.sectionsRingOnSubset E))
    (x : W k) (hy : (Scheme.Spec.map (X.stageToSubset W E hE ⟨k⟩).op).base y =
      (W k).toSpecΓ.base x) :
    (Scheme.Spec.map (X.stageToSubset W E hE ⟨j⟩).op).base y =
      (W j).toSpecΓ.base ⟨x.1, h x.2⟩ := by
  have := quasiSeparatedSpace_of_isIndQuasiAffine X
  have := IsIndQuasiAffine.isQuasiAffine (W k) (hW k)
  have := IsIndQuasiAffine.isQuasiAffine (W j) (hW j)
  rw [← spec_map_res_toSpecΓ_base h x, ← hy,
    Scheme.spec_map_res_spec_stageToSubset_base W hW hdir E hEq hE h]

/-- The stalk of the restriction of an ind-quasi-affine scheme to a subset at a point is the
localization of the functions on a quasi-compact open stage at the prime of that point. -/
private lemma isLocalization_stalk_of_stage {X : Scheme.{u}} [IsIndQuasiAffine X] {J : Type u}
    (W : J → X.Opens) (hW : ∀ j, IsCompact (W j : Set X)) (E : Set X) (hEW : ∀ j, E ⊆ W j)
    (j : intersectionIndex W) (x : E)
    (g : Γ(X, W j.val) →+* (subsetLocallyRingedSpace X.toLocallyRingedSpace E).presheaf.stalk x)
    (hg : g = ((subsetLocallyRingedSpace X.toLocallyRingedSpace E).presheaf.Γgerm x).hom.comp
      (X.stageToSubset W E hEW j).hom)
    (P : Ideal Γ(X, W j.val)) (hPp : P.IsPrime)
    (hP : P = ((W j.val).toSpecΓ.base ⟨x.1, hEW j.val x.2⟩).asIdeal) :
    letI : Algebra Γ(X, W j.val)
      ((subsetLocallyRingedSpace X.toLocallyRingedSpace E).presheaf.stalk x) := g.toAlgebra
    IsLocalization P.primeCompl
      ((subsetLocallyRingedSpace X.toLocallyRingedSpace E).presheaf.stalk x) := by
  subst hg hP
  let Z := subsetLocallyRingedSpace X.toLocallyRingedSpace E
  let gamma : LocallyRingedSpace.Γ.obj (op Z) →+* Z.presheaf.stalk x :=
    (Z.presheaf.Γgerm x).hom
  let Uj := W j.val
  let xj : Uj := ⟨x.1, hEW j.val x.2⟩
  let A := Γ(Uj.toScheme, ⊤)
  let B := Γ(X, Uj)
  let eAB : A ≃+* B := Uj.topIso.commRingCatIsoToRingEquiv
  let pA : PrimeSpectrum A := Uj.toScheme.toSpecΓ.base xj
  let qB : PrimeSpectrum B := Uj.toSpecΓ.base xj
  let : pA.asIdeal.IsPrime := pA.2
  let : qB.asIdeal.IsPrime := qB.2
  have hq : qB.asIdeal = Ideal.comap eAB.symm.toRingHom pA.asIdeal := by
    change (PrimeSpectrum.comap eAB.symm.toRingHom pA).asIdeal = _
    rw [PrimeSpectrum.comap_asIdeal]
  let gammaA : A →+* Uj.toScheme.presheaf.stalk xj :=
    (Uj.toScheme.presheaf.Γgerm xj).hom
  let gammaB := gammaA.comp eAB.symm.toRingHom
  let : Algebra A (Uj.toScheme.presheaf.stalk xj) := gammaA.toAlgebra
  let : Uj.toScheme.IsQuasiAffine :=
    AlgebraicGeometry.IsIndQuasiAffine.isQuasiAffine Uj (hW j.val)
  have hLocA : IsLocalization pA.asIdeal.primeCompl
      (Uj.toScheme.presheaf.stalk xj) :=
    isLocalization_toSpecΓ_stalk (U := Uj.toScheme) xj
  let : Algebra B (Uj.toScheme.presheaf.stalk xj) := gammaB.toAlgebra
  have hLocB : IsLocalization qB.asIdeal.primeCompl
      (Uj.toScheme.presheaf.stalk xj) :=
    isLocalization_of_ringEquiv_domain eAB pA.asIdeal gammaA hLocA qB.asIdeal hq
  let eZ := stalkIsoOfPullbackSheaf (Stacks.subsetInclusion (TopCat.of X) E)
    X.toLocallyRingedSpace.sheaf x
  let eU := Uj.stalkIso xj
  let eS := eU ≪≫ eZ.symm
  let t := X.stageToSubset W E hEW j
  have ht (r : B) : eZ.hom (gamma (t r)) =
      X.toLocallyRingedSpace.presheaf.germ Uj x.1 (hEW j.val x.2) r := by
    convert stageToSubset_germ W E hEW j.val x r using 1
    rfl
  have hUloc (r : B) : eU.hom (gammaB r) =
      X.toLocallyRingedSpace.presheaf.germ Uj x.1 (hEW j.val x.2) r := by
    have hh := congrArg (fun g ↦ g (Uj.topIso.inv r))
      (Uj.germ_stalkIso_hom xj (V := ⊤) trivial)
    change eU.hom (gammaB r) =
      X.toLocallyRingedSpace.presheaf.germ (Uj.ι ''ᵁ ⊤) x.1
        ⟨xj, trivial, rfl⟩ (X.presheaf.map (eqToHom Uj.ι_image_top).op r) at hh
    exact hh.trans (X.presheaf.germ_res_apply (eqToHom Uj.ι_image_top) x.1 ⟨xj, trivial, rfl⟩ r)
  have hmap : gamma.comp t.hom = eS.hom.hom.comp gammaB := by
    ext r
    have hright : eZ.hom (eS.hom (gammaB r)) = eU.hom (gammaB r) :=
      Iso.inv_hom_id_apply (C := CommRingCat) eZ (eU.hom (gammaB r))
    have hleftE : eZ.commRingCatIsoToRingEquiv (gamma (t.hom r)) =
        eZ.commRingCatIsoToRingEquiv (eS.hom (gammaB r)) := by
      change eZ.hom (gamma (t.hom r)) = eZ.hom (eS.hom (gammaB r))
      rw [ht r, ← hUloc r, ← hright]
    exact eZ.commRingCatIsoToRingEquiv.injective hleftE
  exact isLocalization_of_ringEquiv_codomain _ gammaB hLocB eS.commRingCatIsoToRingEquiv _ hmap

/-- The unit of the `Γ`-`Spec` adjunction for locally ringed spaces is an isomorphism on the stalk
at a point as soon as that stalk is the localization of the global sections at the prime of the
point. -/
private lemma isIso_stalkMap_identityToΓSpec_of_isLocalization (Z : LocallyRingedSpace.{u})
    (x : Z) (f : LocallyRingedSpace.Γ.obj (op Z) →+* Z.presheaf.stalk x)
    (hf : f = (Z.presheaf.Γgerm x).hom)
    (hLoc : letI : Algebra (LocallyRingedSpace.Γ.obj (op Z)) (Z.presheaf.stalk x) := f.toAlgebra
      letI : (Z.toΓSpec.base x).asIdeal.IsPrime := (Z.toΓSpec.base x).2
      IsLocalization (Z.toΓSpec.base x).asIdeal.primeCompl (Z.presheaf.stalk x)) :
    IsIso ((identityToΓSpec.app Z).stalkMap x) := by
  subst hf
  let : (Z.toΓSpec.base x).asIdeal.IsPrime := (Z.toΓSpec.base x).2
  let R := unop (LocallyRingedSpace.Γ.rightOp.obj Z)
  let eR : LocallyRingedSpace.Γ.obj (op Z) ≃+* R := RingEquiv.refl _
  let specStalk :=
    ((LocallyRingedSpace.Γ.rightOp ⋙ Spec.toLocallyRingedSpace).obj Z).presheaf.stalk
      ((identityToΓSpec.app Z).base x)
  let p' := (identityToΓSpec.app Z).base x
  let : p'.asIdeal.IsPrime := p'.isPrime
  let : Algebra R
      (((LocallyRingedSpace.Γ.rightOp ⋙ Spec.toLocallyRingedSpace).obj Z).presheaf.stalk p') :=
    (StructureSheaf.toStalk R p').hom.toAlgebra
  let : IsLocalization.AtPrime specStalk p'.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (R := R) p'
  have hRel : p'.asIdeal = Ideal.comap eR.symm.toRingHom (Z.toΓSpec.base x).asIdeal := by
    ext
    rfl
  let : Algebra R (Z.presheaf.stalk x) :=
    ((Z.presheaf.Γgerm x).hom.comp eR.symm.toRingHom).toAlgebra
  let : Algebra R (((𝟭 LocallyRingedSpace).obj Z).presheaf.stalk x) :=
    (show R →+* (((𝟭 LocallyRingedSpace).obj Z).presheaf.stalk x) from
      (Z.presheaf.Γgerm x).hom.comp eR.symm.toRingHom).toAlgebra
  let : IsLocalization p'.asIdeal.primeCompl (Z.presheaf.stalk x) :=
    isLocalization_of_ringEquiv_domain eR _ (Z.presheaf.Γgerm x).hom hLoc p'.asIdeal hRel
  let : IsLocalization p'.asIdeal.primeCompl
      (((𝟭 LocallyRingedSpace).obj Z).presheaf.stalk x) := by
    change IsLocalization p'.asIdeal.primeCompl (Z.presheaf.stalk x)
    infer_instance
  have hunit :
      ((identityToΓSpec.app Z).stalkMap x).hom.comp (algebraMap R specStalk) =
        algebraMap R (Z.presheaf.stalk x) := by
    have hh : StructureSheaf.toStalk R p' ≫
        (identityToΓSpec.app Z).stalkMap x = CommRingCat.ofHom (Z.presheaf.Γgerm x).hom := by
      convert LocallyRingedSpace.toStalk_stalkMap_toΓSpec (X := Z) x using 1
      rfl
    exact congrArg (fun q : CommRingCat.of _ ⟶ CommRingCat.of _ => q.hom) hh
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (IsLocalization.bijective p'.asIdeal.primeCompl _ hunit)

/-- The canonical morphism from the restriction of an ind-quasi-affine scheme to an intersection
of a directed family of quasi-compact opens to the spectrum of its sections is an isomorphism on
stalks. -/
private theorem isIso_stalkMap_identityToΓSpec_subset {X : Scheme.{u}} [IsIndQuasiAffine X]
    {J : Type u} [Nonempty J] (W : J → X.Opens) (hW : ∀ j, IsCompact (W j : Set X))
    (hdir : ∀ i j, ∃ k, (W k : Set X) ⊆ W i ∩ W j) (E : Set X) (hE : E = ⋂ j, (W j : Set X))
    (x : E) :
    IsIso ((identityToΓSpec.app (subsetLocallyRingedSpace X.toLocallyRingedSpace E)).stalkMap
      x) := by
  let Z := subsetLocallyRingedSpace X.toLocallyRingedSpace E
  have hEW (j : J) : E ⊆ W j := hE ▸ Set.iInter_subset _ j
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_isIndQuasiAffine X
  let d := Scheme.sectionsRingDiagram X W
  obtain ⟨eR, heR⟩ := colimit_sectionsRing_iso_sectionsRingOnSubset X W hW hdir E hE
  let eΓ : colimit d ≅ LocallyRingedSpace.Γ.obj (op Z) := eR
  let p := Z.toΓSpec.base x
  let : p.asIdeal.IsPrime := p.2
  let gamma : LocallyRingedSpace.Γ.obj (op Z) →+* Z.presheaf.stalk x :=
    (Z.presheaf.Γgerm x).hom
  let rho : (colimit d : CommRingCat) →+* LocallyRingedSpace.Γ.obj (op Z) := eΓ.hom.hom
  let fC := gamma.comp rho
  let pC : Ideal ((colimit d : CommRingCat) : Type u) := Ideal.comap rho p.asIdeal
  let : pC.IsPrime := Ideal.comap_isPrime rho p.asIdeal
  have hLocC : let : Algebra (colimit d : CommRingCat) (Z.presheaf.stalk x) := fC.toAlgebra
      IsLocalization pC.primeCompl (Z.presheaf.stalk x) := by
    refine isLocalization_of_filtered_colimit (F := d) (fun i j ↦ ?_) pC fC fun j ↦ ?_
    · obtain ⟨k, hk⟩ := hdir i.val j.val
      exact ⟨⟨k⟩, (Set.subset_inter_iff.mp hk).1, (Set.subset_inter_iff.mp hk).2⟩
    · have hmapj : rho.comp (colimit.ι d j).hom = (X.stageToSubset W E hEW j).hom :=
        congrArg CommRingCat.Hom.hom (heR j)
      refine isLocalization_stalk_of_stage W hW E hEW j x _ (congrArg gamma.comp hmapj)
        (pC.comap (colimit.ι d j).hom) (Ideal.comap_isPrime _ pC) ?_
      ext r
      have hr : rho ((colimit.ι d j).hom r) = (X.stageToSubset W E hEW j).hom r :=
        RingHom.congr_fun hmapj r
      change rho ((colimit.ι d j).hom r) ∈ p.asIdeal ↔ _
      rw [hr]
      exact Iff.of_eq (congrArg (fun q ↦ r ∈ q.asIdeal)
        (Scheme.spec_stageToSubset_base_toΓSpec W E hEW j x))
  let eΓR := eΓ.commRingCatIsoToRingEquiv
  have hr (r : LocallyRingedSpace.Γ.obj (op Z)) : rho (eΓR.symm r) = r := eΓR.apply_symm_apply r
  have hQ : p.asIdeal = Ideal.comap eΓR.symm.toRingHom pC := by
    ext r
    change r ∈ p.asIdeal ↔ rho (eΓR.symm r) ∈ p.asIdeal
    rw [hr]
  have hgamma : fC.comp eΓR.symm.toRingHom = gamma := by
    ext r
    change gamma (rho (eΓR.symm r)) = gamma r
    rw [hr]
  exact isIso_stalkMap_identityToΓSpec_of_isLocalization Z x _ hgamma
    (isLocalization_of_ringEquiv_domain eΓR pC fC hLocC p.asIdeal hQ)

/-- For an upward directed family of quasi-compact opens, two points of stages which are the
canonical images of the stage coordinates of one point of the spectrum of the functions on the
intersection are the same point of the scheme. -/
private lemma Scheme.val_eq_of_spec_stageToSubset_base_eq {X : Scheme.{u}} [IsIndQuasiAffine X]
    {J : Type u} [Nonempty J] (W : J → X.Opens) (hW : ∀ j, IsCompact (W j : Set X))
    (hdir : ∀ i j, ∃ k, (W k : Set X) ⊆ W i ∩ W j) (E : Set X) (hEq : E = ⋂ j, (W j : Set X))
    (hE : ∀ j, E ⊆ W j) (hup : ∀ i j, ∃ k, W i ≤ W k ∧ W j ≤ W k)
    {y : Spec (X.sectionsRingOnSubset E)} {i j : J} {xi : W i} {xj : W j}
    (hi : (W i).toSpecΓ.base xi = (Scheme.Spec.map (X.stageToSubset W E hE ⟨i⟩).op).base y)
    (hj : (W j).toSpecΓ.base xj = (Scheme.Spec.map (X.stageToSubset W E hE ⟨j⟩).op).base y) :
    xi.1 = xj.1 := by
  obtain ⟨k, hik, hjk⟩ := hup i j
  exact val_eq_of_toSpecΓ_base_eq (hW k) (x := ⟨xi.1, hik xi.2⟩) (y := ⟨xj.1, hjk xj.2⟩)
    ((Scheme.spec_stageToSubset_base_eq_of_le W hW hdir E hEq hE hik y xi hi.symm).symm.trans
      (Scheme.spec_stageToSubset_base_eq_of_le W hW hdir E hEq hE hjk y xj hj.symm))

/-- For an upward directed family of quasi-compact opens, a point of the spectrum of the functions
on the intersection whose coordinate at one stage is the canonical image of a point of the
intersection is the canonical image of that point. -/
private lemma Scheme.exists_toΓSpec_eq_of_spec_stageToSubset_base {X : Scheme.{u}}
    [IsIndQuasiAffine X]
    {J : Type u} [Nonempty J] (W : J → X.Opens) (hW : ∀ j, IsCompact (W j : Set X))
    (hdir : ∀ i j, ∃ k, (W k : Set X) ⊆ W i ∩ W j) (E : Set X) (hEq : E = ⋂ j, (W j : Set X))
    (hE : ∀ j, E ⊆ W j) (hup : ∀ i j, ∃ k, W i ≤ W k ∧ W j ≤ W k)
    (y : Spec (X.sectionsRingOnSubset E)) (j₀ : J) (x₀ : W j₀)
    (hx₀ : (W j₀).toSpecΓ.base x₀ = (Scheme.Spec.map (X.stageToSubset W E hE ⟨j₀⟩).op).base y)
    (hx₀E : x₀.1 ∈ E) :
    ∃ x : E, (subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec.base x = y := by
  have := quasiSeparatedSpace_of_isIndQuasiAffine X
  refine ⟨⟨x₀.1, hx₀E⟩,
    (Scheme.eq_of_spec_stageToSubset_base_eq W hW hdir E hEq hE (y := y) fun j ↦ ?_).symm⟩
  obtain ⟨k, hik, hjk⟩ := hup j₀ j
  obtain ⟨xj, hjp, hjx⟩ := exists_toSpecΓ_eq_of_spec_map_res (hW k) (hW j) hjk _ _
    ((Scheme.spec_map_res_spec_stageToSubset_base W hW hdir E hEq hE hjk y).trans
      (Scheme.spec_stageToSubset_base_eq_of_le W hW hdir E hEq hE hik y x₀ hx₀.symm))
    (hE j hx₀E)
  have hpt : xj = ⟨x₀.1, hE j hx₀E⟩ := Subtype.ext hjx
  rw [hjp, hpt]
  exact (Scheme.spec_stageToSubset_base_toΓSpec W E hE ⟨j⟩ ⟨x₀.1, hx₀E⟩).symm

/-- The spectrum of a stage map pulls back the canonical image of a subset of the intersection
of a directed family of quasi-compact opens to its canonical image in the spectrum of the
functions on the intersection. -/
private lemma Scheme.preimage_spec_stageToSubset_base_image_toSpecΓ {X : Scheme.{u}}
    [IsIndQuasiAffine X] {J : Type u} [Nonempty J] (W : J → X.Opens)
    (hW : ∀ j, IsCompact (W j : Set X)) (hdir : ∀ i j, ∃ k, (W k : Set X) ⊆ W i ∩ W j)
    (E : Set X) (hEq : E = ⋂ j, (W j : Set X)) (hE : ∀ j, E ⊆ W j) (j : J) {O : Set X}
    (hOE : O ⊆ E) :
    (Scheme.Spec.map (X.stageToSubset W E hE ⟨j⟩).op).base ⁻¹'
        ((W j).toSpecΓ.base '' {x : W j | (x : X) ∈ O}) =
      (subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec.base ''
        {x : E | (x : X) ∈ O} := by
  have := quasiSeparatedSpace_of_isIndQuasiAffine X
  apply Set.Subset.antisymm
  · rintro y ⟨z, hzO, hzy⟩
    let x : E := ⟨z.1, hOE hzO⟩
    refine ⟨x, hzO,
      (Scheme.eq_of_spec_stageToSubset_base_eq W hW hdir E hEq hE (y := y) fun l ↦ ?_).symm⟩
    obtain ⟨k, hk⟩ := hdir j l
    have hkj : W k ≤ W j := hk.trans Set.inter_subset_left
    have hkl : W k ≤ W l := hk.trans Set.inter_subset_right
    obtain ⟨xk, hxk, hxkv⟩ := exists_toSpecΓ_eq_of_spec_map_res (hW j) (hW k) hkj _ z
      ((Scheme.spec_map_res_spec_stageToSubset_base W hW hdir E hEq hE hkj y).trans hzy.symm)
      (hE k x.2)
    rw [Scheme.spec_stageToSubset_base_eq_of_le W hW hdir E hEq hE hkl y xk hxk,
      Scheme.spec_stageToSubset_base_toΓSpec W E hE ⟨l⟩ x]
    congr 1
    exact Subtype.ext hxkv
  · rintro y ⟨x, hxO, rfl⟩
    exact ⟨⟨x.1, hE j x.2⟩, hxO, (Scheme.spec_stageToSubset_base_toΓSpec W E hE ⟨j⟩ x).symm⟩

/-- The canonical map from a subset contained in each member of a family of quasi-compact opens of
an ind-quasi-affine scheme to the spectrum of its functions is injective. -/
private lemma Scheme.toΓSpec_base_injective_subset {X : Scheme.{u}} [IsIndQuasiAffine X]
    {J : Type u}
    (W : J → X.Opens) (hW : ∀ j, IsCompact (W j : Set X)) (E : Set X) (hE : ∀ j, E ⊆ W j)
    (j : J) :
    Function.Injective (subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec.base := by
  intro x y hxy
  exact Subtype.ext <| val_eq_of_toSpecΓ_base_eq (hW j) (x := ⟨x.1, hE j x.2⟩)
    (y := ⟨y.1, hE j y.2⟩)
    ((Scheme.spec_stageToSubset_base_toΓSpec W E hE ⟨j⟩ x).symm.trans
      ((congrArg (fun z ↦ (Scheme.Spec.map (X.stageToSubset W E hE ⟨j⟩).op).base z) hxy).trans
        (Scheme.spec_stageToSubset_base_toΓSpec W E hE ⟨j⟩ y)))

/-- A map from a subspace `E ⊆ U` onto a subset `S` is open into `S` as soon as, after a
continuous map, it agrees with an open embedding of `U`. -/
private theorem isOpenMap_codRestrict_of_comp_eq {X Y T : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace T] {E U : Set X} (hEU : E ⊆ U) (S : Set Y)
    (g : E → Y) (hgS : ∀ x, g x ∈ S) (hsurj : ∀ y ∈ S, ∃ x, g x = y) {q : Y → T}
    (hq : Continuous q) {e : U → T} (he : Topology.IsOpenEmbedding e)
    (hcomp : ∀ x, q (g x) = e ⟨x.1, hEU x.2⟩) :
    IsOpenMap fun x ↦ (⟨g x, hgS x⟩ : S) := by
  intro A hA
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hA
  refine isOpen_induced_iff.mpr ⟨q ⁻¹' (e '' {z | (z : X) ∈ O}),
    (he.isOpenMap _ (hO.preimage continuous_subtype_val)).preimage hq, ?_⟩
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨z, hzO, hz⟩
    obtain ⟨x, rfl⟩ := hsurj y hy
    have hv : (⟨x.1, hEU x.2⟩ : U) = z := he.injective ((hcomp x).symm.trans hz.symm)
    exact ⟨x, by rwa [← hv] at hzO, rfl⟩
  · rintro ⟨x, hxO, hx⟩
    obtain rfl : g x = y := congrArg Subtype.val hx
    exact ⟨⟨x.1, hEU x.2⟩, hxO, (hcomp x).symm⟩

/-- **Stacks Project, Tag 0API.** The canonical map from a nonempty intersection
of quasi-compact opens in an ind-quasi-affine scheme to the spectrum of its ring
of sections identifies it, as a locally ringed space, with an intersection of
quasi-compact opens in that spectrum.  Each comparison map to the spectrum of a
stage is the spectrum of the restriction map of functions from that stage. -/
@[stacks 0API "intersection_embedding"]
theorem exists_iInter_iso_iInter_in_specΓ
    {X : Scheme.{u}} [AlgebraicGeometry.IsIndQuasiAffine X]
    {I : Type v} [Nonempty I] (U : I → X.Opens)
    (hU : ∀ i, IsCompact (U i : Set X)) :
    let E : Set X := ⋂ i, (U i : Set X)
    let Z := subsetLocallyRingedSpace X.toLocallyRingedSpace E
    let Y := Spec.toLocallyRingedSpace.obj (op (LocallyRingedSpace.Γ.obj (op Z)))
    ∃ (p : ∀ i, Y ⟶ Spec.toLocallyRingedSpace.obj (op Γ(X, U i)))
      (V : I → Opens Y),
      (∀ i, IsCompact (V i : Set Y)) ∧
      (∀ i, (V i : Set Y) = (p i).base ⁻¹' Set.range (U i).toSpecΓ.base) ∧
      (∀ i (x : E), (p i).base (Z.toΓSpec.base x) =
        (U i).toSpecΓ.base ⟨x.1, Set.mem_iInter.mp x.2 i⟩) ∧
      (∀ i (W : Set X), IsOpen W → W ⊆ E →
        (p i).base ⁻¹' ((U i).toSpecΓ.base ''
          {x : U i | (x : X) ∈ W}) =
        Z.toΓSpec.base '' {x : E | (x : X) ∈ W}) ∧
      (∀ i, p i = (Scheme.Spec.map (X.openToSubset (U i) E
        (Set.iInter_subset (fun k ↦ (U k : Set X)) i)).op).toLRSHom) ∧
      ∃ e : Z ≅ subsetLocallyRingedSpace Y (⋂ i, (V i : Set Y)),
          e.hom.toHom ≫ ofSubset Y (⋂ i, (V i : Set Y)) =
            (identityToΓSpec.app Z).toHom := by
  classical
  let E : Set X := ⋂ i, (U i : Set X)
  let Z := subsetLocallyRingedSpace X.toLocallyRingedSpace E
  let Y := Spec.toLocallyRingedSpace.obj (op (LocallyRingedSpace.Γ.obj (op Z)))
  let J : Type u := compactOpenNeighborhoods E
  let W : J → X.Opens := fun j => j.1
  have hJne : Nonempty J := compactOpenNeighborhoods_nonempty U hU E rfl
  have hJdir : ∀ i j : J, ∃ k : J, (W k : Set X) ⊆ W i ∩ W j :=
    compactOpenNeighborhoods_directed E
  have hJE : E = ⋂ j : J, (W j : Set X) := compactOpenNeighborhoods_iInter U hU E rfl
  have hW (j : J) : IsCompact (W j : Set X) := j.2.1
  have hEW (j : J) : E ⊆ W j := j.2.2
  have hJup (i j : J) : ∃ k : J, W i ≤ W k ∧ W j ≤ W k :=
    ⟨⟨W i ⊔ W j, (hW i).union (hW j), fun _ hx ↦ Or.inl (hEW i hx)⟩, le_sup_left, le_sup_right⟩
  let ji (i : I) : J := ⟨U i, hU i, fun _ hx ↦ Set.mem_iInter.mp hx i⟩
  let p (i : I) : Y ⟶ Spec.toLocallyRingedSpace.obj (op Γ(X, U i)) :=
    (Scheme.Spec.map (X.stageToSubset W E hEW ⟨ji i⟩).op).toLRSHom
  have hrange (i : I) : IsOpen (Set.range (U i).toSpecΓ.base) := by
    let : IsOpenImmersion (U i).toSpecΓ :=
      isOpenImmersion_toSpecΓ_of_isIndQuasiAffine X (U i) (hU i)
    exact (U i).toSpecΓ.isOpenEmbedding.isOpen_range
  let V (i : I) : Opens Y :=
    ⟨(p i).base ⁻¹' Set.range (U i).toSpecΓ.base, (hrange i).preimage (p i).base.hom.2⟩
  have hcompat (i : I) (x : E) : (p i).base (Z.toΓSpec.base x) =
      (U i).toSpecΓ.base ⟨x.1, Set.mem_iInter.mp x.2 i⟩ :=
    Scheme.spec_stageToSubset_base_toΓSpec W E hEW ⟨ji i⟩ x
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hsurj (y : Y) (hy : y ∈ ⋂ i, (V i : Set Y)) : ∃ x : E, Z.toΓSpec.base x = y := by
    obtain ⟨x₀, hx₀⟩ := Set.mem_iInter.mp hy i₀
    have hx₀E : x₀.1 ∈ E := Set.mem_iInter.mpr fun i ↦ (Set.mem_iInter.mp hy i).elim
      fun xi hxi ↦ Scheme.val_eq_of_spec_stageToSubset_base_eq W hW hJdir E hJE hEW hJup
        (i := ji i) (j := ji i₀) hxi hx₀ ▸ xi.2
    exact Scheme.exists_toΓSpec_eq_of_spec_stageToSubset_base W hW hJdir E hJE hEW hJup y
      (ji i₀) x₀ hx₀ hx₀E
  refine ⟨p, V, ?_, fun i ↦ rfl, hcompat, fun i O _ hOE ↦
    Scheme.preimage_spec_stageToSubset_base_image_toSpecΓ W hW hJdir E hJE hEW (ji i) hOE,
    fun i ↦ rfl, ?_⟩
  · intro i
    have hCompactImage : IsCompact (Set.range (U i).toSpecΓ.base) := by
      let : CompactSpace (U i) := isCompact_iff_compactSpace.mp (hU i)
      rw [← Set.image_univ]
      exact isCompact_univ.image ((U i).toSpecΓ.base.hom.continuous_toFun)
    exact (inferInstance : QuasiCompact (Scheme.Spec.map
      (X.stageToSubset W E hEW ⟨ji i⟩).op)).isCompact_preimage _ (hrange i) hCompactImage
  · let S : Set Y := ⋂ i, (V i : Set Y)
    have hfS (z : Z) : (identityToΓSpec.app Z).base z ∈ S := by
      refine Set.mem_iInter.mpr fun i ↦ ?_
      change (p i).base (Z.toΓSpec.base z) ∈ Set.range (U i).toSpecΓ.base
      rw [hcompat i z]
      exact ⟨⟨z.1, Set.mem_iInter.mp z.2 i⟩, rfl⟩
    have := isOpenImmersion_toSpecΓ_of_isIndQuasiAffine X (U i₀) (hU i₀)
    exact exists_iso_subsetLocallyRingedSpace S _ hfS
      (Scheme.toΓSpec_base_injective_subset W hW E hEW (ji i₀)) hsurj
      (isOpenMap_codRestrict_of_comp_eq (Set.iInter_subset (fun k ↦ (U k : Set X)) i₀) S _ hfS
        hsurj (p i₀).base.hom.continuous (U i₀).toSpecΓ.isOpenEmbedding (hcompat i₀))
      fun x ↦ isIso_stalkMap_identityToΓSpec_subset W hW hJdir E hJE x

/-- **Stacks Project, Tag 0API (open image).** The canonical map from an intersection of a
nonempty family of quasi-compact opens in an ind-quasi-affine scheme to the spectrum of its
global sections sends subsets which are open in the ambient scheme to open subsets. -/
@[stacks 0API "open_image"]
theorem isOpen_image_toΓSpec_of_isOpen
    (X : Scheme.{u}) [AlgebraicGeometry.IsIndQuasiAffine X]
    {I : Type v} [Nonempty I] (U : I → X.Opens)
    (hU : ∀ i, IsCompact (U i : Set X))
    (E W : Set X) (hE : E = ⋂ i, (U i : Set X))
    (hWE : W ⊆ E) (hW : IsOpen W) :
    IsOpen
      ((subsetLocallyRingedSpace
          X.toLocallyRingedSpace E).toΓSpec.base ''
        { x : E | (x : X) ∈ W }) := by
  subst E
  obtain ⟨p, _, _, _, _, hWpre, _, _⟩ :=
    exists_iInter_iso_iInter_in_specΓ (X := X) U hU
  let i : I := Classical.choice ‹Nonempty I›
  rw [← hWpre i W hW hWE]
  let := isOpenImmersion_toSpecΓ_of_isIndQuasiAffine X (U i) (hU i)
  exact ((U i).toSpecΓ.isOpenEmbedding.isOpenMap _
    (hW.preimage (U i).ι.continuous)).preimage ((p i).1.1).hom.continuous

end AlgebraicGeometry
