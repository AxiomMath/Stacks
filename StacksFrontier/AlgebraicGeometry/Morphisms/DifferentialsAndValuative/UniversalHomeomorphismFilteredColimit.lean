module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.IndPresentation.FiniteStage
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Subalgebra
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation

/-!
# Universal homeomorphisms of affine schemes as filtered colimits

A ring map which induces a universal homeomorphism on spectra is a filtered colimit of finitely
presented ring maps with the same property. If it moreover induces isomorphisms on all residue
fields, its target is a filtered colimit of finitely presented algebras having both properties.

The target is written as the directed union of its finitely generated subalgebras over the
source; each of those is a quotient of a polynomial algebra, and the spectrum of each is a
universal homeomorphism over the base because the whole spectrum morphism is. Each finitely
generated subalgebra is in turn a directed colimit of finitely presented algebras with surjective
transition maps, so the finite-stage criterion applies and produces a finitely presented stage
with the same properties, through which the given finitely presented algebra factors.

## Main results

* `AlgebraicGeometry.isFilteredColimit_finitePresentation_universalHomeomorphism`: the
  filtered-colimit presentation of a universal homeomorphism of affine schemes.
* `AlgebraicGeometry.ind_finitePresentation_residueFieldMap_isIso_universalHomeomorphism`: the
  same presentation with the residue-field condition imposed at every stage.

## Implementation notes

A filtered-colimit presentation is expressed by `CategoryTheory.ObjectProperty.ind` in the
category of algebras under the source ring, so its stages and structure maps are part of a
colimit presentation rather than being chosen independently. At each stage, finite presentation
is imposed on the structure map, while the geometric conditions are imposed on the induced
morphism of affine spectra.

## References

* [Stacks Project, Tag 0EUJ](https://stacks.math.columbia.edu/tag/0EUJ)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace DirectedPresentation

open Limits

noncomputable section

variable {R : CommRingCat.{u}} {Λ : Type u} [PartialOrder Λ] [Nonempty Λ]
  [IsDirectedOrder Λ]
  (G : Λ → Type u) [∀ l, CommRing (G l)] [∀ l, Algebra ↑R (G l)]
  (f : ∀ i j, i ≤ j → G i →ₐ[↑R] G j)
  [DirectedSystem G fun i j h ↦ ⇑(f i j h)]

private def diagram : Λ ⥤ CommRingCat.{u} where
  obj l := CommRingCat.of (G l)
  map {i j} h := CommRingCat.ofHom (f i j h.le).toRingHom
  map_id l := by
    ext x
    exact DirectedSystem.map_self (f := fun i j h ↦ ⇑(f i j h)) x
  map_comp {i j k} h k := by
    ext x
    exact (DirectedSystem.map_map (f := fun i j h ↦ ⇑(f i j h)) h.le k.le x).symm

private def structureMap : (Functor.const Λ).obj R ⟶ diagram G f where
  app l := CommRingCat.ofHom (algebraMap ↑R (G l))
  naturality i j h := by ext x; exact ((f i j h.le).commutes x).symm

variable {T : Type u} [CommRing T] [Algebra ↑R T] (g : ∀ l, G l →ₐ[↑R] T)
  (hg : ∀ i j h x, g j (f i j h x) = g i x)

private def cocone : Cocone (diagram G f) where
  pt := CommRingCat.of T
  ι :=
    { app l := CommRingCat.ofHom (g l).toRingHom
      naturality := fun i j h ↦ by ext x; exact hg i j h.le x }

private def directLimitCocone : Cocone (diagram G f) :=
  cocone G f (DirectLimit.Algebra.of G f) fun _ _ h x ↦ DirectLimit.Algebra.of_f h x

private def directLimitIsColimit : IsColimit (directLimitCocone G f) where
  desc t := CommRingCat.ofHom <| DirectLimit.Ring.lift G f ↑t.pt (fun l ↦ (t.ι.app l).hom)
    fun _ _ h x ↦ congr($(t.w (homOfLE h)).hom x)
  fac t l := by ext x; rfl
  uniq t m hm := by
    ext x
    induction x using DirectLimit.induction with | _ l y => exact congr($(hm l).hom y)

private def isColimit
    (hbij : Function.Bijective (DirectLimit.Algebra.lift G f T g hg)) :
    IsColimit (Under.liftCocone (diagram G f) (structureMap G f) (cocone G f g hg)
      (CommRingCat.ofHom (algebraMap ↑R T))
      fun l ↦ by ext x; exact (g l).commutes x) :=
  Under.isColimitLiftCocone _ _ _ _ _
    ((directLimitIsColimit G f).ofIsoColimit <| Cocone.ext
      (RingEquiv.ofBijective (DirectLimit.Algebra.lift G f T g hg).toRingHom hbij).toCommRingCatIso
      fun _ ↦ by ext x; rfl)

private def algebraDiagram : Λ ⥤ CommAlgCat.{u} ↑R where
  obj l := CommAlgCat.of ↑R (G l)
  map {i j} h := CommAlgCat.ofHom (f i j h.le)
  map_id l := by
    ext x
    exact DirectedSystem.map_self (f := fun i j h ↦ ⇑(f i j h)) x
  map_comp {i j k} h k := by
    ext x
    exact (DirectedSystem.map_map (f := fun i j h ↦ ⇑(f i j h)) h.le k.le x).symm

private def algebraCocone : Cocone (algebraDiagram G f) where
  pt := CommAlgCat.of ↑R T
  ι :=
    { app l := CommAlgCat.ofHom (g l)
      naturality := fun i j h ↦ by ext x; exact hg i j h.le x }

private def algebraDirectLimitCocone : Cocone (algebraDiagram G f) :=
  algebraCocone G f (DirectLimit.Algebra.of G f) fun _ _ h x ↦ DirectLimit.Algebra.of_f h x

private def algebraDirectLimitIsColimit : IsColimit (algebraDirectLimitCocone G f) where
  desc t := CommAlgCat.ofHom <| DirectLimit.Algebra.lift G f ↑t.pt
    (fun l ↦ (t.ι.app l).hom) (fun _ _ h x ↦ congr($(t.w (homOfLE h)).hom x))
  fac t l := by ext x; rfl
  uniq t m hm := by
    ext x
    induction x using DirectLimit.induction with | _ l y => exact congr($(hm l).hom y)

private def algebraIsColimit
    (hbij : Function.Bijective (DirectLimit.Algebra.lift G f T g hg)) :
    IsColimit (algebraCocone G f g hg) :=
  (algebraDirectLimitIsColimit G f).ofIsoColimit <| Cocone.ext
    (CommAlgCat.isoMk (AlgEquiv.ofBijective (DirectLimit.Algebra.lift G f T g hg) hbij))
    fun _ ↦ by ext x; rfl

end

end DirectedPresentation

/-- A ring map inducing a universal homeomorphism on spectra is a filtered colimit of finitely
presented ring maps which induce universal homeomorphisms on spectra. -/
@[stacks 0EUJ "universal_homeomorphism_filtered_colimit"]
public theorem isFilteredColimit_finitePresentation_universalHomeomorphism
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom f).op)) :
    ObjectProperty.ind.{u}
      (fun C : Under (CommRingCat.of A) ↦
        C.hom.hom.FinitePresentation ∧
          UniversalHomeomorphism (Scheme.Spec.map C.hom.op))
      (Under.mk (CommRingCat.ofHom f)) := by
  rw [CommRingCat.ind_under_iff_exists_factorization _ (fun _ h ↦ h.1)]
  intro C hC φ
  let : Algebra A B := f.toAlgebra
  let : Algebra A C.right := C.hom.hom.toAlgebra
  let ψ : C.right →ₐ[A] B :=
    ⟨φ.right.hom, fun a ↦ congr($(Under.w φ).hom a)⟩
  let B' : Subalgebra A B := ψ.range
  let q : C.right →ₐ[A] B' := ψ.rangeRestrict
  let inc : B' →ₐ[A] B := B'.val
  let : Algebra.FinitePresentation A C.right :=
    RingHom.finitePresentation_algebraMap.mp hC
  let : Algebra.FiniteType A B' :=
    Algebra.FiniteType.of_surjective q ψ.rangeRestrict_surjective
  let : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op) :=
    universalHomeomorphism_specMap_subalgebra B'
  obtain ⟨Λ, _, _, _, G, _, _, t, _, g, hg, hfp, hsurj, hbij⟩ :=
    Algebra.exists_directedSystem_finitePresentation_lift_bijective A B'
  let D : Λ ⥤ Under (CommRingCat.of A) :=
    Under.lift (DirectedPresentation.diagram (R := CommRingCat.of A) G t)
      (DirectedPresentation.structureMap (R := CommRingCat.of A) G t)
  let c : Cocone D := Under.liftCocone
    (DirectedPresentation.diagram (R := CommRingCat.of A) G t)
    (DirectedPresentation.structureMap (R := CommRingCat.of A) G t)
    (DirectedPresentation.cocone (R := CommRingCat.of A) G t g hg)
    (CommRingCat.ofHom (algebraMap A B')) (fun l ↦ by ext x; exact (g l).commutes x)
  have hc : IsColimit c :=
    DirectedPresentation.isColimit (R := CommRingCat.of A) G t g hg hbij
  let DA : Λ ⥤ CommAlgCat.{u} A :=
    DirectedPresentation.algebraDiagram (R := CommRingCat.of A) G t
  let cA : Cocone DA :=
    DirectedPresentation.algebraCocone (R := CommRingCat.of A) G t g hg
  have hcA : IsColimit cA :=
    DirectedPresentation.algebraIsColimit (R := CommRingCat.of A) G t g hg hbij
  let : Category.{u} (ULift.{u + 1} Λ) := {
    Hom X Y := ULift.{u} (PLift (X.down ≤ Y.down))
    id X := ⟨⟨le_rfl⟩⟩
    comp p q := ⟨⟨p.down.down.trans q.down.down⟩⟩ }
  let eI : Λ ≌ ULift.{u + 1} Λ :=
    { functor :=
        { obj := ULift.up
          map := fun k ↦ ⟨⟨k.le⟩⟩ }
      inverse :=
        { obj := ULift.down
          map := fun k ↦ homOfLE k.down.down }
      unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
      counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) }
  let : IsFiltered (ULift.{u + 1} Λ) := IsFiltered.of_equivalence eI
  let DA' : ULift.{u + 1} Λ ⥤ CommAlgCat.{u} A := eI.inverse ⋙ DA
  let cA' : Cocone DA' := cA.whisker eI.inverse
  have hcA' : IsColimit cA' := hcA.whiskerEquivalence eI.symm
  obtain ⟨i, hi⟩ := eventually_universalHomeomorphism_of_isColimit
    DA' cA'.ι hcA' (fun l ↦ hfp (eI.inverse.obj l)) (fun {_ _} k ↦ by
      show Function.Surjective (t _ _ _)
      exact hsurj inferInstance _ _ (eI.inverse.map k).le)
  obtain ⟨l, σ, hσ⟩ :=
    (((CommRingCat.isFinitelyPresentable_under_tfae C).out 1 2).mp hC :
      IsFinitelyPresentable.{u} C).exists_hom_of_isColimit hc
    (Under.homMk (CommRingCat.ofHom q.toRingHom) (by ext x; exact q.commutes x))
  let σ' : C.right →ₐ[A] G l :=
    { toRingHom := σ.right.hom
      commutes' := fun x ↦ congr($(Under.w σ).hom x) }
  obtain ⟨j, hlj, hij⟩ := exists_ge_ge l (eI.inverse.obj i)
  have hU := hi (eI.functor.map (homOfLE hij))
  change UniversalHomeomorphism
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (G j))).op) at hU
  refine ⟨Under.mk (CommRingCat.ofHom (algebraMap A (G j))),
    Under.homMk (CommRingCat.ofHom ((t l j hlj).comp σ').toRingHom)
      (by ext x; exact ((t l j hlj).comp σ').commutes x),
    Under.homMk (CommRingCat.ofHom ((inc.comp (g j)).toRingHom))
      (by ext x; exact (inc.comp (g j)).commutes x), ?_, ?_⟩
  · ext x
    have hs := congr($(hσ).right.hom x)
    change g l (σ' x) = q x at hs
    show inc (g j (t l j hlj (σ' x))) = φ.right.hom x
    rw [hg l j hlj]
    exact congrArg inc hs
  · refine ⟨?_, hU⟩
    show (algebraMap A (G j)).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr (hfp j)


private def directLimitDiagram {R : Type u} [CommRing R] {Λ : Type u}
    [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type u) [∀ l, CommRing (G l)] [∀ l, Algebra R (G l)]
    (f : ∀ i j, i ≤ j → G i →ₐ[R] G j)
    [DirectedSystem G fun i j h ↦ ⇑(f i j h)] : Λ ⥤ CommAlgCat.{u} R where
  obj l := CommAlgCat.of R (G l)
  map {i j} h := CommAlgCat.ofHom (f i j h.le)
  map_id i := by ext x; exact DirectedSystem.map_self (f := fun i j h ↦ ⇑(f i j h)) x
  map_comp {i j k} hij hjk := by
    ext x
    exact (DirectedSystem.map_map (f := fun i j h ↦ ⇑(f i j h)) hij.le hjk.le x).symm


open Limits

noncomputable section

/-- A ring map which is a universal homeomorphism on spectra and induces isomorphisms on
residue fields is a filtered colimit of finitely presented ring maps with both properties. -/
@[stacks 0EUJ "residue_field_isomorphism_filtered_colimit"]
public theorem ind_finitePresentation_residueFieldMap_isIso_universalHomeomorphism
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hres : ∀ x : Spec (.of B),
      IsIso ((Scheme.Spec.map (CommRingCat.ofHom f).op).residueFieldMap x))
    (huh : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom f).op)) :
    ObjectProperty.ind.{u}
      (fun C : Under (CommRingCat.of A) ↦
        C.hom.hom.FinitePresentation ∧
          (UniversalHomeomorphism (Scheme.Spec.map C.hom.op) ∧
            ∀ x : Spec C.right,
              IsIso ((Scheme.Spec.map C.hom.op).residueFieldMap x)))
      (Under.mk (CommRingCat.ofHom f)) := by
  let : Algebra A B := f.toAlgebra
  rw [CommRingCat.ind_under_iff_exists_factorization _ (fun _ h ↦ h.1)]
  intro C hC k
  let : Algebra A C.right := C.hom.hom.toAlgebra
  let φ : C.right →ₐ[A] B :=
    { k.right.hom with
      commutes' := fun a ↦ congrArg (fun q ↦ q.hom a) (Under.w k) }
  let B' : Subalgebra A B := φ.range
  let ψ : C.right →ₐ[A] B' := φ.rangeRestrict
  let ιB : B' →ₐ[A] B := B'.val
  have : Algebra.FiniteType A C.right :=
    RingHom.FiniteType.of_finitePresentation
      (RingHom.finitePresentation_algebraMap.mpr hC)
  let : Algebra.FiniteType A B' :=
    Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) := huh
  have : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op) :=
    universalHomeomorphism_specMap_subalgebra B'
  obtain ⟨Λ, _, _, _, G, _, _, d, _, g, hg, hfp, hsurj, hbij⟩ :=
    Algebra.exists_directedSystem_finitePresentation_lift_bijective A B'
  let D := DirectedPresentation.algebraDiagram (R := CommRingCat.of A) G d
  let c := DirectedPresentation.algebraCocone (R := CommRingCat.of A) G d g hg
  have hc : IsColimit c :=
    DirectedPresentation.algebraIsColimit (R := CommRingCat.of A) G d g hg hbij
  let cU := (commAlgCatEquivUnder (CommRingCat.of A)).functor.mapCocone c
  have hcU : IsColimit cU := isColimitOfPreserves
    (commAlgCatEquivUnder (CommRingCat.of A)).functor hc
  let k' : C ⟶ cU.pt := Under.homMk (CommRingCat.ofHom ψ.toRingHom) (by
    ext a
    exact ψ.commutes a)
  obtain ⟨i, q, hq⟩ :=
    (((CommRingCat.isFinitelyPresentable_under_tfae C).out 1 2).mp hC :
      IsFinitelyPresentable.{u} C).exists_hom_of_isColimit hcU k'
  change C ⟶ Under.mk (CommRingCat.ofHom (algebraMap A (G i))) at q
  let I := ULift.{u + 1} Λ
  let : Category.{u} I := {
    Hom X Y := ULift.{u} (PLift (X.down ≤ Y.down))
    id _ := ULift.up ⟨le_rfl⟩
    comp a b := ULift.up ⟨a.down.down.trans b.down.down⟩ }
  let down : I ⥤ Λ := {
    obj x := x.down
    map a := homOfLE a.down.down }
  let up : Λ ⥤ I := {
    obj x := ULift.up x
    map a := ULift.up ⟨a.le⟩ }
  let e : I ≌ Λ := {
    functor := down
    inverse := up
    unitIso := NatIso.ofComponents fun _ ↦
      { hom := ULift.up ⟨le_rfl⟩, inv := ULift.up ⟨le_rfl⟩ }
    counitIso := NatIso.ofComponents fun _ ↦ Iso.refl _ }
  let DL := down ⋙ D
  let cL := c.whisker down
  have hcL : IsColimit cL := hc.whiskerEquivalence e
  obtain ⟨i₀, hi₀⟩ :=
    eventually_universalHomeomorphism_and_isIso_residueFieldMap_of_isColimit
      (I := I) (B := DL) cL.ι hcL (fun j ↦ hfp j.down)
        (fun {i j} a ↦ by
          show Function.Surjective (d i.down j.down a.down.down)
          exact hsurj inferInstance _ _ _)
        (isIso_residueFieldMap_specMap_subalgebra
          (A := A) (B := B) hres B')
  obtain ⟨j, hij, hi₀j⟩ := exists_ge_ge i i₀.down
  obtain ⟨huhj, hresj⟩ := hi₀ (ULift.up ⟨hi₀j⟩)
  dsimp [DL, down, D, DirectedPresentation.algebraDiagram] at huhj hresj
  let Bj : Under (CommRingCat.of A) :=
    Under.mk (CommRingCat.ofHom (algebraMap A (G j)))
  let qj : C ⟶ Bj := Under.homMk
    (CommRingCat.ofHom ((d i j hij).toRingHom.comp q.right.hom)) (by
      ext a
      show d i j hij (q.right.hom (C.hom.hom a)) = algebraMap A (G j) a
      rw [show q.right.hom (C.hom.hom a) = algebraMap A (G i) a from
        congr($(Under.w q).hom a)]
      exact (d i j hij).commutes a)
  let rj : Bj ⟶ Under.mk (CommRingCat.ofHom f) := Under.homMk
    (CommRingCat.ofHom ((ιB.comp (g j)).toRingHom)) (by ext a; exact (ιB.comp (g j)).commutes a)
  refine ⟨Bj, qj, rj, ?_, by simpa [Bj] using hfp j, huhj, hresj⟩
  ext x
  have eq1 := congrArg (fun z ↦ z.right.hom x) hq
  change g i (q.right.hom x) = ψ x at eq1
  show ιB (g j (d i j hij (q.right.hom x))) = k.right.hom x
  rw [hg i j hij]
  exact congrArg ιB eq1

end

end AlgebraicGeometry

end
