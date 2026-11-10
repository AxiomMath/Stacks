module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.RingHom.Etale
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.EtaleCoequalizer
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Etale.Lifting

/-!
# The category of étale algebras over a ring

For a commutative ring `A`, the étale `A`-algebras form a full subcategory `EtaleUnder A` of
the category of commutative rings under `A`.  This file records the three properties of that
category which make it usable as an index category for a filtered colimit: it is essentially
small, it is filtered, and each of its objects is a finitely presentable `A`-algebra.  It also
records that every étale algebra over a quotient `A ⧸ I` is itself the quotient by `I` of an
étale `A`-algebra.

## Main definitions

* `AlgebraicGeometry.ProEtale.EtaleUnder`: the category of étale algebras over a ring.

## Main results

* `AlgebraicGeometry.ProEtale.etaleUnder_essentiallySmall`: essential smallness.
* `AlgebraicGeometry.ProEtale.etaleUnder_isFiltered`: filteredness.
* `AlgebraicGeometry.ProEtale.etaleUnder_finitelyPresentable`: every étale algebra is a
  finitely presentable object.
* `AlgebraicGeometry.ProEtale.etaleUnder_quotient_lift`: an étale algebra over `A ⧸ I` is the
  quotient by `I` of an étale `A`-algebra.

## Implementation notes

Essential smallness is deduced from the corresponding statement for finitely presented
algebras, where the witnessing set is the set of standard presentations
`A[x₀, …, xₙ₋₁] ⧸ (s)` indexed by a number of variables and a finite set of relations.

## References

* [Stacks Project, Tag 097P](https://stacks.math.columbia.edu/tag/097P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- The full subcategory of `A`-algebras — commutative rings under `A` — whose structure
map is étale. -/
public abbrev EtaleUnder (A : Type u) [CommRing A] :=
  (CommRingCat.etale.underObj (X := CommRingCat.of A)).FullSubcategory

/-- The index type for standard finite presentations of an `A`-algebra: a number of variables
together with a finite set of polynomial relations among them. -/
private abbrev EtalePresentationIndex (A : Type u) [CommRing A] :=
  Σ n : ℕ, Finset (MvPolynomial (Fin n) A)

/-- The `A`-algebra `A[x₀, …, xₙ₋₁] ⧸ (s)` attached to a number of variables `n` and a finite
set of relations `s`. -/
private noncomputable def etalePresentationModel (A : Type u) [CommRing A]
    (i : EtalePresentationIndex A) : Under (CommRingCat.of A) :=
  Under.mk (CommRingCat.ofHom (algebraMap A
    (MvPolynomial (Fin i.1) A ⧸ Ideal.span (i.2 : Set (MvPolynomial (Fin i.1) A)))))

/-- The property of an `A`-algebra of being one of the standard finite presentations. -/
private def etalePresentationModels (A : Type u) [CommRing A] :
    ObjectProperty (Under (CommRingCat.of A)) :=
  ObjectProperty.ofObj (etalePresentationModel A)

/-- Finitely presented `A`-algebras form an essentially small class: each of them is isomorphic
to one of the standard finite presentations, of which there is only a set. -/
private theorem finitePresentationUnder_essentiallySmall (A : Type u) [CommRing A] :
    ObjectProperty.EssentiallySmall.{u}
      (fun X : Under (CommRingCat.of A) => X.hom.hom.FinitePresentation) := by
  let : Small.{u} (EtalePresentationIndex A) := small_self _
  have hsmall : ObjectProperty.Small.{u} (etalePresentationModels A) := by
    apply small_of_surjective (f := fun i : EtalePresentationIndex A =>
      (⟨etalePresentationModel A i, ObjectProperty.ofObj.mk i⟩ :
        Subtype (etalePresentationModels A)))
    rintro ⟨X, ⟨i⟩⟩
    exact ⟨i, rfl⟩
  refine ⟨etalePresentationModels A, hsmall, fun X hX => ?_⟩
  let : Algebra A X.right := X.hom.hom.toAlgebra
  have hfp : Algebra.FinitePresentation A X.right :=
    RingHom.finitePresentation_algebraMap.mp hX
  obtain ⟨n, I, e, s, hs⟩ := Algebra.FinitePresentation.iff.mp hfp
  let idx : EtalePresentationIndex A := ⟨n, s⟩
  let M := etalePresentationModel A idx
  let : Algebra A M.right := M.hom.hom.toAlgebra
  have hspan : Ideal.span (s : Set (MvPolynomial (Fin n) A)) = I := hs
  have eI : ((MvPolynomial (Fin n) A) ⧸
      Ideal.span (s : Set (MvPolynomial (Fin n) A))) ≃ₐ[A] X.right :=
    (Ideal.quotientEquivAlgOfEq A hspan).trans e
  let hr : M.right ≅ X.right := eI.toRingEquiv.toCommRingCatIso
  have hw : X.hom ≫ hr.symm.hom = M.hom := by
    ext a
    change eI.symm.toRingEquiv (X.hom.hom a) = M.hom.hom a
    exact eI.symm.commutes a
  exact ⟨M, ⟨idx⟩, ⟨Under.isoMk hr.symm hw⟩⟩

/-- The category of étale `A`-algebras is essentially small, because an étale algebra is
finitely presented. -/
public instance etaleUnder_essentiallySmall (A : Type u) [CommRing A] :
    EssentiallySmall.{u, u, u + 1} (EtaleUnder A) := by
  have hle : CommRingCat.etale.underObj (X := CommRingCat.of A) ≤
      (fun X : Under (CommRingCat.of A) => X.hom.hom.FinitePresentation) :=
    fun _ hX => (RingHom.Etale.iff_flat_and_formallyUnramified.mp hX).2.2
  let : ObjectProperty.EssentiallySmall.{u}
      (fun X : Under (CommRingCat.of A) => X.hom.hom.FinitePresentation) :=
    finitePresentationUnder_essentiallySmall A
  let : ObjectProperty.EssentiallySmall.{u}
      (CommRingCat.etale.underObj (X := CommRingCat.of A)) :=
    ObjectProperty.EssentiallySmall.of_le hle
  infer_instance

/-- An étale `A ⧸ I`-algebra `X` is the quotient by `I` of an étale `A`-algebra: there is an
étale `A`-algebra `Y` and a surjection `Y → X` with kernel the ideal generated by `I` and
compatible with the structure maps. -/
public theorem etaleUnder_quotient_lift (A : Type u) [CommRing A] (I : Ideal A)
    (X : Under (CommRingCat.of (A ⧸ I))) (hX : RingHom.Etale X.hom.hom) :
    ∃ Y : Under (CommRingCat.of A), RingHom.Etale Y.hom.hom ∧
      ∃ f : Y.right →+* X.right, Function.Surjective f ∧
        RingHom.ker f = I.map Y.hom.hom ∧
        f.comp Y.hom.hom = X.hom.hom.comp (Ideal.Quotient.mk I) := by
  let : Algebra (A ⧸ I) X.right := X.hom.hom.toAlgebra
  let : Algebra A X.right := (X.hom.hom.comp (Ideal.Quotient.mk I)).toAlgebra
  let : Algebra.Etale (A ⧸ I) X.right := (RingHom.etale_algebraMap).mp hX
  have hT : IsScalarTower A (A ⧸ I) X.right := .of_algebraMap_eq fun _ => rfl
  obtain ⟨C, _, _, hC, ψ, hsurj, hker⟩ :=
    etale_lift_along_surjection A (A ⧸ I) X.right Ideal.Quotient.mk_surjective
  let Y : Under (CommRingCat.of A) := Under.mk (CommRingCat.ofHom (algebraMap A C))
  refine ⟨Y, ?_, ψ.toRingHom, hsurj, ?_, ?_⟩
  · change RingHom.Etale (algebraMap A C)
    exact RingHom.etale_algebraMap.mpr hC
  · change RingHom.ker (ψ : C →+* X.right) = I.map (algebraMap A C)
    have hq : RingHom.ker (algebraMap A (A ⧸ I)) = I := by
      ext x
      simp
    rw [hker, hq]
  · ext a
    exact ψ.commutes a

/-- The category of étale `A`-algebras is filtered: the identity is étale, two étale algebras
map to their pushout, and two parallel maps are coequalized by an étale algebra. -/
public instance etaleUnder_isFiltered (A : Type u) [CommRing A] :
    IsFiltered (EtaleUnder A) where
  nonempty := by
    let X : Under (CommRingCat.of A) := Under.mk (𝟙 (CommRingCat.of A))
    exact ⟨⟨X, by
      change RingHom.Etale (algebraMap A A)
      exact RingHom.etale_algebraMap.mpr inferInstance⟩⟩
  cocone_objs X Y := by
    let f := X.obj.hom
    let g := Y.obj.hom
    let T : CommRingCat := Limits.pushout f g
    let hT : CommRingCat.of A ⟶ T := f ≫ Limits.pushout.inl f g
    have hEt : CommRingCat.etale hT :=
      MorphismProperty.comp_mem CommRingCat.etale f (Limits.pushout.inl f g)
        X.property (MorphismProperty.pushout_inl f g Y.property)
    let Z : EtaleUnder A := ⟨Under.mk hT, hEt⟩
    let u : X ⟶ Z := ObjectProperty.homMk <| Under.homMk
      (Limits.pushout.inl f g) rfl
    let v : Y ⟶ Z := ObjectProperty.homMk <| Under.homMk
      (Limits.pushout.inr f g) (Limits.pushout.condition (f := f) (g := g)).symm
    exact ⟨Z, u, v, trivial⟩
  cocone_maps {X Y} f g := by
    let : Algebra A X.obj.right := X.obj.hom.hom.toAlgebra
    let : Algebra A Y.obj.right := Y.obj.hom.hom.toAlgebra
    let : Algebra.Etale A X.obj.right := RingHom.etale_algebraMap.mp X.property
    let : Algebra.Etale A Y.obj.right := RingHom.etale_algebraMap.mp Y.property
    let fA : X.obj.right →ₐ[A] Y.obj.right :=
      { f.hom.right.hom with commutes' := fun a => congrArg (fun k => k.hom a) (Under.w f.hom) }
    let gA : X.obj.right →ₐ[A] Y.obj.right :=
      { g.hom.right.hom with commutes' := fun a => congrArg (fun k => k.hom a) (Under.w g.hom) }
    obtain ⟨E, _, _, hE, h, j, hj, hgj, _⟩ :=
      etale_coequalize_maps A X.obj.right Y.obj.right fA gA
    let Z : EtaleUnder A :=
      ⟨Under.mk (CommRingCat.ofHom (algebraMap A E)), by
        change RingHom.Etale (algebraMap A E)
        exact RingHom.etale_algebraMap.mpr hE⟩
    let k : Y ⟶ Z := ObjectProperty.homMk <| Under.homMk
      (CommRingCat.ofHom h.toRingHom) (by
      apply CommRingCat.hom_ext
      ext a
      exact h.commutes a)
    refine ⟨Z, k, ?_⟩
    apply ObjectProperty.hom_ext
    ext x
    exact (DFunLike.congr_fun hj x).trans (DFunLike.congr_fun hgj x).symm

/-- An étale `A`-algebra is a finitely presentable object of the category of `A`-algebras. -/
public theorem etaleUnder_finitelyPresentable (A : Type u) [CommRing A]
    (X : EtaleUnder A) : IsFinitelyPresentable.{u} X.obj := by
  let : Algebra A X.obj.right := X.obj.hom.hom.toAlgebra
  have hEt : Algebra.Etale A X.obj.right := RingHom.etale_algebraMap.mp X.property
  have hfp : X.obj.hom.hom.FinitePresentation :=
    (RingHom.finitePresentation_algebraMap).mpr hEt.finitePresentation
  exact CommRingCat.isFinitelyPresentable_under (CommRingCat.of A) X.obj hfp

end AlgebraicGeometry.ProEtale
