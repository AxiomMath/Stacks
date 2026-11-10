module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.RingHom.Etale
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.EtaleAlgebras
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Lifting ind-étale algebras across a quotient

For a commutative ring `A` and an ideal `I`, quotient base change on ind-étale algebras
`C ↦ C ⧸ IC` has a fully faithful right adjoint `v`.  Its counit identifies the quotient of
each lifted algebra with the original algebra, naturally; so every ind-étale `A ⧸ I`-algebra
`V` is `v(V) ⧸ I v(V)` for an ind-étale `A`-algebra `v(V)`.

The lift of `V` is the colimit of the factorizations `A → B → V` with `A → B` étale.  That
index category is filtered, essentially small, and its objects are finitely presentable, which
is what makes the colimit ind-étale and makes maps out of it computable stage by stage.  The
counit is surjective because each stage of a presentation of `V` is already reached by a
factorization, and injective because its kernel is pure and units lift along the localization
of a lift at any element.

## Main definitions

* `AlgebraicGeometry.ProEtale.IndEtaleAlgebra`: the category of ind-étale algebras over a ring.
* `AlgebraicGeometry.ProEtale.indEtaleQuotientBaseChange`: quotient base change.
* `AlgebraicGeometry.ProEtale.indEtaleQuotientLift`: the right-adjoint lift.

## Main results

* `AlgebraicGeometry.ProEtale.indEtaleBaseChange_hasFullyFaithfulRightAdjoint`: the adjunction.
* `AlgebraicGeometry.ProEtale.indEtaleQuotientLift_fullyFaithful`: full faithfulness.
* `AlgebraicGeometry.ProEtale.indEtaleQuotientLift_baseChangeIso`: the composite of the lift
  with quotient base change is the identity.
* `AlgebraicGeometry.ProEtale.indEtaleQuotientLift_isUnit_of_quotient_isUnit`: units lift from
  the quotient of a lifted algebra.

## Implementation notes

An algebra is represented as a commutative ring under its base ring.  Ind-étaleness is the
ind-completion of the object property of étaleness in that under category.  Base change is
pushout along `A → A ⧸ I`; it is restricted to the ind-étale full subcategories using the
stability of ind-étaleness under pushout.  The natural isomorphism is the canonical
identification `v(V) ⧸ I v(V) ≅ V`.

The adjunction and the natural isomorphism are stated as `Nonempty` of the corresponding
structure, so that no particular hom-set bijection is fixed by the statement.

## References

* [Stacks Project, Tag 097P](https://stacks.math.columbia.edu/tag/097P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- The category of ind-étale algebras over `A`. -/
public abbrev IndEtaleAlgebra (A : Type u) [CommRing A] :=
  (ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
    (X := CommRingCat.of A))).FullSubcategory

/-- Extension of scalars along `A → A ⧸ I`, restricted to ind-étale algebras. -/
@[stacks 097P "the quotient base-change functor"]
public noncomputable def indEtaleQuotientBaseChange (A : Type u) [CommRing A]
    (I : Ideal A) : IndEtaleAlgebra A ⥤ IndEtaleAlgebra (A ⧸ I) :=
  (ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
    (X := CommRingCat.of (A ⧸ I)))).lift
    ((ObjectProperty.ι _) ⋙ Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (fun X => MorphismProperty.ind_underObj_pushout
      (CommRingCat.ofHom (Ideal.Quotient.mk I)) X.property)

attribute [implicit_reducible] indEtaleQuotientBaseChange

/-- Extension of scalars along `A → A ⧸ I`, as a functor from étale `A`-algebras to all
`A ⧸ I`-algebras: the target is not cut down to the ind-étale ones. -/
public noncomputable abbrev etaleQuotientBaseChangeRaw (A : Type u) [CommRing A]
    (I : Ideal A) : EtaleUnder A ⥤ Under (CommRingCat.of (A ⧸ I)) :=
  (ObjectProperty.ι _) ⋙ Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The index category used to build the lift of an ind-étale `A ⧸ I`-algebra `V`: its objects
are the factorizations `A → B → V` with `A → B` étale, that is, the objects of the
costructured-arrow category over `V` of quotient base change on étale `A`-algebras. -/
public noncomputable abbrev etaleQuotientLiftIndex (A : Type u) [CommRing A] (I : Ideal A)
    (V : IndEtaleAlgebra (A ⧸ I)) :=
  CostructuredArrow (etaleQuotientBaseChangeRaw A I) V.obj

/-- The diagram of `A`-algebras underlying the index category of factorizations: a
factorization `A → B → V` is sent to `B`. -/
public noncomputable abbrev etaleQuotientLiftDiagram (A : Type u) [CommRing A] (I : Ideal A)
    (V : IndEtaleAlgebra (A ⧸ I)) : etaleQuotientLiftIndex A I V ⥤ Under (CommRingCat.of A) where
  obj i := i.left.obj
  map f := f.left.hom
  map_id _ := rfl
  map_comp _ _ := rfl


/-- The index category of factorizations is nonempty: a stage of a presentation of `V` by étale
`A ⧸ I`-algebras lifts to an étale `A`-algebra. -/
private theorem etaleQuotientLiftIndex_nonempty (A : Type u) [CommRing A] (I : Ideal A)
    (V : IndEtaleAlgebra (A ⧸ I)) : Nonempty (etaleQuotientLiftIndex A I V) := by
  classical
  obtain ⟨J, _, _, pres, hpres⟩ := V.property
  let i : J := Classical.choice IsFiltered.nonempty
  let X : Under (CommRingCat.of (A ⧸ I)) := pres.diag.obj i
  obtain ⟨Y, hY, f, hsurj, hker, hcompat⟩ := etaleUnder_quotient_lift A I X (hpres i)
  let Y' : EtaleUnder A := ⟨Y, hY⟩
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let g : Y ⟶ (Under.map b).obj X :=
    Under.homMk (CommRingCat.ofHom f) (CommRingCat.hom_ext hcompat)
  let t : (etaleQuotientBaseChangeRaw A I).obj Y' ⟶ X :=
    ((Under.mapPushoutAdj b).homEquiv Y X).symm g
  exact ⟨CostructuredArrow.mk (Y := Y') (t ≫ pres.ι.app i)⟩

/-- Every map to `V` out of an étale `A ⧸ I`-algebra `X` factors through a factorization whose
quotient base change surjects onto `X`. -/
private theorem etaleQuotientLiftIndex_stageSurjective (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I))
    (X : EtaleUnder (A ⧸ I)) (m : X.obj ⟶ V.obj) :
    ∃ (i : etaleQuotientLiftIndex A I V)
      (t : (etaleQuotientBaseChangeRaw A I).obj i.left ⟶ X.obj),
      Function.Surjective t.right.hom ∧ i.hom = t ≫ m := by
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let : Algebra (A ⧸ I) X.obj.right := X.obj.hom.hom.toAlgebra
  let : Algebra A X.obj.right := (X.obj.hom.hom.comp (Ideal.Quotient.mk I)).toAlgebra
  let : Algebra.Etale (A ⧸ I) X.obj.right := RingHom.etale_algebraMap.mp X.property
  let hT : IsScalarTower A (A ⧸ I) X.obj.right := .of_algebraMap_eq fun _ => rfl
  obtain ⟨Y, hY, f, hsurj, hker, hcompat⟩ := etaleUnder_quotient_lift A I X.obj X.property
  let Y' : EtaleUnder A := ⟨Y, hY⟩
  have hc : Y.hom ≫ CommRingCat.ofHom f = b ≫ X.obj.hom := CommRingCat.hom_ext hcompat
  let d : CommRingCat.of ((etaleQuotientBaseChangeRaw A I).obj Y').right ⟶
      CommRingCat.of X.obj.right :=
    Limits.pushout.desc (CommRingCat.ofHom f) X.obj.hom hc
  let t : (etaleQuotientBaseChangeRaw A I).obj Y' ⟶ X.obj :=
    Under.homMk d (by
      apply CommRingCat.hom_ext
      exact congrArg (fun q : CommRingCat.of _ ⟶ CommRingCat.of _ => q.hom)
        (Limits.pushout.inr_desc (CommRingCat.ofHom f) X.obj.hom hc))
  have ht : t.right.hom.comp (Limits.pushout.inl Y.hom b).hom = f := by
    change d.hom.comp (Limits.pushout.inl Y.hom b).hom = f
    exact congrArg (fun q : CommRingCat.of Y.right ⟶ CommRingCat.of X.obj.right => q.hom)
      (Limits.pushout.inl_desc (CommRingCat.ofHom f) X.obj.hom hc)
  have hsurjT : Function.Surjective t.right.hom := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨(Limits.pushout.inl Y.hom b).hom y,
      congrArg (fun q : Y.right →+* X.obj.right => q y) ht⟩
  refine ⟨CostructuredArrow.mk (Y := Y') (t ≫ m), t, hsurjT, rfl⟩

/-- The index category of factorizations is essentially small, because the category of étale
`A`-algebras is. -/
private theorem etaleQuotientLiftIndex_essentiallySmall (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I)) :
    EssentiallySmall.{u, u, u + 1} (etaleQuotientLiftIndex A I V) := by
  let : EssentiallySmall.{u, u, u + 1} (EtaleUnder A) := etaleUnder_essentiallySmall A
  infer_instance

/-- Two factorizations are dominated by a third one, built from the pushout of their étale
algebras. -/
private theorem etaleQuotientLiftIndex_cocone_objs (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I))
    (x y : etaleQuotientLiftIndex A I V) :
    ∃ (z : etaleQuotientLiftIndex A I V) (_ : x ⟶ z) (_ : y ⟶ z), True := by
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let X := x.left.obj
  let Y := y.left.obj
  let fx := X.hom
  let fy := Y.hom
  have hPx : CommRingCat.etale (fx ≫ Limits.pushout.inl fx fy) :=
    MorphismProperty.comp_mem CommRingCat.etale fx (Limits.pushout.inl fx fy)
      x.left.property (MorphismProperty.pushout_inl fx fy y.left.property)
  let Z : EtaleUnder A := ⟨Under.mk (fx ≫ Limits.pushout.inl fx fy), hPx⟩
  let ux : x.left ⟶ Z := ObjectProperty.homMk <| Under.homMk (Limits.pushout.inl fx fy) rfl
  let uy : y.left ⟶ Z := ObjectProperty.homMk <| Under.homMk (Limits.pushout.inr fx fy) (by
    dsimp [Z]
    exact (Limits.pushout.condition (f := fx) (g := fy)).symm)
  let xa : X ⟶ (Under.map b).obj V.obj :=
    (Under.mapPushoutAdj b).homEquiv X V.obj x.hom
  let ya : Y ⟶ (Under.map b).obj V.obj :=
    (Under.mapPushoutAdj b).homEquiv Y V.obj y.hom
  have hbase : fx ≫ xa.right = fy ≫ ya.right := by
    apply CommRingCat.hom_ext
    ext a
    have hx := congrArg (fun q : CommRingCat.of A ⟶ V.obj.right => q.hom a) (Under.w xa)
    have hy := congrArg (fun q : CommRingCat.of A ⟶ V.obj.right => q.hom a) (Under.w ya)
    change xa.right.hom (fx.hom a) = V.obj.hom.hom (Ideal.Quotient.mk I a) at hx
    change ya.right.hom (fy.hom a) = V.obj.hom.hom (Ideal.Quotient.mk I a) at hy
    exact hx.trans hy.symm
  let t := Limits.pushout.desc xa.right ya.right hbase
  have ht : (fx ≫ Limits.pushout.inl fx fy) ≫ t = b ≫ V.obj.hom := by
    rw [Category.assoc, Limits.pushout.inl_desc]
    exact Under.w xa
  let za : Z.obj ⟶ (Under.map b).obj V.obj := Under.homMk t ht
  let zh : (etaleQuotientBaseChangeRaw A I).obj Z ⟶ V.obj :=
    ((Under.mapPushoutAdj b).homEquiv Z.obj V.obj).symm za
  let z : etaleQuotientLiftIndex A I V := CostructuredArrow.mk zh
  let f : x ⟶ z := CostructuredArrow.homMk ux (by
    apply (Under.mapPushoutAdj b).homEquiv X V.obj |>.injective
    change (Under.mapPushoutAdj b).homEquiv X V.obj
      ((Under.pushout b).map ux.hom ≫ zh) = xa
    rw [Adjunction.homEquiv_naturality_left]
    rw [Equiv.apply_symm_apply]
    change ux.hom ≫ za = xa
    apply (Under.forget (CommRingCat.of A)).map_injective
    change Limits.pushout.inl fx fy ≫ t = xa.right
    exact Limits.pushout.inl_desc _ _ _)
  let g : y ⟶ z := CostructuredArrow.homMk uy (by
    apply (Under.mapPushoutAdj b).homEquiv Y V.obj |>.injective
    change (Under.mapPushoutAdj b).homEquiv Y V.obj
      ((Under.pushout b).map uy.hom ≫ zh) = ya
    rw [Adjunction.homEquiv_naturality_left]
    rw [Equiv.apply_symm_apply]
    change uy.hom ≫ za = ya
    apply (Under.forget (CommRingCat.of A)).map_injective
    change Limits.pushout.inr fx fy ≫ t = ya.right
    exact Limits.pushout.inr_desc _ _ _)
  exact ⟨z, f, g, trivial⟩

/-- Two parallel maps of factorizations become equal after a further map, built from the
coequalizer of the two underlying maps of étale algebras. -/
private theorem etaleQuotientLiftIndex_cocone_maps (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I))
    {x y : etaleQuotientLiftIndex A I V} (f g : x ⟶ y) :
    ∃ (z : etaleQuotientLiftIndex A I V) (h : y ⟶ z), f ≫ h = g ≫ h := by
  classical
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let X := x.left.obj
  let Y := y.left.obj
  let : Algebra A V.obj.right :=
    (V.obj.hom.hom.comp (Ideal.Quotient.mk I)).toAlgebra
  let : Algebra A X.right := X.hom.hom.toAlgebra
  let : Algebra A Y.right := Y.hom.hom.toAlgebra
  let : Algebra.Etale A X.right := RingHom.etale_algebraMap.mp x.left.property
  let : Algebra.Etale A Y.right := RingHom.etale_algebraMap.mp y.left.property
  let xa : X ⟶ (Under.map b).obj V.obj :=
    (Under.mapPushoutAdj b).homEquiv X V.obj x.hom
  let ya : Y ⟶ (Under.map b).obj V.obj :=
    (Under.mapPushoutAdj b).homEquiv Y V.obj y.hom
  have hfa : f.left.hom ≫ ya = xa := by
    have hh := congrArg ((Under.mapPushoutAdj b).homEquiv X V.obj) f.w
    change (Under.mapPushoutAdj b).homEquiv X V.obj
        ((Under.pushout b).map f.left.hom ≫ y.hom) =
      (Under.mapPushoutAdj b).homEquiv X V.obj x.hom at hh
    rw [Adjunction.homEquiv_naturality_left] at hh
    simpa [xa, ya] using hh
  have hga : g.left.hom ≫ ya = xa := by
    have hh := congrArg ((Under.mapPushoutAdj b).homEquiv X V.obj) g.w
    change (Under.mapPushoutAdj b).homEquiv X V.obj
        ((Under.pushout b).map g.left.hom ≫ y.hom) =
      (Under.mapPushoutAdj b).homEquiv X V.obj x.hom at hh
    rw [Adjunction.homEquiv_naturality_left] at hh
    simpa [xa, ya] using hh
  let fA : X.right →ₐ[A] Y.right :=
    { toRingHom := f.left.hom.right.hom
      commutes' a :=
        (congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of Y.right => k.hom a)
          f.left.hom.w :) }
  let gA : X.right →ₐ[A] Y.right :=
    { toRingHom := g.left.hom.right.hom
      commutes' a :=
        (congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of Y.right => k.hom a)
          g.left.hom.w :) }
  let xA : X.right →ₐ[A] V.obj.right :=
    { toRingHom := xa.right.hom
      commutes' a :=
        (congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of V.obj.right => k.hom a) xa.w :) }
  let yA : Y.right →ₐ[A] V.obj.right :=
    { toRingHom := ya.right.hom
      commutes' a :=
        (congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of V.obj.right => k.hom a) ya.w :) }
  have hrf : yA.comp fA = xA := AlgHom.ext fun a =>
    (congrArg (fun k : X ⟶ (Under.map b).obj V.obj => k.right.hom a) hfa :)
  have hrg : yA.comp gA = xA := AlgHom.ext fun a =>
    (congrArg (fun k : X ⟶ (Under.map b).obj V.obj => k.right.hom a) hga :)
  obtain ⟨E, hERing, hEAlg, hE, eh, ej, he, hge, hfactor⟩ :=
    etale_coequalize_maps A X.right Y.right fA gA
  let : CommRing E := hERing
  let : Algebra A E := hEAlg
  let Z : EtaleUnder A := ⟨Under.mk (CommRingCat.ofHom (algebraMap A E)), by
    change RingHom.Etale (algebraMap A E)
    exact RingHom.etale_algebraMap.mpr hE⟩
  let uX : x.left ⟶ Z := ObjectProperty.homMk <| Under.homMk
    (CommRingCat.ofHom ej.toRingHom) (by
      apply CommRingCat.hom_ext
      ext a
      exact ej.commutes a)
  let uY : y.left ⟶ Z := ObjectProperty.homMk <| Under.homMk
    (CommRingCat.ofHom eh.toRingHom) (by
      apply CommRingCat.hom_ext
      ext a
      exact eh.commutes a)
  obtain ⟨m, hmX, hmY⟩ := hfactor yA xA hrf hrg
  let za : Z.obj ⟶ (Under.map b).obj V.obj := Under.homMk
    (CommRingCat.ofHom m.toRingHom) (by
      apply CommRingCat.hom_ext
      ext a
      exact m.commutes a)
  have hX : uX.hom ≫ za = xa := by
    ext a
    exact congrArg (fun q : X.right →ₐ[A] V.obj.right => q a) hmY
  have hY : uY.hom ≫ za = ya := by
    ext a
    exact congrArg (fun q : Y.right →ₐ[A] V.obj.right => q a) hmX
  let zh : (etaleQuotientBaseChangeRaw A I).obj Z ⟶ V.obj :=
    ((Under.mapPushoutAdj b).homEquiv Z.obj V.obj).symm za
  let z : etaleQuotientLiftIndex A I V := CostructuredArrow.mk zh
  let hx : x ⟶ z := CostructuredArrow.homMk uX (by
    apply (Under.mapPushoutAdj b).homEquiv X V.obj |>.injective
    change (Under.mapPushoutAdj b).homEquiv X V.obj
      ((Under.pushout b).map uX.hom ≫ zh) = xa
    rw [Adjunction.homEquiv_naturality_left]
    rw [Equiv.apply_symm_apply]
    exact hX)
  let hy : y ⟶ z := CostructuredArrow.homMk uY (by
    apply (Under.mapPushoutAdj b).homEquiv Y V.obj |>.injective
    change (Under.mapPushoutAdj b).homEquiv Y V.obj
      ((Under.pushout b).map uY.hom ≫ zh) = ya
    rw [Adjunction.homEquiv_naturality_left]
    rw [Equiv.apply_symm_apply]
    exact hY)
  refine ⟨z, hy, ?_⟩
  apply CostructuredArrow.hom_ext
  apply ObjectProperty.hom_ext
  apply (Under.forget (CommRingCat.of A)).map_injective
  apply CommRingCat.hom_ext
  ext a
  change eh (f.left.hom.right.hom a) = eh (g.left.hom.right.hom a)
  exact (congrArg (fun q : X.right →ₐ[A] E => q a) he).trans
    (congrArg (fun q : X.right →ₐ[A] E => q a) hge).symm

/-- The index category of factorizations is filtered. -/
private instance etaleQuotientLiftIndex_filtered (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I)) :
    IsFiltered (etaleQuotientLiftIndex A I V) where
  nonempty := etaleQuotientLiftIndex_nonempty A I V
  cocone_objs x y := etaleQuotientLiftIndex_cocone_objs A I V x y
  cocone_maps _ _ f g := etaleQuotientLiftIndex_cocone_maps A I V f g

/-- Diagrams indexed by the category of factorizations have colimits in `A`-algebras, since
that index category is essentially small. -/
private instance etaleQuotientLiftIndex_hasColimits (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I)) :
    HasColimitsOfShape (etaleQuotientLiftIndex A I V) (Under (CommRingCat.of A)) :=
  hasColimitsOfShape_of_essentiallySmall (etaleQuotientLiftIndex A I V)
    (Under (CommRingCat.of A))

/-- The diagram of étale algebras of all factorizations `A → B → V` has a colimit. -/
noncomputable local instance etaleQuotientLiftDiagram_hasColimit (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I)) :
    HasColimit (etaleQuotientLiftDiagram A I V) :=
  HasColimitsOfShape.has_colimit (etaleQuotientLiftDiagram A I V)

/-- The `A`-algebra lifting an ind-étale `A ⧸ I`-algebra `V`: the colimit over all
factorizations `A → B → V` with `A → B` étale of the algebras `B`. -/
public noncomputable abbrev etaleQuotientLiftColimit (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I)) : Under (CommRingCat.of A) :=
  colimit (etaleQuotientLiftDiagram A I V)

/-- The lift of an ind-étale `A ⧸ I`-algebra is an ind-étale `A`-algebra. -/
public theorem etaleQuotientLiftColimit_ind (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I)) :
    ObjectProperty.ind.{u} (CommRingCat.etale.underObj
      (X := CommRingCat.of A))
      ((colimit.cocone (etaleQuotientLiftDiagram A I V)).pt) := by
  let pres : ColimitPresentation (etaleQuotientLiftIndex A I V)
      (colimit (etaleQuotientLiftDiagram A I V)) := {
    diag := etaleQuotientLiftDiagram A I V
    ι := (colimit.cocone (etaleQuotientLiftDiagram A I V)).ι
    isColimit := colimit.isColimit (etaleQuotientLiftDiagram A I V) }
  exact ObjectProperty.of_essentiallySmall_index pres (fun i => i.left.property)

/-- The cocone over the quotient base changes of the factorizations, given by their structure
maps to `V`. -/
private noncomputable def etaleQuotientLift_counitCocone (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I)) :
    Cocone (etaleQuotientLiftDiagram A I V ⋙
      Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk I))) where
  pt := V.obj
  ι :=
    { app := fun i => by
        change (etaleQuotientBaseChangeRaw A I).obj i.left ⟶ V.obj
        exact i.hom
      naturality := by
        intro i j f
        change ((etaleQuotientBaseChangeRaw A I).map f.left ≫ j.hom) = i.hom
        exact f.w }

/-- The comparison map from the quotient by `I` of the lift of `V` to `V`, induced by the
structure maps of the factorizations. -/
private noncomputable def etaleQuotientLift_counitRaw (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I)) :
    (Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk I))).obj
      (etaleQuotientLiftColimit A I V) ⟶ V.obj :=
  (isColimitOfPreserves (Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (colimit.isColimit (etaleQuotientLiftDiagram A I V))).desc
      (etaleQuotientLift_counitCocone A I V)

/-- The comparison map is compatible with the structure map of each factorization. -/
private theorem etaleQuotientLift_counitRaw_fac (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I))
    (i : etaleQuotientLiftIndex A I V) :
    (Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk I))).map
        (colimit.ι (etaleQuotientLiftDiagram A I V) i) ≫
      etaleQuotientLift_counitRaw A I V = i.hom := by
  exact (isColimitOfPreserves _ (colimit.isColimit (etaleQuotientLiftDiagram A I V))).fac
    (etaleQuotientLift_counitCocone A I V) i

/-- The comparison map is surjective, because each stage of a presentation of `V` is already
hit by a factorization. -/
private theorem etaleQuotientLift_counitRaw_surjective (A : Type u) [CommRing A]
    (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I)) :
    Function.Surjective (etaleQuotientLift_counitRaw A I V).right.hom := by
  classical
  obtain ⟨J, hJ, hJ', pres, hpres⟩ := V.property
  let : SmallCategory J := hJ
  let : IsFiltered J := hJ'
  let D := etaleQuotientLiftDiagram A I V
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let F := Under.pushout b
  intro x
  let U := Under.forget (CommRingCat.of (A ⧸ I))
  let R := forget CommRingCat
  let cU := U.mapCocone pres.cocone
  have hcU : IsColimit cU := isColimitOfPreserves U pres.isColimit
  let cR := R.mapCocone cU
  have hcR : IsColimit cR := isColimitOfPreserves R hcU
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep
    (F := pres.diag ⋙ U ⋙ R) hcR x
  let X : EtaleUnder (A ⧸ I) := ⟨pres.diag.obj j, hpres j⟩
  obtain ⟨i, t, ht, hi⟩ := etaleQuotientLiftIndex_stageSurjective A I V X
    (pres.ι.app j)
  obtain ⟨z, hz⟩ := ht y
  let p := (Under.pushout b).map (colimit.ι (etaleQuotientLiftDiagram A I V) i)
  refine ⟨p.right.hom z, ?_⟩
  have hfac := etaleQuotientLift_counitRaw_fac A I V i
  have heq := congrArg (fun q => q.right.hom z) hfac
  calc
    (etaleQuotientLift_counitRaw A I V).right.hom
        (p.right.hom z) = (p ≫ etaleQuotientLift_counitRaw A I V).right.hom z := by
          rfl
    _ = i.hom.right.hom z := heq
    _ = (pres.ι.app j).right.hom (t.right.hom z) := by
      rw [hi]
      rfl
    _ = x := by
      rw [hz]
      exact hy

/-- Two maps from an étale `A`-algebra into the lift of `V` which become equal after quotient
base change followed by the comparison map are equal.  This is where finite presentability of
étale algebras is used. -/
private theorem etaleQuotientLift_map_ext (A : Type u) [CommRing A]
    (I : Ideal A) (S : EtaleUnder A) (V : IndEtaleAlgebra (A ⧸ I))
    (f g : S.obj ⟶ etaleQuotientLiftColimit A I V)
    (h : (Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk I))).map f ≫
        etaleQuotientLift_counitRaw A I V =
      (Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk I))).map g ≫
        etaleQuotientLift_counitRaw A I V) : f = g := by
  classical
  let D := etaleQuotientLiftDiagram A I V
  let F := Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let : IsFinitelyPresentable.{u} S.obj := etaleUnder_finitelyPresentable A S
  let : EssentiallySmall.{u, u, u + 1} (etaleQuotientLiftIndex A I V) :=
    etaleQuotientLiftIndex_essentiallySmall A I V
  let : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  let : IsCardinalFiltered (etaleQuotientLiftIndex A I V) Cardinal.aleph0 :=
    (isCardinalFiltered_aleph0_iff _).2 inferInstance
  let : IsCardinalPresentable.{u} S.obj Cardinal.aleph0 := inferInstance
  let c := colimit.cocone D
  let hc := colimit.isColimit D
  obtain ⟨i, u, hu⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    (κ := Cardinal.aleph0) (c := c) hc f
  obtain ⟨j, v, hv⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    (κ := Cardinal.aleph0) (c := c) hc g
  have hobj_i : D.obj i = i.left.obj := rfl
  have hobj_j : D.obj j = j.left.obj := rfl
  let ui : S.obj ⟶ i.left.obj := u ≫ eqToHom hobj_i
  let vj : S.obj ⟶ j.left.obj := v ≫ eqToHom hobj_j
  obtain ⟨k, p, q, _⟩ := etaleQuotientLiftIndex_cocone_objs A I V i j
  have hobj_k : D.obj k = k.left.obj := rfl
  have hmap_p : D.map p = eqToHom hobj_i ≫ p.left.hom ≫ eqToHom hobj_k.symm := by
    cases hobj_i
    cases hobj_k
    rfl
  have hmap_q : D.map q = eqToHom hobj_j ≫ q.left.hom ≫ eqToHom hobj_k.symm := by
    cases hobj_j
    cases hobj_k
    rfl
  have hpbase : F.map p.left.hom ≫ k.hom = i.hom := by
    simpa [F, etaleQuotientBaseChangeRaw] using p.w
  have hqbase : F.map q.left.hom ≫ k.hom = j.hom := by
    simpa [F, etaleQuotientBaseChangeRaw] using q.w
  let a : S.obj ⟶ k.left.obj := ui ≫ p.left.hom
  let b : S.obj ⟶ k.left.obj := vj ≫ q.left.hom
  have hfac_k : F.map (colimit.ι D k) ≫
      etaleQuotientLift_counitRaw A I V = k.hom :=
    etaleQuotientLift_counitRaw_fac A I V k
  have hf : f = a ≫ c.ι.app k := by
    calc
      f = u ≫ c.ι.app i := hu.symm
      _ = u ≫ D.map p ≫ c.ι.app k := by
        simp
      _ = a ≫ c.ι.app k := by
        rw [hmap_p]
        simp [ui, a, Category.assoc]
  have hg : g = b ≫ c.ι.app k := by
    calc
      g = v ≫ c.ι.app j := hv.symm
      _ = v ≫ D.map q ≫ c.ι.app k := by
        simp
      _ = b ≫ c.ι.app k := by
        rw [hmap_q]
        simp [vj, b, Category.assoc]
  have hf' : f = a ≫ colimit.ι D k := by simpa [c] using hf
  have hg' : g = b ≫ colimit.ι D k := by simpa [c] using hg
  have hab : F.map a ≫ k.hom = F.map b ≫ k.hom := by
    calc
      F.map a ≫ k.hom = F.map f ≫ etaleQuotientLift_counitRaw A I V := by
        calc
          F.map a ≫ k.hom = F.map a ≫
              (F.map (colimit.ι D k) ≫ etaleQuotientLift_counitRaw A I V) := by
                rw [← hfac_k]
          _ = F.map (a ≫ colimit.ι D k) ≫ etaleQuotientLift_counitRaw A I V := by
                simp [Functor.map_comp, Category.assoc]
          _ = F.map f ≫ etaleQuotientLift_counitRaw A I V := by rw [← hf']
      _ = F.map g ≫ etaleQuotientLift_counitRaw A I V := h
      _ = F.map b ≫ k.hom := by
        calc
          F.map g ≫ etaleQuotientLift_counitRaw A I V =
              F.map (b ≫ colimit.ι D k) ≫ etaleQuotientLift_counitRaw A I V := by rw [← hg']
          _ = F.map b ≫ (F.map (colimit.ι D k) ≫
              etaleQuotientLift_counitRaw A I V) := by
                simp [Functor.map_comp, Category.assoc]
          _ = F.map b ≫ k.hom := by
                rw [hfac_k]
  let a' : S ⟶ k.left := ObjectProperty.homMk a
  let b' : S ⟶ k.left := ObjectProperty.homMk b
  let i₀ : etaleQuotientLiftIndex A I V :=
    CostructuredArrow.mk (F.map a'.hom ≫ k.hom)
  let α : i₀ ⟶ k := CostructuredArrow.homMk a' rfl
  let β : i₀ ⟶ k := CostructuredArrow.homMk b' hab.symm
  obtain ⟨z, r, hr⟩ := etaleQuotientLiftIndex_cocone_maps A I V α β
  have hab' : a ≫ r.left.hom = b ≫ r.left.hom :=
    congrArg (fun t : i₀ ⟶ z => t.left.hom) hr
  have hcol : r.left.hom ≫ c.ι.app z = c.ι.app k := by
    simpa [D, etaleQuotientLiftDiagram] using c.w r
  calc
    f = a ≫ c.ι.app k := hf
    _ = a ≫ r.left.hom ≫ c.ι.app z := by
      have hh := congrArg (fun t => a ≫ t) hcol.symm
      simpa [Category.assoc] using hh
    _ = b ≫ r.left.hom ≫ c.ι.app z :=
      congrArg (fun t : S.obj ⟶ z.left.obj => t ≫ c.ι.app z) hab'
    _ = b ≫ c.ι.app k := by
      have hh := congrArg (fun t => b ≫ t) hcol
      simpa [Category.assoc] using hh
    _ = g := hg.symm

/-- A map `V → W` of ind-étale `A ⧸ I`-algebras induces a functor between the index categories
of factorizations, by composing the structure map of a factorization with it. -/
@[implicit_reducible]
public noncomputable def etaleQuotientLiftIndexMap (A : Type u) [CommRing A]
  (I : Ideal A) {V W : IndEtaleAlgebra (A ⧸ I)} (f : V ⟶ W) :
    etaleQuotientLiftIndex A I V ⥤ etaleQuotientLiftIndex A I W where
  obj x := CostructuredArrow.mk (x.hom ≫ f.hom)
  map {x y} g := CostructuredArrow.homMk g.left (by
    change ((etaleQuotientBaseChangeRaw A I).map g.left ≫ y.hom) ≫ f.hom =
      x.hom ≫ f.hom
    rw [CostructuredArrow.w])
  map_id x := by
    apply CostructuredArrow.hom_ext
    simp
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    rfl

/-- The map of lifts induced by a map of ind-étale `A ⧸ I`-algebras. -/
public noncomputable def etaleQuotientLiftColimitMap (A : Type u) [CommRing A]
    (I : Ideal A) {V W : IndEtaleAlgebra (A ⧸ I)} (f : V ⟶ W) :
    etaleQuotientLiftColimit A I V ⟶ etaleQuotientLiftColimit A I W := by
  let Dv := etaleQuotientLiftDiagram A I V
  let Dw := etaleQuotientLiftDiagram A I W
  let G := etaleQuotientLiftIndexMap A I f
  let c : Cocone Dv := {
    pt := colimit Dw
    ι := {
      app := fun i => colimit.ι Dw (G.obj i)
      naturality := by
        intro i j g
        simpa [Dv, Dw, G, etaleQuotientLiftIndexMap, etaleQuotientLiftDiagram] using
          (colimit.cocone Dw).w ((etaleQuotientLiftIndexMap A I f).map g) }
  }
  exact colimit.desc Dv c

/-- The map of lifts induced by a map of ind-étale `A ⧸ I`-algebras acts on the factorization
`i` by the induced functor on index categories. -/
private lemma etaleQuotientLiftColimitMap_ι (A : Type u) [CommRing A] (I : Ideal A)
    {V W : IndEtaleAlgebra (A ⧸ I)} (f : V ⟶ W) (i : etaleQuotientLiftIndex A I V) :
    colimit.ι (etaleQuotientLiftDiagram A I V) i ≫ etaleQuotientLiftColimitMap A I f =
      colimit.ι (etaleQuotientLiftDiagram A I W)
        ((etaleQuotientLiftIndexMap A I f).obj i) :=
  colimit.ι_desc _ _

/-- The lift, as a functor from ind-étale `A ⧸ I`-algebras to ind-étale `A`-algebras. -/
public noncomputable def indEtaleQuotientLiftFunctor (A : Type u) [CommRing A]
    (I : Ideal A) : IndEtaleAlgebra (A ⧸ I) ⥤ IndEtaleAlgebra A where
  obj V := ⟨etaleQuotientLiftColimit A I V, etaleQuotientLiftColimit_ind A I V⟩
  map f := ObjectProperty.homMk (etaleQuotientLiftColimitMap A I f)
  map_id V := by
    apply ObjectProperty.hom_ext
    change etaleQuotientLiftColimitMap A I (𝟙 V) = 𝟙 _
    apply (colimit.isColimit (etaleQuotientLiftDiagram A I V)).hom_ext
    intro i
    change colimit.ι (etaleQuotientLiftDiagram A I V) i ≫
      etaleQuotientLiftColimitMap A I (𝟙 V) =
      colimit.ι (etaleQuotientLiftDiagram A I V) i
    rw [etaleQuotientLiftColimitMap_ι]
    let i' : etaleQuotientLiftIndex A I V :=
      CostructuredArrow.mk (i.hom ≫ 𝟙 V.obj)
    let u : i' ⟶ i := CostructuredArrow.homMk (𝟙 i.left)
    have hc := (colimit.cocone (etaleQuotientLiftDiagram A I V)).w u
    simpa [i', u, etaleQuotientLiftDiagram, etaleQuotientLiftIndexMap] using hc.symm
  map_comp {V W U} f g := by
    apply ObjectProperty.hom_ext
    change etaleQuotientLiftColimitMap A I (f ≫ g) =
      etaleQuotientLiftColimitMap A I f ≫ etaleQuotientLiftColimitMap A I g
    apply (colimit.isColimit (etaleQuotientLiftDiagram A I V)).hom_ext
    intro i
    change colimit.ι (etaleQuotientLiftDiagram A I V) i ≫
      etaleQuotientLiftColimitMap A I (f ≫ g) =
      colimit.ι (etaleQuotientLiftDiagram A I V) i ≫
        etaleQuotientLiftColimitMap A I f ≫ etaleQuotientLiftColimitMap A I g
    rw [etaleQuotientLiftColimitMap_ι, ← Category.assoc, etaleQuotientLiftColimitMap_ι,
      etaleQuotientLiftColimitMap_ι]
    let i₁ : etaleQuotientLiftIndex A I U :=
      CostructuredArrow.mk (i.hom ≫ (f ≫ g).hom)
    let i₂ : etaleQuotientLiftIndex A I U :=
      CostructuredArrow.mk ((i.hom ≫ f.hom) ≫ g.hom)
    let u : i₁ ⟶ i₂ := CostructuredArrow.homMk (𝟙 i.left) (by cat_disch)
    have hc := (colimit.cocone (etaleQuotientLiftDiagram A I U)).w u
    simpa [i₁, i₂, u, etaleQuotientLiftIndexMap, etaleQuotientLiftDiagram,
      Category.assoc] using hc.symm

/-- The canonical lift of an ind-étale algebra over `A ⧸ I` to one over `A`. -/
@[stacks 097P "the right-adjoint lift"]
public noncomputable def indEtaleQuotientLift (A : Type u) [CommRing A]
    (I : Ideal A) : IndEtaleAlgebra (A ⧸ I) ⥤ IndEtaleAlgebra A :=
  indEtaleQuotientLiftFunctor A I

/-- The cocone on a chosen presentation of an ind-étale `A`-algebra `X` whose descent is the
map `X → v(V)` corresponding to a map `X ⧸ IX → V`. -/
private noncomputable def indEtaleQuotientLift_homForwardCocone
    (A : Type u) [CommRing A] (I : Ideal A)
    (X : IndEtaleAlgebra A) (V : IndEtaleAlgebra (A ⧸ I))
    (J : Type u) [SmallCategory J] [IsFiltered J]
    (pres : ColimitPresentation J X.obj)
    (hpres : ∀ i, CommRingCat.etale.underObj (pres.diag.obj i))
    (h : (indEtaleQuotientBaseChange A I).obj X ⟶ V) :
    Cocone pres.diag := by
  classical
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let F := Under.pushout b
  let hh : F.obj X.obj ⟶ V.obj := h.hom
  let E := etaleQuotientLiftIndex A I V
  let D := etaleQuotientLiftDiagram A I V
  let Φ : J ⥤ E := {
    obj := fun i => by
      let si : EtaleUnder A := ⟨pres.diag.obj i, hpres i⟩
      have leg : (ObjectProperty.ι (CommRingCat.etale.underObj
          (X := CommRingCat.of A))).obj si ⟶
          (ObjectProperty.ι (ObjectProperty.ind.{u} (CommRingCat.etale.underObj
            (X := CommRingCat.of A)))).obj X := pres.ι.app i
      exact CostructuredArrow.mk (Y := si) (F.map leg ≫ hh)
    map := fun {i j} f => by
      let si : EtaleUnder A := ⟨pres.diag.obj i, hpres i⟩
      let sj : EtaleUnder A := ⟨pres.diag.obj j, hpres j⟩
      let f' : si ⟶ sj := ObjectProperty.homMk (pres.diag.map f)
      exact CostructuredArrow.homMk f' (by
        change (F.map f'.hom ≫ F.map (pres.ι.app j) ≫ hh) =
          F.map (pres.ι.app i) ≫ hh
        have hf : f'.hom ≫ pres.ι.app j = pres.ι.app i := by
          simp [f']
        have hf' := congrArg (fun k => F.map k) hf
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun k => k ≫ hh) hf')
    map_id := by
      intro i
      apply CostructuredArrow.hom_ext
      apply ObjectProperty.hom_ext
      change pres.diag.map (𝟙 i) = 𝟙 (pres.diag.obj i)
      exact pres.diag.map_id i
    map_comp := by
      intro i j k f g
      apply CostructuredArrow.hom_ext
      apply ObjectProperty.hom_ext
      exact pres.diag.map_comp f g }
  let c : Cocone pres.diag := {
    pt := colimit D
    ι := {
      app := fun i => colimit.ι D (Φ.obj i)
      naturality := by
        intro i j f
        change pres.diag.map f ≫ colimit.ι D (Φ.obj j) = colimit.ι D (Φ.obj i)
        simpa [D, Φ, etaleQuotientLiftDiagram] using
          (colimit.cocone D).w (Φ.map f) } }
  exact c

/-- The map `X → v(V)` corresponding to a map `X ⧸ IX → V`, computed from a given presentation
of `X` by étale `A`-algebras. -/
private noncomputable def indEtaleQuotientLift_homForwardAux
    (A : Type u) [CommRing A] (I : Ideal A)
    (X : IndEtaleAlgebra A) (V : IndEtaleAlgebra (A ⧸ I))
    (J : Type u) [SmallCategory J] [IsFiltered J]
    (pres : ColimitPresentation J X.obj)
    (hpres : ∀ i, CommRingCat.etale.underObj (pres.diag.obj i))
    (h : (indEtaleQuotientBaseChange A I).obj X ⟶ V) :
    X ⟶ (indEtaleQuotientLift A I).obj V :=
  ObjectProperty.homMk (pres.isColimit.desc
    (indEtaleQuotientLift_homForwardCocone A I X V J pres hpres h))

/-- The map `X → v(V)` corresponding to a map `X ⧸ IX → V`. -/
private noncomputable def indEtaleQuotientLift_homForward
    (A : Type u) [CommRing A] (I : Ideal A)
    (X : IndEtaleAlgebra A) (V : IndEtaleAlgebra (A ⧸ I))
    (h : (indEtaleQuotientBaseChange A I).obj X ⟶ V) :
    X ⟶ (indEtaleQuotientLift A I).obj V := by
  classical
  let hX := X.property
  let J := Classical.choose hX
  let hJ := Classical.choose_spec hX
  letI : SmallCategory J := Classical.choose hJ
  let hJ' := Classical.choose_spec hJ
  letI : IsFiltered J := Classical.choose hJ'
  let hJ'' := Classical.choose_spec hJ'
  let pres : ColimitPresentation J X.obj := Classical.choose hJ''
  let hpres := Classical.choose_spec hJ''
  exact indEtaleQuotientLift_homForwardAux A I X V J pres hpres h

/-- The map `X ⧸ IX → V` corresponding to a map `X → v(V)`: quotient base change followed by
the comparison map. -/
private noncomputable def indEtaleQuotientLift_homBackward
    (A : Type u) [CommRing A] (I : Ideal A)
    (X : IndEtaleAlgebra A) (V : IndEtaleAlgebra (A ⧸ I))
    (g : X ⟶ (indEtaleQuotientLift A I).obj V) :
    (indEtaleQuotientBaseChange A I).obj X ⟶ V := by
  let ε : (indEtaleQuotientBaseChange A I).obj
      ((indEtaleQuotientLift A I).obj V) ⟶ V :=
    ObjectProperty.homMk (etaleQuotientLift_counitRaw A I V)
  exact (indEtaleQuotientBaseChange A I).map g ≫ ε

/-- The comparison maps are natural in the ind-étale `A ⧸ I`-algebra. -/
private theorem indEtaleQuotientLift_counit_natural
    (A : Type u) [CommRing A] (I : Ideal A)
    {V W : IndEtaleAlgebra (A ⧸ I)} (f : V ⟶ W) :
    (indEtaleQuotientBaseChange A I).map
        ((indEtaleQuotientLift A I).map f) ≫
      ObjectProperty.homMk (etaleQuotientLift_counitRaw A I W) =
    ObjectProperty.homMk (etaleQuotientLift_counitRaw A I V) ≫ f := by
  classical
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let F := Under.pushout b
  let Dv := etaleQuotientLiftDiagram A I V
  let Dw := etaleQuotientLiftDiagram A I W
  apply ObjectProperty.hom_ext
  change F.map (etaleQuotientLiftColimitMap A I f) ≫
      etaleQuotientLift_counitRaw A I W =
    etaleQuotientLift_counitRaw A I V ≫ f.hom
  apply (isColimitOfPreserves F (colimit.isColimit Dv)).hom_ext
  intro i
  let Gi := (etaleQuotientLiftIndexMap A I f).obj i
  have hmap : (colimit.ι Dv i) ≫ etaleQuotientLiftColimitMap A I f =
      colimit.ι Dw Gi := by
    simp [etaleQuotientLiftColimitMap, Dv, Dw, Gi,
      etaleQuotientLiftIndexMap, etaleQuotientLiftDiagram]
  have hfacV : F.map (colimit.ι Dv i) ≫ etaleQuotientLift_counitRaw A I V = i.hom := by
    simpa [F, Dv] using etaleQuotientLift_counitRaw_fac A I V i
  have hfacW : F.map (colimit.ι Dw Gi) ≫ etaleQuotientLift_counitRaw A I W =
      Gi.hom := by
    simpa [F, Dw] using etaleQuotientLift_counitRaw_fac A I W Gi
  calc
    F.map (colimit.ι Dv i) ≫
        (F.map (etaleQuotientLiftColimitMap A I f) ≫
          etaleQuotientLift_counitRaw A I W) =
        F.map ((colimit.ι Dv i) ≫ etaleQuotientLiftColimitMap A I f) ≫
          etaleQuotientLift_counitRaw A I W := by
            simp [Functor.map_comp, Category.assoc]
    _ = F.map (colimit.ι Dw Gi) ≫ etaleQuotientLift_counitRaw A I W := by rw [hmap]
    _ = Gi.hom := hfacW
    _ = i.hom ≫ f.hom := rfl
    _ = (F.map (colimit.ι Dv i) ≫ etaleQuotientLift_counitRaw A I V) ≫ f.hom := by
      rw [hfacV]
    _ = F.map (colimit.ι Dv i) ≫
        (etaleQuotientLift_counitRaw A I V ≫ f.hom) := by
          rw [Category.assoc]

/-- The two directions of the hom correspondence compose to the identity on maps
`X ⧸ IX → V`. -/
private theorem indEtaleQuotientLift_homBackward_homForward
    (A : Type u) [CommRing A] (I : Ideal A)
    (X : IndEtaleAlgebra A) (V : IndEtaleAlgebra (A ⧸ I))
    (h : (indEtaleQuotientBaseChange A I).obj X ⟶ V) :
    indEtaleQuotientLift_homBackward A I X V
      (indEtaleQuotientLift_homForward A I X V h) = h := by
  classical
  let hX := X.property
  let J := Classical.choose hX
  let hJ := Classical.choose_spec hX
  let : SmallCategory J := Classical.choose hJ
  let hJ' := Classical.choose_spec hJ
  let : IsFiltered J := Classical.choose hJ'
  let hJ'' := Classical.choose_spec hJ'
  let pres : ColimitPresentation J X.obj := Classical.choose hJ''
  let hpres := Classical.choose_spec hJ''
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let F := Under.pushout b
  let hh : F.obj X.obj ⟶ V.obj := h.hom
  let D := etaleQuotientLiftDiagram A I V
  let E := etaleQuotientLiftIndex A I V
  let c := indEtaleQuotientLift_homForwardCocone A I X V J pres hpres h
  let ε : F.obj (colimit D) ⟶ V.obj := etaleQuotientLift_counitRaw A I V
  -- Both maps agree on each étale stage of the chosen presentation of `X`.
  apply ObjectProperty.hom_ext
  apply (isColimitOfPreserves F pres.isColimit).hom_ext
  intro i
  let si : EtaleUnder A := ⟨pres.diag.obj i, hpres i⟩
  let leg : (ObjectProperty.ι (CommRingCat.etale.underObj
      (X := CommRingCat.of A))).obj si ⟶
      (ObjectProperty.ι (ObjectProperty.ind.{u} (CommRingCat.etale.underObj
        (X := CommRingCat.of A)))).obj X := pres.ι.app i
  let idx : E := CostructuredArrow.mk (Y := si)
    (F.map leg ≫ hh)
  have hci : c.ι.app i = colimit.ι D idx := by
    change (indEtaleQuotientLift_homForwardCocone A I X V J pres hpres h).ι.app i = _
    dsimp [indEtaleQuotientLift_homForwardCocone, idx, leg, F, hh]
  change F.map (pres.ι.app i) ≫
      (F.map (pres.isColimit.desc c) ≫ ε) =
        F.map (pres.ι.app i) ≫ hh
  have hfac := etaleQuotientLift_counitRaw_fac A I V idx
  have hfac' : F.map (colimit.ι D idx) ≫ ε =
      idx.hom := by
    simpa [F, ε] using hfac
  calc
    F.map (pres.ι.app i) ≫
        (F.map (pres.isColimit.desc c) ≫ ε) =
        F.map (pres.ι.app i ≫ pres.isColimit.desc c) ≫
          ε :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun k ↦ k ≫ ε) (F.map_comp _ _).symm)
    _ = F.map (c.ι.app i) ≫ ε :=
      congrArg (fun k ↦ F.map k ≫ ε) (pres.isColimit.fac c i)
    _ = F.map (pres.ι.app i) ≫ hh :=
      (congrArg (fun k ↦ F.map k ≫ ε) hci).trans hfac'

/-- The two directions of the hom correspondence compose to the identity on maps
`X → v(V)`. -/
private theorem indEtaleQuotientLift_homForward_homBackward
    (A : Type u) [CommRing A] (I : Ideal A)
    (X : IndEtaleAlgebra A) (V : IndEtaleAlgebra (A ⧸ I))
    (g : X ⟶ (indEtaleQuotientLift A I).obj V) :
    indEtaleQuotientLift_homForward A I X V
      (indEtaleQuotientLift_homBackward A I X V g) = g := by
  classical
  let hX := X.property
  let J := Classical.choose hX
  let hJ := Classical.choose_spec hX
  let : SmallCategory J := Classical.choose hJ
  let hJ' := Classical.choose_spec hJ
  let : IsFiltered J := Classical.choose hJ'
  let hJ'' := Classical.choose_spec hJ'
  let pres : ColimitPresentation J X.obj := Classical.choose hJ''
  let hpres := Classical.choose_spec hJ''
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let F := Under.pushout b
  let D := etaleQuotientLiftDiagram A I V
  let ε : F.obj (colimit D) ⟶ V.obj := etaleQuotientLift_counitRaw A I V
  let c := indEtaleQuotientLift_homForwardCocone A I X V J pres hpres
    (indEtaleQuotientLift_homBackward A I X V g)
  change ObjectProperty.homMk
      (pres.isColimit.desc c) = g
  apply ObjectProperty.hom_ext
  apply pres.isColimit.hom_ext
  intro i
  let si : EtaleUnder A := ⟨pres.diag.obj i, hpres i⟩
  let f : si.obj ⟶ etaleQuotientLiftColimit A I V := pres.ι.app i ≫ g.hom
  let leg : (ObjectProperty.ι (CommRingCat.etale.underObj
      (X := CommRingCat.of A))).obj si ⟶
      (ObjectProperty.ι (ObjectProperty.ind.{u} (CommRingCat.etale.underObj
        (X := CommRingCat.of A)))).obj X := pres.ι.app i
  let g' : si.obj ⟶ etaleQuotientLiftColimit A I V :=
    pres.ι.app i ≫ (pres.isColimit.desc c)
  have hfg : f = g' := by
    apply etaleQuotientLift_map_ext A I si V f g'
    change F.map f ≫ ε = F.map g' ≫ ε
    dsimp [f, g']
    let E := etaleQuotientLiftIndex A I V
    let idx : E := CostructuredArrow.mk (Y := si)
      (F.map leg ≫ (indEtaleQuotientLift_homBackward A I X V g).hom)
    have hci : c.ι.app i = colimit.ι D idx := by
      change (indEtaleQuotientLift_homForwardCocone A I X V J pres hpres
        (indEtaleQuotientLift_homBackward A I X V g)).ι.app i = _
      dsimp [indEtaleQuotientLift_homForwardCocone, idx, leg, F]
    have hfac := etaleQuotientLift_counitRaw_fac A I V idx
    have hfac' : F.map (colimit.ι D idx) ≫ ε = idx.hom := by
      simpa [F, ε] using hfac
    calc
      F.map (pres.ι.app i ≫ g.hom) ≫ ε =
          F.map (pres.ι.app i) ≫ (indEtaleQuotientLift_homBackward A I X V g).hom := by
            change F.map (pres.ι.app i ≫ g.hom) ≫ ε =
              F.map (pres.ι.app i) ≫ (F.map g.hom ≫ ε)
            exact (congrArg (fun k ↦ k ≫ ε) (F.map_comp (pres.ι.app i) g.hom)).trans
              (Category.assoc _ _ _)
      _ = idx.hom := by
            rfl
      _ = F.map (colimit.ι D idx) ≫ ε := hfac'.symm
      _ = F.map (c.ι.app i) ≫ ε :=
            congrArg (fun k ↦ F.map k ≫ ε) hci.symm
      _ = F.map (pres.ι.app i ≫ pres.isColimit.desc c) ≫ ε :=
            congrArg (fun k ↦ F.map k ≫ ε) (pres.isColimit.fac c i).symm
      _ = F.map g' ≫ ε := rfl
  exact hfg.symm

/-- Quotient base change is left adjoint to the canonical lift. -/
private noncomputable def indEtaleBaseChange_adjunction
    (A : Type u) [CommRing A] (I : Ideal A) :
    indEtaleQuotientBaseChange A I ⊣ indEtaleQuotientLift A I := by
  classical
  let F := indEtaleQuotientBaseChange A I
  let G := indEtaleQuotientLift A I
  let e : ∀ X V, (F.obj X ⟶ V) ≃ (X ⟶ G.obj V) := fun X V => {
    toFun := indEtaleQuotientLift_homForward A I X V
    invFun := indEtaleQuotientLift_homBackward A I X V
    left_inv := indEtaleQuotientLift_homBackward_homForward A I X V
    right_inv := indEtaleQuotientLift_homForward_homBackward A I X V }
  let core : Adjunction.CoreHomEquiv F G := {
    homEquiv := e
    homEquiv_naturality_left_symm := by
      intro X' X V f g
      change indEtaleQuotientLift_homBackward A I X' V (f ≫ g) =
        (indEtaleQuotientBaseChange A I).map f ≫
          indEtaleQuotientLift_homBackward A I X V g
      simp [indEtaleQuotientLift_homBackward, Functor.map_comp, Category.assoc]
    homEquiv_naturality_right := by
      intro X V W h k
      apply (Equiv.injective (e X W).symm)
      change (e X W).symm (e X W (h ≫ k)) =
        (e X W).symm (e X V h ≫ G.map k)
      rw [Equiv.symm_apply_apply]
      symm
      change indEtaleQuotientLift_homBackward A I X W
          (indEtaleQuotientLift_homForward A I X V h ≫ G.map k) = h ≫ k
      calc
        indEtaleQuotientLift_homBackward A I X W
            (indEtaleQuotientLift_homForward A I X V h ≫ G.map k) =
            (indEtaleQuotientBaseChange A I).map
                (indEtaleQuotientLift_homForward A I X V h) ≫
              ((indEtaleQuotientBaseChange A I).map (G.map k) ≫
                ObjectProperty.homMk (etaleQuotientLift_counitRaw A I W)) := by
              simp [indEtaleQuotientLift_homBackward, Functor.map_comp, Category.assoc]
        _ = ((indEtaleQuotientBaseChange A I).map
              (indEtaleQuotientLift_homForward A I X V h) ≫
                ObjectProperty.homMk (etaleQuotientLift_counitRaw A I V)) ≫ k := by
              rw [indEtaleQuotientLift_counit_natural, Category.assoc]
        _ = h ≫ k := by
              change indEtaleQuotientLift_homBackward A I X V
                (indEtaleQuotientLift_homForward A I X V h) ≫ k = h ≫ k
              rw [indEtaleQuotientLift_homBackward_homForward A I X V h] }
  exact Adjunction.mkOfHomEquiv core

/-- Quotient base change is left adjoint to the canonical lift. -/
@[stacks 097P "the adjunction"]
public theorem indEtaleBaseChange_hasFullyFaithfulRightAdjoint
    (A : Type u) [CommRing A] (I : Ideal A) :
    Nonempty (indEtaleQuotientBaseChange A I ⊣ indEtaleQuotientLift A I) :=
  ⟨indEtaleBaseChange_adjunction A I⟩

/-- An element `g` of a lifted algebra is a unit as soon as its image under the map
`C ⟶ V` (with `C` the lift of `V`) adjoint to the counit is a unit.  This is the form of
unit lifting obtained by localizing at `g`, as in the proof of Stacks 09BK. -/
private theorem indEtaleQuotientLift_isUnit_of_isUnit_comparison
    (A : Type u) [CommRing A] (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I))
    (g : ((indEtaleQuotientLift A I).obj V).obj.right)
    (ht : IsUnit (((Under.mapPushoutAdj (CommRingCat.ofHom (Ideal.Quotient.mk I))).homEquiv
      ((indEtaleQuotientLift A I).obj V).obj V.obj
      (((indEtaleBaseChange_adjunction A I).homEquiv _ V).symm (𝟙 _)).hom).right.hom g)) :
    IsUnit g := by
  classical
  let C := (indEtaleQuotientLift A I).obj V
  let : Algebra A C.obj.right := C.obj.hom.hom.toAlgebra
  let D := Localization.Away g
  have hC : (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A C.obj.right) := by
    rw [CommAlgCat.ind_etale_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk]
    exact C.property
  have hD : (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A D) :=
    CommAlgCat.ind_etale_comp hC (ObjectProperty.le_ind _ _ inferInstance)
  let W : IndEtaleAlgebra A := ⟨Under.mk (CommRingCat.ofHom (algebraMap A D)), by
    rw [CommAlgCat.ind_etale_iff_ind_algebraMap,
      MorphismProperty.ind_iff_ind_underMk] at hD
    exact hD⟩
  let f : C ⟶ W := ObjectProperty.homMk
    (Under.homMk (CommRingCat.ofHom (algebraMap C.obj.right D)) (by
      ext a
      exact (IsScalarTower.algebraMap_apply A C.obj.right D a).symm))
  let adj := indEtaleBaseChange_adjunction A I
  let e : (indEtaleQuotientBaseChange A I).obj C ⟶ V :=
    (adj.homEquiv C V).symm (𝟙 C)
  let b := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let t : C.obj ⟶ (Under.map b).obj V.obj :=
    (Under.mapPushoutAdj b).homEquiv C.obj V.obj e.hom
  let s : D →+* V.obj.right := IsLocalization.Away.lift g ht
  have hs (a : C.obj.right) : s (algebraMap C.obj.right D a) = t.right.hom a :=
    IsLocalization.Away.lift_eq g ht a
  let s' : W.obj ⟶ (Under.map b).obj V.obj := Under.homMk (CommRingCat.ofHom s) (by
    ext a
    change s (algebraMap A D a) = _
    rw [IsScalarTower.algebraMap_apply A C.obj.right D, hs]
    exact congrArg (fun k : CommRingCat.of A ⟶ V.obj.right => k.hom a) (Under.w t))
  let k : (indEtaleQuotientBaseChange A I).obj W ⟶ V := ObjectProperty.homMk
    (((Under.mapPushoutAdj b).homEquiv W.obj V.obj).symm s')
  have hfk : (indEtaleQuotientBaseChange A I).map f ≫ k = e := by
    apply ObjectProperty.hom_ext
    apply ((Under.mapPushoutAdj b).homEquiv C.obj V.obj).injective
    change (Under.mapPushoutAdj b).homEquiv C.obj V.obj
      ((Under.pushout b).map f.hom ≫ k.hom) = t
    rw [Adjunction.homEquiv_naturality_left]
    change f.hom ≫ (Under.mapPushoutAdj b).homEquiv W.obj V.obj
      (((Under.mapPushoutAdj b).homEquiv W.obj V.obj).symm s') = t
    rw [Equiv.apply_symm_apply]
    ext a
    exact hs a
  -- Adjointness gives a retraction of `C → C[g⁻¹]`.
  let r : W ⟶ C := adj.homEquiv W V k
  have hfr : f ≫ r = 𝟙 C := by
    rw [← adj.homEquiv_naturality_left, hfk]
    exact (adj.homEquiv C V).apply_symm_apply (𝟙 C)
  have hr := (IsLocalization.Away.algebraMap_isUnit (S := D) g).map r.hom.right.hom
  have he := congrArg (fun k : C ⟶ C => k.hom.right.hom g) hfr
  change r.hom.right.hom (algebraMap C.obj.right D g) = g at he
  change IsUnit (r.hom.right.hom (algebraMap C.obj.right D g)) at hr
  rwa [he] at hr

/-- An element of a lifted algebra is a unit if its image modulo the extended ideal is a unit.
The ideal is extended along the structure map of the underlying `A`-algebra. This follows
from adjointness by localizing at the element, as in the proof of Stacks 09BK. -/
public theorem indEtaleQuotientLift_isUnit_of_quotient_isUnit
    (A : Type u) [CommRing A] (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I))
    (g : ((indEtaleQuotientLift A I).obj V).obj.right)
    (hg : IsUnit (Ideal.Quotient.mk
      (I.map ((indEtaleQuotientLift A I).obj V).obj.hom.hom) g)) : IsUnit g := by
  classical
  let C := (indEtaleQuotientLift A I).obj V
  let e : (indEtaleQuotientBaseChange A I).obj C ⟶ V :=
    ((indEtaleBaseChange_adjunction A I).homEquiv C V).symm (𝟙 C)
  let b := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let t : C.obj ⟶ (Under.map b).obj V.obj :=
    (Under.mapPushoutAdj b).homEquiv C.obj V.obj e.hom
  -- The comparison map kills the extended ideal, so it sends `g` to a unit.
  have hI : I.map C.obj.hom.hom ≤ RingHom.ker t.right.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change t.right.hom (C.obj.hom.hom a) = 0
    have hw := congrArg (fun k : CommRingCat.of A ⟶ V.obj.right => k.hom a) (Under.w t)
    change t.right.hom (C.obj.hom.hom a) = V.obj.hom.hom (Ideal.Quotient.mk I a) at hw
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] at hw
    exact hw
  let q := Ideal.Quotient.lift (I.map C.obj.hom.hom) t.right.hom (fun a ha => hI ha)
  exact indEtaleQuotientLift_isUnit_of_isUnit_comparison A I V g (hg.map q)

/-- An element of the lift of `V` is a unit as soon as its image under the comparison map is a
unit.  This is the form of unit lifting used to prove that the comparison map is injective. -/
private theorem indEtaleQuotientLift_isUnit_of_counit_isUnit
    (A : Type u) [CommRing A] (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I))
    (g : (etaleQuotientLiftColimit A I V).right)
    (hg : IsUnit ((etaleQuotientLift_counitRaw A I V).right.hom
      (((Under.mapPushoutAdj (CommRingCat.ofHom (Ideal.Quotient.mk I))).unit.app
        (etaleQuotientLiftColimit A I V)).right.hom g))) :
    IsUnit g := by
  classical
  let C := (indEtaleQuotientLift A I).obj V
  let gC : C.obj.right := g
  let adj := indEtaleBaseChange_adjunction A I
  let e : (indEtaleQuotientBaseChange A I).obj C ⟶ V :=
    (adj.homEquiv C V).symm (𝟙 C)
  let b := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let t : C.obj ⟶ (Under.map b).obj V.obj :=
    (Under.mapPushoutAdj b).homEquiv C.obj V.obj e.hom
  refine indEtaleQuotientLift_isUnit_of_isUnit_comparison A I V gC ?_
  have he : e = indEtaleQuotientLift_homBackward A I C V (𝟙 C) := by
    simp [e, adj, indEtaleBaseChange_adjunction,
      Adjunction.mkOfHomEquiv_homEquiv]
  have hunitmap : ((Under.mapPushoutAdj b).unit.app C.obj).right.hom gC =
      ((Under.mapPushoutAdj b).unit.app (etaleQuotientLiftColimit A I V)).right.hom g :=
    rfl
  have hgC : IsUnit ((etaleQuotientLift_counitRaw A I V).right.hom
      (((Under.mapPushoutAdj b).unit.app C.obj).right.hom gC)) := by
    rw [hunitmap]
    exact hg
  have hteq : t.right.hom gC = (etaleQuotientLift_counitRaw A I V).right.hom
      (((Under.mapPushoutAdj b).unit.app C.obj).right.hom gC) := by
    dsimp [t]
    simp [he, gC, b, indEtaleQuotientLift_homBackward,
      Under.mapPushoutAdj, Under.id_right]
    rfl
  rw [hteq]
  exact hgC

/-- The comparison map is injective: its kernel is pure because `V` is ind-étale over the
quotient of the lift, and an element of a pure ideal is killed by a unit. -/
private theorem etaleQuotientLift_counitRaw_injective
    (A : Type u) [CommRing A] (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I)) :
    Function.Injective (etaleQuotientLift_counitRaw A I V).right.hom := by
  classical
  let C := (indEtaleQuotientLift A I).obj V
  let b : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let F := Under.pushout b
  let X := etaleQuotientLiftColimit A I V
  let T := F.obj X
  let : Algebra A X.right := X.hom.hom.toAlgebra
  let : Algebra (A ⧸ I) T.right := T.hom.hom.toAlgebra
  let : Algebra (A ⧸ I) V.obj.right := V.obj.hom.hom.toAlgebra
  let ε := etaleQuotientLift_counitRaw A I V
  let S := T.right
  let q : X.right →+* S := ((Under.mapPushoutAdj b).unit.app X).right.hom
  have hq : Function.Surjective q := by
    let e := CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of (A ⧸ I)) X
    have hinc : Function.Surjective
        (Algebra.TensorProduct.includeRight (R := A) (A := A ⧸ I)
          (B := X.right)) := by
      exact Algebra.TensorProduct.includeRight_surjective
        (R := A) (S := A ⧸ I) (T := X.right) Ideal.Quotient.mk_surjective
    have hcomp : ∀ x : X.right,
        e.inv.right.hom (q x) =
          Algebra.TensorProduct.includeRight (R := A) (A := A ⧸ I)
            (B := X.right) x := by
      intro x
      have hi := CommRingCat.pushout_inl_tensorProdObjIsoPushoutObj_inv_right
        (S := CommRingCat.of (A ⧸ I)) X
      have hi' : pushout.inl X.hom b ≫ e.inv.right =
          CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := A) (A := A ⧸ I)
              (B := X.right)).toRingHom := by
        simpa [e, b] using hi
      change (pushout.inl X.hom b ≫ e.inv.right).hom x =
        Algebra.TensorProduct.includeRight (R := A) (A := A ⧸ I)
          (B := X.right) x
      exact congrArg (fun f => f.hom x) hi'
    intro y
    obtain ⟨x, hx⟩ := hinc (e.inv.right.hom y)
    refine ⟨x, ?_⟩
    have hiso : IsIso e.inv.right :=
      inferInstanceAs (IsIso ((Under.forget (CommRingCat.of (A ⧸ I))).map e.inv))
    apply ((ConcreteCategory.isIso_iff_bijective e.inv.right).mp hiso).1
    rw [hcomp]
    change Algebra.TensorProduct.includeRight x = e.inv.right.hom y
    exact hx
  have hS : (CommAlgCat.etale (A ⧸ I)).ind
      (CommAlgCat.of (A ⧸ I) S) := by
    rw [CommAlgCat.ind_etale_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk]
    change ObjectProperty.ind.{u} (CommRingCat.etale.underObj
      (X := CommRingCat.of (A ⧸ I))) T
    exact MorphismProperty.ind_underObj_pushout b
      (etaleQuotientLiftColimit_ind A I V)
  have hV : (CommAlgCat.etale (A ⧸ I)).ind
      (CommAlgCat.of (A ⧸ I) V.obj.right) := by
    rw [CommAlgCat.ind_etale_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk]
    exact V.property
  let : Algebra S V.obj.right := ε.right.hom.toAlgebra
  have hTower : IsScalarTower (A ⧸ I) S V.obj.right := .of_algebraMap_eq fun a => by
    have hw := congrArg (fun f : CommRingCat.of (A ⧸ I) ⟶
        CommRingCat.of V.obj.right => f.hom a) ε.w
    change ε.right.hom (T.hom.hom a) = V.obj.hom.hom a at hw
    exact hw.symm
  let : IsScalarTower (A ⧸ I) S V.obj.right := hTower
  have hSV : (CommAlgCat.etale S).ind (CommAlgCat.of S V.obj.right) :=
    CommAlgCat.ind_etale_of_comp hS hV
  have hflat : Module.Flat S V.obj.right := CommAlgCat.flat_of_ind_etale hSV
  let f : S →ₐ[S] V.obj.right := {
    toRingHom := ε.right.hom
    commutes' := fun _ => rfl }
  have hf : Function.Surjective f := by
    change Function.Surjective ε.right.hom
    exact etaleQuotientLift_counitRaw_surjective A I V
  have hflatQuot : Module.Flat S (S ⧸ RingHom.ker f) := by
    exact Module.Flat.of_linearEquiv
      (Ideal.quotientKerAlgEquivOfSurjective hf).toLinearEquiv
  have hPure : (RingHom.ker ε.right.hom).Pure := by
    rw [Ideal.Pure]
    change Module.Flat S (S ⧸ RingHom.ker f)
    exact hflatQuot
  let : (RingHom.ker ε.right.hom).Pure := hPure
  intro x y hxy
  have hx : x - y ∈ RingHom.ker ε.right.hom := by
    change ε.right.hom (x - y) = 0
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz, hmul⟩ := Ideal.exists_eq_mul_of_pure hx
  obtain ⟨a, ha⟩ := hq z
  have hunitC : IsUnit (1 - a) := by
    apply indEtaleQuotientLift_isUnit_of_counit_isUnit A I V (1 - a)
    have hz0 : ε.right.hom z = 0 := RingHom.mem_ker.mp hz
    have hcalc : ε.right.hom (q (1 - a)) = 1 := by
      simp only [map_sub, map_one, ha, hz0, sub_zero]
    change IsUnit (ε.right.hom (q (1 - a)))
    rw [hcalc]
    exact isUnit_one
  have hunitS : IsUnit (1 - z) := by
    simpa [ha] using hunitC.map q
  have hcancel : (x - y) * (1 - z) = 0 := by
    calc
      (x - y) * (1 - z) = (x - y) - (x - y) * z := by ring
      _ = 0 := sub_eq_zero.mpr hmul
  have hzero : x - y = 0 := hunitS.mul_right_cancel (by simpa using hcancel)
  exact sub_eq_zero.mp hzero

/-- The comparison map is an isomorphism. -/
private theorem etaleQuotientLift_counitRaw_isIso
    (A : Type u) [CommRing A] (I : Ideal A) (V : IndEtaleAlgebra (A ⧸ I)) :
    IsIso (etaleQuotientLift_counitRaw A I V) := by
  apply (isIso_iff_of_reflects_iso (etaleQuotientLift_counitRaw A I V)
    (Under.forget (CommRingCat.of (A ⧸ I)))).mp
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨etaleQuotientLift_counitRaw_injective A I V,
    etaleQuotientLift_counitRaw_surjective A I V⟩

/-- The quotient of a lifted algebra is naturally the original algebra. -/
@[stacks 097P "the quotient comparison"]
public theorem indEtaleQuotientLift_baseChangeIso
    (A : Type u) [CommRing A] (I : Ideal A) :
    Nonempty (indEtaleQuotientLift A I ⋙ indEtaleQuotientBaseChange A I ≅
      𝟭 (IndEtaleAlgebra (A ⧸ I))) := by
  classical
  refine ⟨NatIso.ofComponents (fun V => ?_) ?_⟩
  · let ε : (indEtaleQuotientBaseChange A I).obj
        ((indEtaleQuotientLift A I).obj V) ⟶ V :=
      ObjectProperty.homMk (etaleQuotientLift_counitRaw A I V)
    have : IsIso ε.hom := etaleQuotientLift_counitRaw_isIso A I V
    have : IsIso ε := (ObjectProperty.isIso_hom_iff ε).mp inferInstance
    exact asIso ε
  · intro V W f
    change (indEtaleQuotientBaseChange A I).map
        ((indEtaleQuotientLift A I).map f) ≫
          ObjectProperty.homMk (etaleQuotientLift_counitRaw A I W) =
      ObjectProperty.homMk (etaleQuotientLift_counitRaw A I V) ≫ f
    exact indEtaleQuotientLift_counit_natural A I f

/-- The right-adjoint lift is fully faithful. -/
@[stacks 097P "full faithfulness"]
public theorem indEtaleQuotientLift_fullyFaithful
    (A : Type u) [CommRing A] (I : Ideal A) :
    Nonempty (indEtaleQuotientLift A I).FullyFaithful := by
  obtain ⟨adj⟩ := indEtaleBaseChange_hasFullyFaithfulRightAdjoint A I
  obtain ⟨e⟩ := indEtaleQuotientLift_baseChangeIso A I
  have : IsIso adj.counit := adj.isIso_counit_of_iso e
  exact ⟨adj.fullyFaithfulROfIsIsoCounit⟩

end AlgebraicGeometry.ProEtale
