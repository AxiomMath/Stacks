module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.PointsRelocalized
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Connected geometric fibres and étale neighbourhoods

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`ȳ` be a geometric point of `Y`. The geometric fibre of `f` above `ȳ` is connected exactly when,
for every étale neighbourhood of `ȳ` whose underlying algebraic space is a scheme `V`, the base
change `X_V ⟶ V` has connected fibre above the point `v` of `V` underlying the lift of `ȳ`.

Both fibres are the point space of a presheaf fibre product
(`AlgebraicGeometry.Space.ConnectedPullback`): the geometric fibre is the fibre product of `f`
with the morphism represented by `ȳ`, and the fibre above `v` is the fibre product of the
projection `X_V ⟶ V` with the morphism represented by the residue field point of `V` at `v`.

## Main results

* `AlgebraicGeometry.Space.connectedSpace_geometricFiber_iff_forall_scheme_etaleNeighborhood`
  is the characterization, **Stacks 0A1A**.
* `CategoryTheory.OverShriek.isPullback_relocalizeUnit`: a presheaf on the big fppf site of a
  smaller base is the fibre of the restriction of its lower-shriek extension above the
  tautological section. This is what makes the extension reflect algebraicity.

## Implementation notes

The hard direction is the one starting from the fibres in the étale neighbourhoods. It runs
through geometric connectedness over the residue field at the image point: the ordinary fibres
after all finite separable extensions of that residue field are exactly the fibres in the
affine étale neighbourhoods realizing those extensions
(`AlgebraicGeometry.Space.connectedPullback_finite_residueExtension`), and geometric
connectedness is detected by the finite separable extensions
(`AlgebraicGeometry.Space.isGeometricallyConnected_iff_connectedSpace_finite_separable`).
Turning the base changes of `f` along extensions of the residue field into restrictions of one
presheaf *over that residue field* is `AlgebraicGeometry.Space.exists_viewOver_iso`: the fibre
of `f` above the residue field point, which comes with a morphism to the representable presheaf
of the residue field spectrum, is the lower-shriek extension of an algebraic space over that
spectrum, and base change of the extension is the extension of the restriction
(`CategoryTheory.OverShriek.viewBaseChangeIso`).

Stacks 04SG gives the equivalence producing that presheaf, but only in the form of the forward
functor `AlgebraicGeometry.spacesOverSmallerBaseFunctor` and the presheaf-level equivalence
`AlgebraicGeometry.smallerBasePresheafEquivalence`; the latter supplies the presheaf, and its
algebraicity is obtained from the cartesian square of
`CategoryTheory.OverShriek.isPullback_relocalizeUnit`, whose other three corners are the
restriction of the fibre and two representable presheaves.

The easy direction is a continuous surjection. A geometric point of an algebraically closed
field dominates the residue field point below it
(`AlgebraicGeometry.Space.dominates_schemeResidueFieldPoint`), so the geometric fibre is a base
change of the fibre above the residue field point along a morphism of field spectra, which is
surjective on points because the point space of the representable presheaf of a field spectrum
in the site is a subsingleton.

## References

* [Stacks Project, Tag 0A1A](https://stacks.math.columbia.edu/tag/0A1A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.OverShriek

variable {C : Type v} [Category.{u} C] {U V : C} (f : V ⟶ U)

/-- The tautological section of the restriction along `f` of the representable presheaf of `f`:
over an object `W` of `C/V` it is the factorization of `W.hom ≫ f` through `f` given by `W.hom`
itself. -/
def restrictYonedaSelf :
    (yoneda.obj (Over.mk (𝟙 V)) : (Over V)ᵒᵖ ⥤ Type u) ⟶
      (relocalizeRestrict f).obj (yoneda.obj (Over.mk f)) where
  app W := ↾fun x => Over.homMk x.left (by
    rw [show x.left = (unop W).hom by simpa using Over.w x]
    rfl)
  naturality _ _ _ := by
    ext x
    exact Over.OverMorphism.ext rfl

/-- The unit of the lower-shriek adjunction: a section of `F` over `W` is the section of the
lower-shriek extension over `W` indexed by the tautological factorization `W.hom`. -/
def relocalizeUnit (F : (Over V)ᵒᵖ ⥤ Type u) :
    F ⟶ (relocalizeRestrict f).obj ((relocalizePresheafFunctor f).obj F) :=
  relocalizeToRestricted f (𝟙 ((relocalizePresheafFunctor f).obj F))

/-- **A presheaf is the fibre of the restriction of its lower-shriek extension.** The square
whose upper horizontal arrow is the unit and whose lower horizontal arrow is the tautological
section is cartesian: a section of the restricted extension over `W` is a factorization of
`W.hom ≫ f` through `f` together with a section over it, and prescribing the factorization to be
`W.hom` leaves exactly a section of `F` over `W`.

So an algebraic space over the smaller base is recovered from its lower-shriek extension as a
fibre product with two representable presheaves, which is how algebraicity descends along the
extension. -/
theorem isPullback_relocalizeUnit (F : (Over V)ᵒᵖ ⥤ Type u) :
    IsPullback (relocalizeUnit f F) (toYonedaMkId F)
      ((relocalizeRestrict f).map (viewStructureMap f F)) (restrictYonedaSelf f) := by
  refine IsPullback.of_forall_isPullback_app fun W => ?_
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext s
    exact Over.OverMorphism.ext rfl
  · rintro s s' ⟨h₁, -⟩
    have he : (⟨(unop W).hom, s⟩ :
        Σ ψ : (unop W).left ⟶ V, F.obj (op (Over.mk ψ))) = ⟨(unop W).hom, s'⟩ :=
      congrArg Subtype.val h₁
    simpa using he
  · rintro ⟨⟨ψ, s⟩, hψ⟩ x hxy
    have hx : x.left = (unop W).hom := by simpa using Over.w x
    obtain rfl : ψ = (unop W).hom := (congrArg Over.Hom.left hxy).trans hx
    exact ⟨s, Subtype.ext rfl, (subsingleton_yoneda_obj_mkId W).elim _ _⟩

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Descending algebraicity along the lower-shriek extension -/

/-- The presheaf-level form of
`AlgebraicGeometry.spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app`: the structural
morphism of the image of `F` under the presheaf equivalence of Stacks 04SG reads off the
factorization that a section of the lower-shriek extension carries. -/
private theorem smallerBasePresheafEquivalence_hom_app_forgetIso_inv_app
    (T : Scheme.{u}) (hT : B.Contains T) (g : B.obj hT ⟶ B.obj hS)
    (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) (W : (BigFppfOver B S hS)ᵒᵖ)
    (s : ((OverShriek.relocalizePresheafFunctor g).obj F).obj W) :
    (((smallerBasePresheafEquivalence B T S hT hS g).functor.obj F).hom.app W)
        (((smallerBasePresheafForgetIso B T S hT hS g).inv.app F).app W s) =
      Over.homMk s.1.1 s.2 :=
  Over.OverMorphism.ext rfl

/-- **The converse of Stacks 03I5 part (2).** If the lower-shriek extension of `F` along
`g : T ⟶ S` is an algebraic space over `S`, then `F` is an algebraic space over `T`.

By `CategoryTheory.OverShriek.isPullback_relocalizeUnit` the presheaf `F` is the fibre product of
the restriction of that extension with the representable presheaf of the identity of `T`, over
the restriction of the representable presheaf of `g`; all three are algebraic spaces over `T` by
Stacks 03I5 part (1). -/
private theorem isAlgebraicSpace_of_isAlgebraicSpace_relocalize
    (T : Scheme.{u}) (hT : B.Contains T) (g : B.obj hT ⟶ B.obj hS)
    (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
    (hΛ : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor g).obj F)) :
    IsAlgebraicSpace B T hT F := by
  have hH : IsAlgebraicSpace B T hT
      ((OverShriek.relocalizeRestrict g).obj (yoneda.obj (Over.mk g))) :=
    isAlgebraicSpace_relocalizeRestrict B T S hT hS g (yoneda.obj (Over.mk g))
      (isAlgebraicSpace_yoneda B S hS (Over.mk g))
  exact isAlgebraicSpace_of_isPullback
    (isAlgebraicSpace_relocalizeRestrict B T S hT hS g _ hΛ)
    (isAlgebraicSpace_yoneda B T hT (Over.mk (𝟙 (B.obj hT))))
    hH.isSheaf hH.diagonal_representable (OverShriek.isPullback_relocalizeUnit g F)

/-- **Stacks 04SG, essential surjectivity with algebraicity.** An algebraic space over `S` with a
morphism to the representable presheaf of `g : T ⟶ S` is the lower-shriek extension of an
algebraic space over `T`, compatibly with the two morphisms to that representable presheaf.

The presheaf is produced by the presheaf equivalence
`AlgebraicGeometry.smallerBasePresheafEquivalence`, and its algebraicity by
`AlgebraicGeometry.Space.isAlgebraicSpace_of_isAlgebraicSpace_relocalize`. -/
private theorem exists_viewOver_iso
    (T : Scheme.{u}) (hT : B.Contains T) (g : B.obj hT ⟶ B.obj hS)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (π : Q ⟶ yoneda.obj (Over.mk g)) :
    ∃ (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B T hT F),
      Nonempty {e : (OverShriek.relocalizePresheafFunctor g).obj F ≅ Q //
        e.hom ≫ π = OverShriek.viewStructureMap g F} := by
  let E := smallerBasePresheafEquivalence B T S hT hS g
  let Qπ : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := Over.mk π
  let F := E.inverse.obj Qπ
  let c := E.counitIso.app Qπ
  let e : (OverShriek.relocalizePresheafFunctor g).obj F ≅ Q :=
    ((smallerBasePresheafForgetIso B T S hT hS g).app F).symm ≪≫
      (Over.forget (yoneda.obj (Over.mk g))).mapIso c
  have he : e.hom ≫ π = OverShriek.viewStructureMap g F := by
    ext W s
    exact (congrArg (fun a => a.app W
        (((smallerBasePresheafForgetIso B T S hT hS g).inv.app F).app W s)) c.hom.w).trans
      (smallerBasePresheafEquivalence_hom_app_forgetIso_inv_app B S hS T hT g F W s)
  exact ⟨F, isAlgebraicSpace_of_isAlgebraicSpace_relocalize B S hS T hT g F
    (AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS e hQ), ⟨⟨e, he⟩⟩⟩

/-! ### From finite separable extensions to arbitrary ones -/

/-- **Connectedness of a fibre above a field-valued point is inherited from the finite separable
extensions.** Let `a` be a morphism to `Y` from the representable presheaf of a field spectrum
`Spec k` in the site. If the fibre of `f` above the induced `K`-valued point is connected for
every finite separable extension `K/k` whose spectrum lies in the site, then it is connected for
every extension `K/k` whose spectrum lies in the site.

The fibre of `f` above `a` is the lower-shriek extension of an algebraic space over `Spec k`
(`AlgebraicGeometry.Space.exists_viewOver_iso`), and the fibre above the `K`-valued point is the
extension of its restriction to `Spec K`
(`CategoryTheory.OverShriek.viewBaseChangeIso`), so the hypothesis says precisely that the
algebraic space over `Spec k` is geometrically connected in the sense of Stacks 0A17. -/
private theorem connectedPullback_fieldExtension
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (g : B.obj hk ⟶ B.obj hS) (a : yoneda.obj (Over.mk g) ⟶ Y)
    (hfinite : ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
      [Algebra.IsSeparable k K] (hK : B.Contains (Spec (.of K))),
      ConnectedPullback B S hS f
        (yoneda.map (Over.homMk (fieldExtensionMap B k K hk hK) rfl :
          Over.mk (fieldExtensionMap B k K hk hK ≫ g) ⟶ Over.mk g) ≫ a))
    (K : Type u) [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K))) :
    ConnectedPullback B S hS f
      (yoneda.map (Over.homMk (fieldExtensionMap B k K hk hK) rfl :
        Over.mk (fieldExtensionMap B k K hk hK ≫ g) ⟶ Over.mk g) ≫ a) := by
  have hQ := isAlgebraicSpace_pullback B S hS f a hX
    (isAlgebraicSpace_yoneda B S hS (Over.mk g)) hY
  obtain ⟨F, hF, ⟨e, he⟩⟩ :=
    exists_viewOver_iso B S hS (Spec (.of k)) hk g hQ (pullback.snd f a)
  have hcompare : ∀ (L : Type u) [Field L] [Algebra k L] (hL : B.Contains (Spec (.of L))),
      ConnectedPoints B (Spec (.of L)) hL
          ((OverShriek.relocalizeRestrict (fieldExtensionMap B k L hk hL)).obj F) ↔
        ConnectedPullback B S hS f
          (yoneda.map (Over.homMk (fieldExtensionMap B k L hk hL) rfl :
            Over.mk (fieldExtensionMap B k L hk hL ≫ g) ⟶ Over.mk g) ≫ a) := by
    intro L _ _ hL
    have hFL := isAlgebraicSpace_relocalizeRestrict B (Spec (.of L)) (Spec (.of k)) hL hk
      (fieldExtensionMap B k L hk hL) F hF
    have iso :=
      OverShriek.viewBaseChangeIso g (fieldExtensionMap B k L hk hL) F (pullback f a)
          (pullback.snd f a) e he ≪≫
        pullbackLeftPullbackSndIso f a
          (yoneda.map (Over.homMk (fieldExtensionMap B k L hk hL) rfl :
            Over.mk (fieldExtensionMap B k L hk hL ≫ g) ⟶ Over.mk g))
    exact (relocalizedPointsHomeomorph B (Spec (.of L)) S hL hS
          (fieldExtensionMap B k L hk hL ≫ g) _ hFL).connectedSpace_iff.trans
      (pointsHomeomorphOfIso B S hS iso).connectedSpace_iff
  have hgeom : IsGeometricallyConnected B k hk F :=
    (isGeometricallyConnected_iff_connectedSpace_finite_separable B k hk F hF).mpr
      fun L _ _ _ _ hL => (hcompare L hL).mpr (hfinite L hL)
  exact (hcompare K hK).mp (hgeom K hK)

/-! ### The characterization -/

/-- Composing the section of a presheaf given by a point with a morphism is the section given by
the image of that point. -/
private theorem yonedaEquiv_symm_comp_eq {C : Type*} [Category C] {P Q : Cᵒᵖ ⥤ Type v}
    (g : P ⟶ Q) {T : C} {x : P.obj (op T)} {z : Q.obj (op T)} (h : g.app (op T) x = z) :
    yonedaEquiv.symm x ≫ g = yonedaEquiv.symm z :=
  (yonedaEquiv_symm_naturality_right _ g _).trans (congrArg yonedaEquiv.symm h)

/-- **Stacks 0A1A.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big
fppf site and let `y` be a geometric point of `Y`. The geometric fibre of `f` above `y` is
connected if and only if, for every étale neighbourhood of `y` whose underlying algebraic space is
isomorphic to a scheme `W` of the site, the base change of `f` to that neighbourhood has connected
fibre above the point of `W` underlying the chosen lift of `y`.

Both fibres are presheaf fibre products, and the fibre above the point of `W` is the one above the
residue field point there
(`AlgebraicGeometry.Space.representedResidueFieldPointInNeighborhood`). -/
@[stacks 0A1A]
theorem connectedSpace_geometricFiber_iff_forall_scheme_etaleNeighborhood
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (y : GeometricPoint B S hS Y) :
    ConnectedPullback B S hS f (yonedaEquiv.symm y.val.value) ↔
      ∀ (U : EtaleNeighborhood B S hS Y hY y) (W : BigFppfOver B S hS)
        (e : U.space ≅ yoneda.obj W),
        ConnectedPullback B S hS f
          (yonedaEquiv.symm (representedResidueFieldPointInNeighborhood B S hS U W e).value ≫
            U.toBase) := by
  constructor
  · intro hconn U W e
    -- The geometric point dominates the residue field point below it.
    obtain ⟨c, hc⟩ := dominates_schemeResidueFieldPoint B S hS W
      (FieldValuedPoint.map B S hS U.space e.hom (liftedPoint U))
    have hvalue : U.space.map c.op
        (representedResidueFieldPointInNeighborhood B S hS U W e).value =
          (liftedPoint U).value := by
      have h := NatTrans.naturality_apply e.inv c.op
        (schemeResidueFieldPoint B S hS W (schemePoint B S hS W
          (FieldValuedPoint.map B S hS U.space e.hom (liftedPoint U)))).value
      refine h.symm.trans ?_
      rw [hc]
      have h₂ : (e.hom ≫ e.inv).app (op ((liftedPoint U).siteObject B S hS U.space))
          (liftedPoint U).value = (liftedPoint U).value := by
        rw [e.hom_inv_id]
        rfl
      exact h₂
    have hcval : yoneda.map c ≫
        yonedaEquiv.symm (representedResidueFieldPointInNeighborhood B S hS U W e).value =
          yonedaEquiv.symm (liftedPoint U).value :=
      (yonedaEquiv_symm_naturality_left c U.space _).trans (congrArg yonedaEquiv.symm hvalue)
    have hlift : yonedaEquiv.symm (liftedPoint U).value ≫ U.toBase =
        yonedaEquiv.symm y.val.value :=
      yonedaEquiv_symm_comp_eq U.toBase U.point_comp
    have hfac : yoneda.map c ≫
        (yonedaEquiv.symm (representedResidueFieldPointInNeighborhood B S hS U W e).value ≫
          U.toBase) = yonedaEquiv.symm y.val.value :=
      by rw [← Category.assoc, hcval]; exact hlift
    -- The morphism of field spectra is surjective on points, hence so is its base change.
    have hsurj : Function.Surjective
        (pointsMap B S hS (yoneda.obj y.val.siteObject) (yoneda.map c)) := fun _ =>
      ⟨(FieldValuedPoint.tautological B S hS (liftedPoint U)).class B S hS _,
        (subsingleton_points_yoneda_siteObject B S hS
          (representedResidueFieldPointInNeighborhood B S hS U W e)).elim _ _⟩
    have hsurj' := surjective_pointsMap_of_isPullback B S hS
      (IsPullback.of_hasPullback
        (pullback.snd f
          (yonedaEquiv.symm (representedResidueFieldPointInNeighborhood B S hS U W e).value ≫
            U.toBase)) (yoneda.map c)).flip hsurj
    -- Split the geometric fibre as a base change of the fibre above the residue field point.
    have : ConnectedSpace (points B S hS
      (pullback (pullback.snd f
        (yonedaEquiv.symm (representedResidueFieldPointInNeighborhood B S hS U W e).value ≫
          U.toBase)) (yoneda.map c))) :=
      connectedSpace_of_presheafIso B S hS
        (pullback_point_compIso f
          (yonedaEquiv.symm (representedResidueFieldPointInNeighborhood B S hS U W e).value ≫
            U.toBase) (yoneda.map c) (yonedaEquiv.symm y.val.value) hfac) hconn
    exact hsurj'.connectedSpace (continuous_pointsMap B S hS _)
  · intro hRHS
    -- Replace `Y` by a scheme-valued étale neighbourhood of `y`.
    let Uid : EtaleNeighborhood B S hS Y hY y :=
      { space := Y
        isAlgebraicSpace := hY
        toBase := 𝟙 Y
        etale_toBase := fun T φ hφ => by simpa using hφ
        point := y.val.value
        point_comp := by simp }
    obtain ⟨U₀, -, ⟨V, ⟨rep⟩⟩⟩ := exists_scheme_refinement B S hS Y hY y Uid
    let e₀ : U₀.space ≅ yoneda.obj V := rep.toIso.symm
    let a : yoneda.obj V ⟶ Y := e₀.inv ≫ U₀.toBase
    have ha : IsEtale B S hS a := fun T φ hφ =>
      U₀.etale_toBase T (φ ≫ e₀.inv) (MorphismProperty.RespectsIso.postcomp _ e₀.inv φ hφ)
    let q : y.val.siteObject ⟶ V := e₀.hom.app (op y.val.siteObject) U₀.point
    have hq : a.app (op y.val.siteObject) q = y.val.value := by
      simpa [a, q] using U₀.point_comp
    -- The point of `V` under the geometric point, and its residue field point.
    let pq : FieldValuedPoint B S hS (yoneda.obj V) :=
      { carrier := y.val.carrier
        field := y.val.field
        contained := y.val.contained
        toBase := y.val.toBase
        value := q }
    let v := schemePoint B S hS V pq
    let r := schemeResidueFieldPoint B S hS V v
    let Vsch := (BigFppfOver.toScheme B S hS).obj V
    let sp := (BigFppfOver.toScheme B S hS).map q
    let ep := Vsch.SpecToEquivOfField y.val.carrier sp
    let _ : Algebra (Vsch.residueField v) y.val.carrier := ep.2.hom.toAlgebra
    have hfacsp : Spec.map ep.2 ≫ Vsch.fromSpecResidueField ep.1 = sp :=
      (Vsch.SpecToEquivOfField y.val.carrier).symm_apply_apply sp
    have hc := connectedPullback_fieldExtension B S hS hX hY f
      (Vsch.residueField v) r.contained r.siteObject.hom (yoneda.map r.value ≫ a)
      (fun Kf _ _ _ _ hKf =>
        connectedPullback_finite_residueExtension B S hS hY f y hRHS V a ha q hq v rfl Kf hKf)
      y.val.carrier y.val.contained
    -- Identify the resulting fibre with the geometric fibre.
    let h : B.obj y.val.contained ⟶ B.obj r.contained :=
      fieldExtensionMap B (Vsch.residueField v) y.val.carrier r.contained y.val.contained
    let R : BigFppfOver B S hS := Over.mk (h ≫ r.siteObject.hom)
    let j : R ⟶ r.siteObject := Over.homMk h rfl
    have hj : h ≫ r.value.left = q.left := by
      apply B.inclusion.map_injective
      refine (B.inclusion.map_comp _ _).trans (Eq.trans ?_ hfacsp)
      exact congrArg (fun t => t ≫ Vsch.fromSpecResidueField v)
        (map_fieldExtensionMap B (Vsch.residueField v) y.val.carrier r.contained
          y.val.contained)
    let eR : R ≅ y.val.siteObject := Over.isoMk (Iso.refl _) (by
      show (𝟙 _) ≫ y.val.siteObject.hom = h ≫ r.siteObject.hom
      have hrw : r.value.left ≫ V.hom = r.siteObject.hom := r.value.w
      have hqw : q.left ≫ V.hom = y.val.siteObject.hom := q.w
      rw [Category.id_comp, ← hrw, ← Category.assoc, hj, hqw])
    have heR : yoneda.map eR.hom ≫ yonedaEquiv.symm y.val.value =
        yoneda.map j ≫ (yoneda.map r.value ≫ a) := by
      have hpj : j ≫ r.value = eR.hom ≫ q := by
        apply Over.OverMorphism.ext
        show h ≫ r.value.left = (𝟙 _) ≫ q.left
        simpa only [Category.id_comp] using hj
      rw [← Functor.map_comp_assoc, hpj, Functor.map_comp, Category.assoc]
      congr 1
      exact (yonedaEquiv_symm_comp_eq a hq).symm
    exact connectedPullback_of_iso B S hS f
      (yoneda.map j ≫ (yoneda.map r.value ≫ a)) (yonedaEquiv.symm y.val.value) eR heR hc

end AlgebraicGeometry.Space

end
