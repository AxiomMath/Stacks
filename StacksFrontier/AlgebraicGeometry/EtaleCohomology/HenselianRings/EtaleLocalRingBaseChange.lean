module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibre
public import StacksFrontier.RingTheory.Henselian.QuasiFiniteRingMaps

/-!
# Étale local rings and base change

Let `f : X ⟶ S` be a morphism of schemes, let `g : S' ⟶ S` be a second one and let
`X' = X ×_S S'` be the fibre product, with projections `g' : X' ⟶ X` and `f' : X' ⟶ S'`. A
geometric point `x'` of `X'` has images `x = g'(x')`, `s' = f'(x')` and `s = f(x) = g(s')`, and
the four étale local rings at these points sit in a commutative square

`𝒪^sh_{S,s} ⟶ 𝒪^sh_{X,x}`, `𝒪^sh_{S,s} ⟶ 𝒪^sh_{S',s'}`, both followed by maps to
`𝒪^sh_{X',x'}`.

This file constructs that square. It identifies each étale local ring with a strict
henselization of the ordinary local ring at the image of the corresponding point, and proves the
functoriality and locality of the induced homomorphisms. It also constructs an affine chart of
the cartesian square at a point of the fibre product: affine opens `U` of `S`, `V` of `X` and
`W` of `S'` with `V` and `W` over `U`, such that `g'⁻¹V ∩ f'⁻¹W` is an affine open of `X'`
containing the point whose sections are the tensor product of the sections over `V` and over `W`
above the sections over `U`.

## Main results

* `AlgebraicGeometry.GeometricPoint.map_eq_of_isPullback` identifies the two images in `S` of a
  geometric point of a fibre product.
* `AlgebraicGeometry.isHenselization_etaleLocalRing` and
  `AlgebraicGeometry.isSepClosure_residueField_etaleLocalRing` say that the étale local ring at
  a geometric point is a henselization of the ordinary local ring at the image of that point,
  with residue field a separable closure of the residue field there, and
  `AlgebraicGeometry.henselianLocalRing_etaleLocalRing` that it is henselian.
* `AlgebraicGeometry.etaleLocalRingHom_comp` is the functoriality of the induced homomorphism of
  étale local rings, and `AlgebraicGeometry.isLocalHom_etaleLocalRingHom` says that homomorphism
  is local.
* `AlgebraicGeometry.baseChangeEtaleLocalRingHom` is the canonical homomorphism
  `𝒪^sh_{S,s} ⟶ 𝒪^sh_{S',s'}` with the image of the point taken through `X`, and
  `AlgebraicGeometry.etaleLocalRingHom_comp_baseChangeEtaleLocalRingHom` says that the square of
  étale local rings attached to a cartesian square commutes.
* `AlgebraicGeometry.isAffineOpen_of_isPullback` and
  `AlgebraicGeometry.isPushout_appLE_of_isPullback_inter` give the affine chart and its pushout
  square of sections, `AlgebraicGeometry.exists_isPushout_appLE_chart_of_isPullback` their
  combination at a prescribed point, and `AlgebraicGeometry.comap_primeIdealOf_appLE_comp_appLE`
  the contraction of the prime of the chart at that point to the base.

## Implementation notes

The étale local ring at a geometric point carries that point in its type, so the two ways of
reading off the image of a geometric point of `X'` in `S` — through `X` and through `S'` — give
two étale local rings which are equal, but only after rewriting along the commutativity of the
cartesian square. The image through `X` is taken as the base throughout, and the one
identification that this makes unavoidable is isolated in
`AlgebraicGeometry.baseChangeEtaleLocalRingHom`. Composition of a geometric point with two
morphisms, on the other hand, needs no transport: it agrees with composition with the composite
morphism definitionally, which is what makes `AlgebraicGeometry.etaleLocalRingHom_comp` a plain
equation between homomorphisms.

The residue field of the étale local ring is used as the prescribed residue extension, rather
than the separable closure which the chosen henselization tower uses: the identification of the
two is recorded as an isomorphism of extensions, so that the separable closure property transfers
to the residue field itself.

## References

* [Stacks Project, Tag 0GIP](https://stacks.math.columbia.edu/tag/0GIP)
* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

/-- In a cartesian square, the two images in the base of a geometric point of the fibre product
agree: the one taken through the second factor is the one taken through the first. -/
public theorem map_eq_of_isPullback {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) (x' : GeometricPoint X') :
    (x'.map f').map g = (x'.map g').map f :=
  congrArg x'.map sq.w.symm

end GeometricPoint

section Henselization

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The identification of the residue field of the étale local ring with a separable closure
carries the residue of a germ to the residue of its image. -/
public theorem etaleResidueFieldSeparableClosureEquiv_residue
    (r : ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))) :
    etaleResidueFieldSeparableClosureEquiv B S hS s
        (algebraMap (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
          ↥(separableClosure
            (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
            s.residueField) (residue _ r)) =
      residue ↥(etaleLocalRing B S hS s) (algebraMap _ ↥(etaleLocalRing B S hS s) r) := by
  have hloc : IsLocalHom (etaleLocalRingEquivStrictHenselization B S hS s).toRingHom :=
    IsLocalHom.of_surjective _ (etaleLocalRingEquivStrictHenselization B S hS s).surjective
  have h1 := (geometricHenselizationTower S s).strictHenselizationResidueEquiv_residue r
  have h2 := ResidueField.map_residue
    (etaleLocalRingEquivStrictHenselization B S hS s).toRingHom
    (algebraMap _ (geometricHenselizationTower S s).strictHenselization r)
  have h3 := (etaleLocalRing_strictHenselization_canonical B S hS s
    (geometricHenselizationTower S s)).property.1 r
  change ResidueField.mapEquiv (etaleLocalRingEquivStrictHenselization B S hS s)
    ((geometricHenselizationTower S s).strictHenselizationResidueEquiv _) = _
  rw [h1]
  exact h2.trans (congrArg _ h3)

/-- The étale local ring at a geometric point is a henselian local ring: it is the strict
henselization of the ordinary local ring at the image of that point. -/
public instance henselianLocalRing_etaleLocalRing :
    HenselianLocalRing ↥(etaleLocalRing B S hS s) :=
  HenselianLocalRing.of_ringEquiv (etaleLocalRingEquivStrictHenselization B S hS s)

/-- The étale local ring at a geometric point is a henselization of the ordinary local ring at
the image of that point, with its own residue field as the prescribed residue extension. -/
public instance isHenselization_etaleLocalRing :
    IsHenselization ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (ResidueField ↥(etaleLocalRing B S hS s)) ↥(etaleLocalRing B S hS s) :=
  IsHenselization.of_ind_etale inferInstance
    (StacksDraft.indEtale_iff.mp (indEtale_etaleLocalRing B S hS s))
    ⟨RingEquiv.refl _, fun x => ResidueField.map_residue _ x⟩

/-- The identification of the residue field of the étale local ring with a separable closure of
the residue field of the ordinary local ring is an isomorphism of extensions of the latter. -/
public def etaleResidueFieldSeparableClosureAlgEquiv :
    ↥(separableClosure
        (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
        s.residueField) ≃ₐ[
      ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))]
      ResidueField ↥(etaleLocalRing B S hS s) :=
  { etaleResidueFieldSeparableClosureEquiv B S hS s with
    commutes' := fun c => by
      obtain ⟨r, rfl⟩ := residue_surjective
        (R := ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))) c
      exact (etaleResidueFieldSeparableClosureEquiv_residue B S hS s r).trans
        (ResidueField.map_residue (algebraMap _ ↥(etaleLocalRing B S hS s)) r).symm }

/-- The residue field of the étale local ring at a geometric point is a separable closure of the
residue field of the ordinary local ring at the image of that point. -/
public instance isSepClosure_residueField_etaleLocalRing :
    IsSepClosure (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
      (ResidueField ↥(etaleLocalRing B S hS s)) :=
  have := IsSepClosure.sep_closed
    (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
    (K := ↥(separableClosure
      (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
      s.residueField))
  ⟨IsSepClosed.of_ringEquiv
      (etaleResidueFieldSeparableClosureAlgEquiv B S hS s).symm.toRingEquiv,
    AlgEquiv.Algebra.isSeparable (etaleResidueFieldSeparableClosureAlgEquiv B S hS s)⟩

end Henselization

section Functoriality

variable (B : BigEtaleSite.{u}) {X Y Z : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)
  (hZ : B.Contains Z) (f : X ⟶ Y) (h : Y ⟶ Z) (x : GeometricPoint X)

/-- **Functoriality of the étale local ring.** The homomorphisms of étale local rings induced by
two morphisms of schemes compose to the one induced by their composite. -/
public theorem etaleLocalRingHom_comp :
    etaleLocalRingHom B hX hZ (f ≫ h) x =
      (etaleLocalRingHom B hX hY f x).comp (etaleLocalRingHom B hY hZ h (x.map f)) := by
  refine (existsUnique_etaleLocalRingHom B hX hZ (f ≫ h) x).unique
    ⟨etaleLocalRingHom_comp_fromLocalRing B hX hZ (f ≫ h) x,
      toGeometricField_comp_etaleLocalRingHom B hX hZ (f ≫ h) x⟩ ⟨?_, ?_⟩
  · refine RingHom.ext fun r => ?_
    have c1 : etaleLocalRingHom B hY hZ h (x.map f)
          (structureSheafStalkFromLocalRing B Z hZ (x.map (f ≫ h)) r) =
        structureSheafStalkFromLocalRing B Y hY (x.map f)
          ((h.stalkMap ((x.map f).hom (closedPoint (x.map f).residueField))).hom r) :=
      RingHom.congr_fun (etaleLocalRingHom_comp_fromLocalRing B hY hZ h (x.map f)) r
    have c2 : etaleLocalRingHom B hX hY f x
          (structureSheafStalkFromLocalRing B Y hY (x.map f)
            ((h.stalkMap ((x.map f).hom (closedPoint (x.map f).residueField))).hom r)) =
        structureSheafStalkFromLocalRing B X hX x
          ((f.stalkMap (x.hom (closedPoint x.residueField))).hom
            ((h.stalkMap ((x.map f).hom (closedPoint (x.map f).residueField))).hom r)) :=
      RingHom.congr_fun (etaleLocalRingHom_comp_fromLocalRing B hX hY f x) _
    have c3 : ((f ≫ h).stalkMap (x.hom (closedPoint x.residueField))).hom r =
        (f.stalkMap (x.hom (closedPoint x.residueField))).hom
          ((h.stalkMap ((x.map f).hom (closedPoint (x.map f).residueField))).hom r) :=
      ConcreteCategory.congr_hom
        (Scheme.Hom.stalkMap_comp f h (x.hom (closedPoint x.residueField))) r
    exact ((congrArg (etaleLocalRingHom B hX hY f x) c1).trans c2).trans
      (congrArg (structureSheafStalkFromLocalRing B X hX x) c3.symm)
  · refine RingHom.ext fun a => ?_
    exact (RingHom.congr_fun (toGeometricField_comp_etaleLocalRingHom B hX hY f x)
        (etaleLocalRingHom B hY hZ h (x.map f) a)).trans
      (RingHom.congr_fun (toGeometricField_comp_etaleLocalRingHom B hY hZ h (x.map f)) a)

/-- The homomorphism of étale local rings induced by a morphism of schemes is a local
homomorphism. -/
public instance isLocalHom_etaleLocalRingHom : IsLocalHom (etaleLocalRingHom B hX hY f x) := by
  refine ⟨fun a ha => notMem_maximalIdeal.mp fun hma => notMem_maximalIdeal.mpr ha ?_⟩
  refine (residue_eq_zero_iff _).mp (etaleResidueFieldToGeometricField_injective B X hX x ?_)
  refine Eq.trans ?_ (map_zero (etaleResidueFieldToGeometricField B X hX x)).symm
  refine (etaleResidueFieldToGeometricField_residue B X hX x _).trans ?_
  refine (RingHom.congr_fun (toGeometricField_comp_etaleLocalRingHom B hX hY f x) a).trans ?_
  refine (etaleResidueFieldToGeometricField_residue B Y hY (x.map f) a).symm.trans ?_
  exact (congrArg (etaleResidueFieldToGeometricField B Y hY (x.map f))
      ((residue_eq_zero_iff a).mpr hma)).trans
    (map_zero (etaleResidueFieldToGeometricField B Y hY (x.map f)))

end Functoriality

section BaseChange

variable (B : BigEtaleSite.{u}) {X S S' X' : Scheme.{u}} (hS : B.Contains S)
  (hS' : B.Contains S') {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- Transport of a homomorphism out of an étale local ring along an equality of geometric
points. -/
public def etaleLocalRingHomCongr {T : Type u} [CommRing T] {s t : GeometricPoint S}
    (e : s = t) (φ : ↥(etaleLocalRing B S hS s) →+* T) :
    ↥(etaleLocalRing B S hS t) →+* T :=
  e ▸ φ

/-- The transport of a local homomorphism along an equality of geometric points is local. -/
public theorem isLocalHom_etaleLocalRingHomCongr {T : Type u} [CommRing T]
    {s t : GeometricPoint S} (e : s = t) (φ : ↥(etaleLocalRing B S hS s) →+* T)
    (hφ : IsLocalHom φ) : IsLocalHom (etaleLocalRingHomCongr B hS e φ) := by
  subst e; exact hφ

/-- The canonical homomorphism from the étale local ring of the base at the image of a geometric
point of the fibre product, taken through the first factor, to the étale local ring of the second
factor. It is the homomorphism induced by `g`, read at the image through the first factor by
means of `AlgebraicGeometry.GeometricPoint.map_eq_of_isPullback`. -/
public def baseChangeEtaleLocalRingHom (sq : IsPullback g' f' f g) (x' : GeometricPoint X') :
    ↥(etaleLocalRing B S hS ((x'.map g').map f)) →+*
      ↥(etaleLocalRing B S' hS' (x'.map f')) :=
  etaleLocalRingHomCongr B hS (GeometricPoint.map_eq_of_isPullback sq x')
    (etaleLocalRingHom B hS' hS g (x'.map f'))

/-- The canonical homomorphism out of the étale local ring of the base is a local
homomorphism. -/
public instance isLocalHom_baseChangeEtaleLocalRingHom (sq : IsPullback g' f' f g)
    (x' : GeometricPoint X') : IsLocalHom (baseChangeEtaleLocalRingHom B hS hS' sq x') :=
  isLocalHom_etaleLocalRingHomCongr B hS _ _ inferInstance

/-- Transport along an equality of geometric points commutes with postcomposition. -/
public theorem etaleLocalRingHomCongr_comp {T T' : Type u} [CommRing T] [CommRing T']
    {s t : GeometricPoint S} (e : s = t) (φ : ↥(etaleLocalRing B S hS s) →+* T)
    (ψ : T →+* T') :
    etaleLocalRingHomCongr B hS e (ψ.comp φ) =
      ψ.comp (etaleLocalRingHomCongr B hS e φ) := by
  subst e; rfl

/-- The homomorphism of étale local rings induced by a morphism depends on the morphism only
through the geometric point it is read at. -/
public theorem etaleLocalRingHom_eq_congr {Y : Scheme.{u}} (hY : B.Contains Y)
    {k k' : Y ⟶ S} (hk : k = k') (y : GeometricPoint Y) :
    etaleLocalRingHom B hY hS k y =
      etaleLocalRingHomCongr B hS (congrArg y.map hk.symm)
        (etaleLocalRingHom B hY hS k' y) := by
  subst hk; rfl

/-- **The square of étale local rings attached to a cartesian square commutes.** Both composites
from the étale local ring of the base at the image of a geometric point of the fibre product to
the étale local ring of the fibre product at that point — the one through the first factor and
the one through the second — agree, being the homomorphism induced by the diagonal of the
square. -/
public theorem etaleLocalRingHom_comp_baseChangeEtaleLocalRingHom (hX : B.Contains X)
    (hX' : B.Contains X') (sq : IsPullback g' f' f g) (x' : GeometricPoint X') :
    (etaleLocalRingHom B hX' hX g' x').comp (etaleLocalRingHom B hX hS f (x'.map g')) =
      (etaleLocalRingHom B hX' hS' f' x').comp
        (baseChangeEtaleLocalRingHom B hS hS' sq x') := by
  rw [baseChangeEtaleLocalRingHom, ← etaleLocalRingHomCongr_comp,
    ← etaleLocalRingHom_comp B hX' hS' hS f' g x', ← etaleLocalRingHom_comp B hX' hX hS g' f x']
  exact etaleLocalRingHom_eq_congr B hS hX' sq.w x'

end BaseChange

section Chart

variable {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- **An affine chart for a cartesian square at a point of the fibre product.** Given a
cartesian square and a point `p` of the fibre product, there are affine opens `U` of the base,
`V` of the first factor and `W` of the second factor, with `V` and `W` over `U`, such that the
images of `p` lie in `V` and in `W`. -/
public theorem exists_affineOpen_chart_of_isPullback (sq : IsPullback g' f' f g) (p : X') :
    ∃ (U : S.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (W : S'.Opens) (_ : IsAffineOpen W) (_ : V ≤ f ⁻¹ᵁ U) (_ : W ≤ g ⁻¹ᵁ U),
      g' p ∈ V ∧ f' p ∈ W := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : S.Opens)) (x := f (g' p)) trivial
  have hyU' : g (f' p) ∈ U := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun q : X' ⟶ S => q p) sq.w ▸ hyU
  obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (U := f ⁻¹ᵁ U) (x := g' p) hyU
  obtain ⟨W, hW, hwW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (U := g ⁻¹ᵁ U) (x := f' p) hyU'
  exact ⟨U, hU, V, hV, W, hW, hVU, hWU, hzV, hwW⟩

/-- In a cartesian square, an open of the fibre product which is the intersection of the
preimages of affine opens `V` of the first factor and `W` of the second factor, both lying over
an affine open `U` of the base, is affine: it is the fibre product of `V` and `W` over `U`. -/
public theorem isAffineOpen_of_isPullback (sq : IsPullback g' f' f g)
    {U : S.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    {W : S'.Opens} (hW : IsAffineOpen W) (hVU : V ≤ f ⁻¹ᵁ U) (hWU : W ≤ g ⁻¹ᵁ U)
    {U' : X'.Opens} (hU'def : U' = g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ W) : IsAffineOpen U' :=
  have : IsAffine V.toScheme := hV
  have : IsAffine W.toScheme := hW
  have : IsAffine U.toScheme := hU
  IsAffine.of_isPullback (Scheme.Hom.isPullback_resLE sq hWU hVU hU'def)

/-- **The sections over an affine chart of a cartesian square form a pushout square of rings.**
For affine opens `U` of the base, `V` of the first factor and `W` of the second factor with `V`
and `W` over `U`, the sections over the open `g'⁻¹V ∩ f'⁻¹W` of the fibre product are the tensor
product of the sections over `V` and over `W` above the sections over `U`. -/
public theorem isPushout_appLE_of_isPullback_inter (sq : IsPullback g' f' f g)
    {U : S.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    {W : S'.Opens} (hW : IsAffineOpen W) (hVU : V ≤ f ⁻¹ᵁ U) (hWU : W ≤ g ⁻¹ᵁ U)
    {U' : X'.Opens} (hU'def : U' = g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ W) (hU'V : U' ≤ g' ⁻¹ᵁ V)
    (hU'W : U' ≤ f' ⁻¹ᵁ W) :
    IsPushout (f.appLE U V hVU) (g.appLE U W hWU) (g'.appLE V U' hU'V)
      (f'.appLE W U' hU'W) := by
  let _ : IsAffine V.toScheme := hV
  let _ : IsAffine W.toScheme := hW
  let _ : IsAffine U.toScheme := hU
  have hPB := Scheme.Hom.isPullback_resLE sq hWU hVU hU'def
  let _ : IsAffine U'.toScheme := IsAffine.of_isPullback hPB
  have hpush0 := isPushout_appTop_of_isPullback hPB
  refine IsPushout.of_iso hpush0
    U.topIso V.topIso W.topIso U'.topIso ?_ ?_ ?_ ?_
  · exact (arrowResLEAppIso f U V hVU).hom.w.symm
  · exact (arrowResLEAppIso g U W hWU).hom.w.symm
  · exact (arrowResLEAppIso g' V U' hU'V).hom.w.symm
  · exact (arrowResLEAppIso f' W U' hU'W).hom.w.symm

/-- **An affine pushout chart for a cartesian square at a point of the fibre product.** The
chart of `AlgebraicGeometry.exists_affineOpen_chart_of_isPullback`, together with the affineness
of the induced open of the fibre product and the pushout square of sections over it. -/
public theorem exists_isPushout_appLE_chart_of_isPullback (sq : IsPullback g' f' f g) (p : X') :
    ∃ (U : S.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (W : S'.Opens) (_ : IsAffineOpen W) (hVU : V ≤ f ⁻¹ᵁ U) (hWU : W ≤ g ⁻¹ᵁ U)
      (hU'V : g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ W ≤ g' ⁻¹ᵁ V) (hU'W : g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ W ≤ f' ⁻¹ᵁ W),
      g' p ∈ V ∧ f' p ∈ W ∧ IsAffineOpen (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ W) ∧
        IsPushout (f.appLE U V hVU) (g.appLE U W hWU)
          (g'.appLE V (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ W) hU'V)
          (f'.appLE W (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ W) hU'W) := by
  obtain ⟨U, hU, V, hV, W, hW, hVU, hWU, hzV, hwW⟩ :=
    exists_affineOpen_chart_of_isPullback sq p
  exact ⟨U, hU, V, hV, W, hW, hVU, hWU, inf_le_left, inf_le_right, hzV, hwW,
    isAffineOpen_of_isPullback sq hU hV hW hVU hWU rfl,
    isPushout_appLE_of_isPullback_inter sq hU hV hW hVU hWU rfl inf_le_left inf_le_right⟩

/-- The prime of the sections over the chart at a point of the fibre product contracts, along
the structure map from the sections over the chart of the base, to the prime there at the image
of the point. -/
public theorem comap_primeIdealOf_appLE_comp_appLE {U : S.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} {U' : X'.Opens} (hU' : IsAffineOpen U')
    (hVU : V ≤ f ⁻¹ᵁ U) (hU'V : U' ≤ g' ⁻¹ᵁ V) {p : X'} (hp : p ∈ U')
    (hyU : f (g' p) ∈ U) :
    (hU'.primeIdealOf ⟨p, hp⟩).asIdeal.comap
        ((g'.appLE V U' hU'V).hom.comp (f.appLE U V hVU).hom) =
      (hU.primeIdealOf ⟨f (g' p), hyU⟩).asIdeal := by
  have hU'U : U' ≤ (g' ≫ f) ⁻¹ᵁ U := fun q hq => hVU (hU'V hq)
  have hAD : (g'.appLE V U' hU'V).hom.comp (f.appLE U V hVU).hom =
      ((g' ≫ f).appLE U U' hU'U).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE g' f U V U' hVU hU'V)
  refine Eq.trans ?_ (congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE U hU U' hU' hU'U hp))
  exact congrArg (fun φ => (hU'.primeIdealOf ⟨p, hp⟩).asIdeal.comap φ) hAD

end Chart

end AlgebraicGeometry

end
