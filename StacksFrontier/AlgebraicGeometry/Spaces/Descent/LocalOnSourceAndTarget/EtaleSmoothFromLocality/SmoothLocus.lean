module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothFromLocality.EtalePostcomposition

/-!
# Étale-smooth locality from locality hypotheses: the largest open locus and smooth morphisms

The behaviour of the largest open locus of the induced property of morphisms of schemes over `S`
under smooth base change, computed through affine spaces over the residue fields and their
coordinate shears and endomorphisms `xᵢ - xᵢ ^ p`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry

attribute [local instance] bounded_open
attribute [local instance] bounded_pullback
attribute [local instance] bounded_affineSpace
attribute [local instance] pullbackCanonicallyOverRight
attribute [local instance] pullbackSnd_isOver
attribute [local instance] pullbackFst_isOver
attribute [local instance] pullbackLift_isOver
attribute [local instance] affineCoverCanonicallyOver
attribute [local instance] affineCoverMap_isOver
attribute [local instance] bounded_affineCover
attribute [local instance] bounded_openCover

/-- An elementary coordinate shear of affine space over a scheme over `S` is a morphism over
`S`. -/
theorem coordinateShear_isOver
    {Y S : Scheme.{u}} [Y.Over S] {n : Type u} [DecidableEq n]
    (i j : n) (hij : i ≠ j) (d : ℕ) :
    (affineSpaceCoordinateShearIso (S := Y) i j hij d).hom.IsOver S := by
  constructor
  show affineSpaceCoordinateShear i j hij d ≫
    ((AffineSpace n Y ↘ Y) ≫ Y ↘ S) = (AffineSpace n Y ↘ Y) ≫ Y ↘ S
  rw [← Category.assoc]
  simp only [affineSpaceCoordinateShear, AffineSpace.homOfVector_over]

attribute [local instance] coordinateShear_isOver

/-- The endomorphism of affine space with coordinates `xᵢ - xᵢ ^ p` is a morphism over `S`. -/
theorem subPow_isOver
    {Y S : Scheme.{u}} [Y.Over S] {n : Type u} (p : ℕ) :
    (affineSpaceSubPow (S := Y) (n := n) p).IsOver S := by
  constructor
  show affineSpaceSubPow p ≫
    ((AffineSpace n Y ↘ Y) ≫ Y ↘ S) = (AffineSpace n Y ↘ Y) ≫ Y ↘ S
  rw [← Category.assoc]
  simp only [affineSpaceSubPow, AffineSpace.homOfVector_over]

attribute [local instance] subPow_isOver

/-- A reindexing of affine space over a scheme over `S` is a morphism over `S`. -/
theorem reindex_isOver
    {Y S : Scheme.{u}} [Y.Over S] {n m : Type u} (i : m → n) :
    (AffineSpace.reindex i Y).IsOver S := by
  constructor
  show AffineSpace.reindex i Y ≫
    ((AffineSpace m Y ↘ Y) ≫ Y ↘ S) = (AffineSpace n Y ↘ Y) ≫ Y ↘ S
  rw [← Category.assoc, AffineSpace.reindex_over]

attribute [local instance] reindex_isOver

/-- A property local on the target for the smooth topology descends along a surjective
smooth base change. -/
private theorem of_smooth_surjective_isPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .smooth B S hS)]
    {X' X Y' Y : Scheme.{u}} [Y'.Over S] [Y.Over S]
    [Fact (B.Contains X')] [Fact (B.Contains X)]
    [Fact (B.Contains Y')] [Fact (B.Contains Y)]
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [g.IsOver S] (h : IsPullback a b f g) [Smooth g] [Surjective g]
    (hb : relativeProperty B S hS P b) : relativeProperty B S hS P f :=
  relative_of_surjective_isPullback B S hS P a b f g h hb

/-- If `φ` and `ψ` are intertwined by `e`, and `ψ` preserves membership in `U` along the image of
`e`, then `φ` preserves the preimage of `U` under `e`. -/
private theorem preimage_preimage_eq_of_comm {A B : Scheme.{u}} (e : A ⟶ B) (φ : A ⟶ A)
    (ψ : B ⟶ B) (U : B.Opens) (hcomm : φ ≫ e = e ≫ ψ)
    (hU : ∀ z : A, ψ.base (e.base z) ∈ U ↔ e.base z ∈ U) :
    φ ⁻¹ᵁ (e ⁻¹ᵁ U) = e ⁻¹ᵁ U := by
  ext z
  show e.base (φ.base z) ∈ U ↔ e.base z ∈ U
  rw [show e.base (φ.base z) = ψ.base (e.base z) from congrArg (fun k => k.base z) hcomm]
  exact hU z

/-- The projection of relative affine space is compatible with the induced map of affine
spaces. -/
private theorem affineSpace_over_map_apply {A B : Scheme.{u}} {n : Type u} (g : A ⟶ B)
    (w : AffineSpace n A) :
    (AffineSpace n B ↘ B).base (AffineSpace.map n g w) = g.base ((AffineSpace n A ↘ A).base w) :=
  congrArg (fun k => k.base w) (AffineSpace.map_over g)

section RelativeSmoothLocus

open CategoryTheory.Limits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty (AlgebraicSpaces B S hS))
  [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, u + 1} .etale B S hS)]
  [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .smooth B S hS)]
  [hopen : P.RespectsRight (fun ⦃X Y : AlgebraicSpaces B S hS⦄
    (f : X ⟶ Y) => Space.IsOpenImmersion B S hS f.hom)]


omit hopen in
/-- In a cartesian square whose base morphism is smooth, the inverse image of the largest
open locus downstairs is contained in the largest open locus upstairs. -/
private lemma preimage_largestOpen_le_of_smooth_isPullback
    {X' X Y' Y : Scheme.{u}} [Y'.Over S] [Y.Over S] [Fact (B.Contains X')] [Fact (B.Contains X)]
      [Fact (B.Contains Y')] [Fact (B.Contains Y)] {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [g.IsOver S] (h : IsPullback a b f g) [Smooth g] :
    a ⁻¹ᵁ relativeLargestOpen B S hS P f ≤ relativeLargestOpen B S hS P b := by
  let U := relativeLargestOpen B S hS P f
  have hU : relativeProperty B S hS P (U.ι ≫ f) := (relativeLargestOpen_isGreatest B S hS P f).1
  have hp := (isPullback_morphismRestrict a U).paste_vert h
  have hbase := relative_pullback_snd B S hS P (U.ι ≫ f) g hU
  have hV : relativeProperty B S hS P ((a ⁻¹ᵁ U).ι ≫ b) := by
    rw [← hp.isoPullback_hom_snd]
    exact (relative_cancel_left_iso B S hS P hp.isoPullback.hom _).mpr hbase
  exact (relativeLargestOpen_isGreatest B S hS P b).2 hV

/-- A pair of automorphisms of the source and the target commuting with a morphism
preserves its largest open locus. -/
private lemma largestOpen_invariant_under_iso
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y)
    (eX : X ≅ X) (eY : Y ≅ Y) [eY.hom.IsOver S]
    (hcomm : eX.hom ≫ f = f ≫ eY.hom) :
    eX.hom ⁻¹ᵁ relativeLargestOpen B S hS P f = relativeLargestOpen B S hS P f := by
  ext x
  show eX.hom.base x ∈ relativeLargestOpen B S hS P f ↔
    x ∈ relativeLargestOpen B S hS P f
  have : Etale eX.hom := inferInstance
  have : Etale eY.hom := inferInstance
  exact mem_relativeLargestOpen_etaleAt B S hS P f f eY.hom eX.hom
    hcomm x
    ((etale_iff_forall_etaleAt eX.hom).mp inferInstance x)
    ((etale_iff_forall_etaleAt eY.hom).mp inferInstance
      (f.base x))

/-- The largest open locus of the induced morphism of affine spaces is invariant under every
elementary coordinate shear. -/
private lemma affineSpace_largestOpen_invariant_under_coordinateShear
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y) {n :
      Type u} [Finite n] [DecidableEq n]
    (i j : n) (hij : i ≠ j) (d : ℕ) :
    affineSpaceCoordinateShear i j hij d ⁻¹ᵁ
        relativeLargestOpen B S hS P (AffineSpace.map n f) =
      relativeLargestOpen B S hS P (AffineSpace.map n f) :=
  largestOpen_invariant_under_iso B S hS P (AffineSpace.map n f)
    (affineSpaceCoordinateShearIso i j hij d)
    (affineSpaceCoordinateShearIso i j hij d)
    (affineSpace_map_comm_coordinateShear f i j hij d).symm

/-- The fibre over a point of the base of the largest open locus of the induced morphism of
affine spaces, viewed as an open of affine space over the residue field of that point. -/
private noncomputable def affineSpace_fiber_largestOpen
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] {n : Type u}
      [Finite n]
    (f : X ⟶ Y) (x : X) :
    (AffineSpace n (Spec (X.residueField x))).Opens :=
  (AffineSpace.map n (X.fromSpecResidueField x)) ⁻¹ᵁ
    relativeLargestOpen B S hS P (AffineSpace.map n f)

/-- The fibre of the largest open locus is invariant under every elementary coordinate
shear. -/
private lemma affineSpace_fiber_largestOpen_shear_preimage
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] {n : Type u}
      [Finite n] [DecidableEq n]
    (f : X ⟶ Y) (x : X)
    (i j : n) (hij : i ≠ j) (d : ℕ) :
    affineSpaceCoordinateShear i j hij d ⁻¹ᵁ
        affineSpace_fiber_largestOpen B S hS P f x =
      affineSpace_fiber_largestOpen B S hS P f x := by
  exact preimage_preimage_eq_of_comm _ _ _ _
    (affineSpace_map_comm_coordinateShear (X.fromSpecResidueField x) i j hij d).symm fun z =>
    SetLike.ext_iff.mp
      (affineSpace_largestOpen_invariant_under_coordinateShear B S hS P f i j hij d) _

/-- Read on the prime spectrum of the polynomial ring over the residue field, the fibre of the
largest open locus is invariant under every coordinate shear. -/
private lemma affineSpace_fiber_largestOpen_specIso_shear_invariant
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y)
    (x : X) (d : ℕ) (i j : Fin d) (hij : i ≠ j) (r : ℕ) :
    PrimeSpectrum.comap
        (coordinateShearULift (R := ↑(X.residueField x)) i j hij r).toRingHom ⁻¹'
      ((AffineSpace.SpecIso (ULift.{u} (Fin d)) (X.residueField x)).inv ⁻¹ᵁ
        affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) B S hS P f x).carrier =
      ((AffineSpace.SpecIso (ULift.{u} (Fin d)) (X.residueField x)).inv ⁻¹ᵁ
        affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) B S hS P f x).carrier := by
  exact congrArg SetLike.coe (preimage_preimage_eq_of_comm _ _ _
    (affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) B S hS P f x)
    (affineSpace_fiberSpecIso_inv_shear (.of (X.residueField x)) d i j hij r) fun z =>
    SetLike.ext_iff.mp (affineSpace_fiber_largestOpen_shear_preimage B S hS P f x
      (ULift.up i) (ULift.up j) (fun h => hij (congrArg ULift.down h)) r) _)

/-- For `d ≥ 2`, a nonempty fibre of the largest open locus which in positive characteristic
is invariant under the endomorphism with coordinates `xᵢ - xᵢ ^ p` for `p` the
characteristic is all of affine space over the residue field. -/
private lemma affineSpace_fiber_largestOpen_eq_top_of_sub_pow_invariant
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y)
    (x : X) (d : ℕ) (hd : 2 ≤ d)
    (hnonempty : Nonempty (affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) B S hS P f x))
    (hfrob : 0 < ringChar (X.residueField x) →
      affineSpaceSubPow (ringChar (X.residueField x)) ⁻¹ᵁ
        affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) B S hS P f x =
        affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) B S hS P f x) :
    affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) B S hS P f x = ⊤ := by
  classical
  let U := affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) B S hS P f x
  let e := AffineSpace.SpecIso (ULift.{u} (Fin d)) (X.residueField x)
  let W : Set (PrimeSpectrum
      (MvPolynomial (ULift.{u} (Fin d)) (↑(X.residueField x)))) :=
    (e.inv ⁻¹ᵁ U).carrier
  have hopen : IsOpen W := U.2.preimage e.inv.continuous
  have he : ∀ z, e.inv.base (e.hom.base z) = z := fun z => by simp [e]
  have hnonemptyW : W.Nonempty := by
    obtain ⟨z, hz⟩ := hnonempty
    exact ⟨e.hom.base z, by change e.inv.base (e.hom.base z) ∈ U; rwa [he]⟩
  have hWinv : ∀ (i j : Fin d) (hij : i ≠ j) (r : ℕ),
      PrimeSpectrum.comap
        (coordinateShearULift (R := ↑(X.residueField x)) i j hij r).toRingHom ⁻¹' W = W :=
    affineSpace_fiber_largestOpen_specIso_shear_invariant B S hS P f x d
  have hfrobW : 0 < ringChar (X.residueField x) → PrimeSpectrum.comap
      (MvPolynomial.aeval (R := ↑(X.residueField x))
        (fun i : ULift.{u} (Fin d) => MvPolynomial.X i -
          MvPolynomial.X i ^ ringChar (X.residueField x))).toRingHom ⁻¹' W = W := by
    intro hchar
    exact congrArg SetLike.coe (preimage_preimage_eq_of_comm _ _ _ U
      (affineSpace_specIso_inv_sub_pow (X.residueField x) (ULift.{u} (Fin d))
        (ringChar (X.residueField x))) fun z => SetLike.ext_iff.mp (hfrob hchar) _)
  have hfull := affineOpen_eq_univ_of_shear_and_sub_pow_invariant_ulift
    d hd W hopen hnonemptyW hWinv hfrobW
  apply top_unique
  intro z _
  have hz : e.hom.base z ∈ W := by rw [hfull]; trivial
  change e.inv.base (e.hom.base z) ∈ U at hz
  rwa [he] at hz

/-- If the endomorphism with coordinates `xᵢ - xᵢ ^ p` is étale at a point of affine space
and at its image, it does not change membership in the largest open locus. -/
private lemma largestOpen_mem_iff_of_subPow_etaleAt
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y) {n :
      Type u} [Finite n]
    (p : ℕ) (x : AffineSpace n X)
    (hx : EtaleAt (affineSpaceSubPow p) x)
    (hfx : EtaleAt (affineSpaceSubPow p)
      ((AffineSpace.map n f).base x)) :
    (affineSpaceSubPow p).base x ∈
        relativeLargestOpen B S hS P (AffineSpace.map n f) ↔
      x ∈ relativeLargestOpen B S hS P (AffineSpace.map n f) :=
  mem_relativeLargestOpen_etaleAt B S hS P
    (AffineSpace.map n f) (AffineSpace.map n f)
    (affineSpaceSubPow p) (affineSpaceSubPow p)
    (affineSpace_map_comm_subPow f p).symm x hx hfx

/-- The fibre of the largest open locus over a point is invariant under the endomorphism
with coordinates `xᵢ - xᵢ ^ p` as soon as the latter is étale along the two fibres
involved. -/
private lemma affineSpace_fiber_largestOpen_subPow_preimage
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] {n : Type u}
      [Finite n]
    (f : X ⟶ Y) (x : X) (p : ℕ)
    (htarget : ∀ z : AffineSpace n X,
      (AffineSpace n X ↘ X).base z = x →
        EtaleAt (affineSpaceSubPow p) z)
    (htargetY : ∀ z : AffineSpace n Y,
      (AffineSpace n Y ↘ Y).base z = f.base x →
        EtaleAt (affineSpaceSubPow p) z) :
    affineSpaceSubPow p ⁻¹ᵁ affineSpace_fiber_largestOpen (n := n) B S hS P f x =
      affineSpace_fiber_largestOpen (n := n) B S hS P f x := by
  refine preimage_preimage_eq_of_comm _ _ _ _
    (affineSpace_map_comm_subPow (n := n) (X.fromSpecResidueField x) p).symm fun z => ?_
  have hzx : (AffineSpace n X ↘ X).base (AffineSpace.map n (X.fromSpecResidueField x) z) = x :=
    (affineSpace_over_map_apply _ z).trans
      (Scheme.fromSpecResidueField_apply x _)
  exact largestOpen_mem_iff_of_subPow_etaleAt B S hS P f p _
    (htarget _ hzx)
    (htargetY _ ((affineSpace_over_map_apply f _).trans (congrArg f.base hzx)))

/-- For `d ≥ 2`, a nonempty fibre of the largest open locus over a point of the base is all
of affine space over the residue field of that point. -/
private lemma affineSpace_fiber_largestOpen_eq_top
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y)
    (x : X) (d : ℕ) (hd : 2 ≤ d)
    (hnonempty : Nonempty (affineSpace_fiber_largestOpen
      (n := ULift.{u} (Fin d)) B S hS P f x)) :
    affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) B S hS P f x = ⊤ := by
  apply affineSpace_fiber_largestOpen_eq_top_of_sub_pow_invariant B S hS P f x d hd hnonempty
  intro hchar
  apply affineSpace_fiber_largestOpen_subPow_preimage B S hS P f x
  · intro z hz
    apply affineSpace_subPow_etaleAt
    rw [hz]
    exact CharP.cast_eq_zero _ _
  · intro z hz
    apply affineSpace_subPow_etaleAt
    rw [hz]
    apply (f.residueFieldMap x).hom.injective
    simp

/-- For `d ≥ 2`, the largest open locus of the induced morphism of affine spaces contains the
whole fibre of each of its points. -/
private lemma affineSpace_largestOpen_saturated
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y)
    (d : ℕ) (hd : 2 ≤ d)
    (z w : AffineSpace (ULift.{u} (Fin d)) X)
    (he : (AffineSpace (ULift.{u} (Fin d)) X ↘ X) z =
      (AffineSpace (ULift.{u} (Fin d)) X ↘ X) w)
    (hz : z ∈ relativeLargestOpen B S hS P (AffineSpace.map (ULift.{u} (Fin d)) f)) :
    w ∈ relativeLargestOpen B S hS P (AffineSpace.map (ULift.{u} (Fin d)) f) := by
  let x := (AffineSpace (ULift.{u} (Fin d)) X ↘ X) w
  have hzlift := affineSpace_exists_fiber_point z
  rw [he] at hzlift
  obtain ⟨z', hz'⟩ := hzlift
  obtain ⟨w', hw'⟩ := affineSpace_exists_fiber_point w
  have hn : Nonempty (affineSpace_fiber_largestOpen
      (n := ULift.{u} (Fin d)) B S hS P f x) := by
    refine ⟨z', ?_⟩
    show (AffineSpace.map _ (X.fromSpecResidueField x)) z' ∈
      relativeLargestOpen B S hS P (AffineSpace.map _ f)
    rwa [hz']
  have ht := affineSpace_fiber_largestOpen_eq_top B S hS P f x d hd hn
  have hw : w' ∈ affineSpace_fiber_largestOpen
      (n := ULift.{u} (Fin d)) B S hS P f x := ht.ge trivial
  change (AffineSpace.map _ (X.fromSpecResidueField x)) w' ∈
    relativeLargestOpen B S hS P (AffineSpace.map _ f) at hw
  rwa [hw'] at hw

/-- For `d ≥ 2`, the image in `X` of the largest open locus of the induced morphism of affine
`d`-spaces lies in the largest open locus of the original morphism. -/
private lemma mem_largestOpen_of_affineSpace
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y)
    (d : ℕ) (hd : 2 ≤ d)
    (z : AffineSpace (ULift.{u} (Fin d)) X)
    (hz : z ∈ relativeLargestOpen B S hS P (AffineSpace.map (ULift.{u} (Fin d)) f)) :
    (AffineSpace (ULift.{u} (Fin d)) X ↘ X) z ∈ relativeLargestOpen B S hS P f := by
  let n := ULift.{u} (Fin d)
  let W := relativeLargestOpen B S hS P (AffineSpace.map n f)
  let q := (AffineSpace n X ↘ X)
  let U : X.Opens := ⟨q '' (W : Set (AffineSpace n X)),
    AffineSpace.isOpenMap_over (n := n) X W W.isOpen⟩
  apply (mem_relativeLargestOpen B S hS P f (q z)).mpr
  refine ⟨U, ⟨z, hz, rfl⟩, ?_⟩
  have : Smooth (AffineSpace n Y ↘ Y) := affineSpace_smooth_over
  apply of_smooth_surjective_isPullback B S hS P (AffineSpace.isPullback_map (n := n) (U.ι ≫
    f)).flip
  have : Etale (AffineSpace.map n U.ι) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (AffineSpace.isPullback_map (n := n) U.ι).flip inferInstance
  have hall : relativeLargestOpen B S hS P (AffineSpace.map n (U.ι ≫ f)) = ⊤ := by
    apply top_unique
    intro w _
    rw [AffineSpace.map_comp, ← preimage_relativeLargestOpen_etale B S hS P]
    show (AffineSpace.map n U.ι) w ∈ W
    have hw : q ((AffineSpace.map n U.ι) w) ∈ U := by
      rw [show q ((AffineSpace.map n U.ι) w) = U.ι ((AffineSpace n U.toScheme ↘ U.toScheme) w)
        from affineSpace_over_map_apply U.ι w]
      exact ((AffineSpace n U.toScheme ↘ U.toScheme) w).property
    obtain ⟨v, hv, he⟩ := hw
    exact affineSpace_largestOpen_saturated B S hS P
       f d hd v
      ((AffineSpace.map n U.ι) w) he hv
  have hp := (relativeLargestOpen_isGreatest B S hS P
    (AffineSpace.map n (U.ι ≫ f))).1
  rw [hall] at hp
  change relativeProperty B S hS P ((AffineSpace n U.toScheme).topIso.hom ≫ AffineSpace.map n
    (U.ι ≫ f)) at hp
  exact (relative_cancel_left_iso B S hS P (AffineSpace n U.toScheme).topIso.hom _).mp hp

/-- For every `d`, the image in `X` of the largest open locus of the induced morphism of
affine `d`-spaces lies in the largest open locus of the original morphism. -/
private lemma mem_largestOpen_of_affineSpace_any
    {X Y : Scheme.{u}} [Y.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y) (d : ℕ)
    (z : AffineSpace (ULift.{u} (Fin d)) X)
    (hz : z ∈ relativeLargestOpen B S hS P (AffineSpace.map (ULift.{u} (Fin d)) f)) :
    (AffineSpace (ULift.{u} (Fin d)) X ↘ X) z ∈ relativeLargestOpen B S hS P f := by
  let i := fun i : ULift.{u} (Fin d) => (ULift.up (Fin.castAdd 2 i.down) : ULift.{u} (Fin (d + 2)))
  let qX := AffineSpace.reindex i X
  let qY := AffineSpace.reindex i Y
  have : Smooth qY := by
    rw [show qY = (affineSpaceAddTwoIso d Y).hom ≫
      (AffineSpace (ULift.{u} (Fin 2)) (AffineSpace (ULift.{u} (Fin d)) Y) ↘
        AffineSpace (ULift.{u} (Fin d)) Y) from (affineSpaceAddTwoIso_hom_over d Y).symm]
    have : Smooth (AffineSpace (ULift.{u} (Fin 2))
      (AffineSpace (ULift.{u} (Fin d)) Y) ↘ AffineSpace (ULift.{u} (Fin d)) Y) :=
        affineSpace_smooth_over
    infer_instance
  have : Surjective qX := by
    rw [show qX = (affineSpaceAddTwoIso d X).hom ≫
      (AffineSpace (ULift.{u} (Fin 2)) (AffineSpace (ULift.{u} (Fin d)) X) ↘
        AffineSpace (ULift.{u} (Fin d)) X) from (affineSpaceAddTwoIso_hom_over d X).symm]
    infer_instance
  have h : IsPullback qX (AffineSpace.map (ULift.{u} (Fin (d + 2))) f)
      (AffineSpace.map (ULift.{u} (Fin d)) f) qY := by
    apply IsPullback.of_right _ (AffineSpace.map_reindex i f).symm
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) f).flip
    simpa [qX, qY] using
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin (d + 2))) f).flip
  obtain ⟨w, hw⟩ := qX.surjective z
  have hwW : w ∈ relativeLargestOpen B S hS P
      (AffineSpace.map (ULift.{u} (Fin (d + 2))) f) :=
    preimage_largestOpen_le_of_smooth_isPullback B S hS P h (by simpa [hw] using hz)
  have hm := mem_largestOpen_of_affineSpace B S hS P f (d + 2) (by omega) w hwW
  have he : (AffineSpace (ULift.{u} (Fin (d + 2))) X ↘ X) w =
      (AffineSpace (ULift.{u} (Fin d)) X ↘ X) z := by
    rw [← AffineSpace.reindex_over i X]
    show (AffineSpace (ULift.{u} (Fin d)) X ↘ X) (qX w) = _
    rw [hw]
  rwa [he] at hm

/-- In a cartesian square whose base morphism is smooth at the relevant point, a point whose
image lies in the largest open locus downstairs lies in the largest open locus upstairs. -/
private lemma mem_largestOpen_of_smoothAt_isPullback
    {X' X Y' Y : Scheme.{u}} [Y'.Over S] [Y.Over S] [Fact (B.Contains X')] [Fact (B.Contains X)]
      [Fact (B.Contains Y')] [Fact (B.Contains Y)] {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [g.IsOver S] (h : IsPullback a b f g)
    (z : X') (hg : InfinitesimalLifting.SmoothAt g (b z))
    (hz : a z ∈ relativeLargestOpen B S hS P f) : z ∈ relativeLargestOpen B S hS P b := by
  obtain ⟨V, hzV, hV⟩ := smoothAt_has_smooth_open_neighborhood g (b z) hg
  have : Smooth (V.ι ≫ g) := hV
  let zV : (b ⁻¹ᵁ V).toScheme := ⟨z, hzV⟩
  have hp := ((isPullback_morphismRestrict b V).paste_vert h.flip).flip
  have hz' : zV ∈ relativeLargestOpen B S hS P (b ∣_ V) :=
    preimage_largestOpen_le_of_smooth_isPullback B S hS P hp hz
  exact (mem_relativeLargestOpen_etaleAt B S hS P
    b (b ∣_ V) V.ι (b ⁻¹ᵁ V).ι (by simp) zV
    ((etale_iff_forall_etaleAt _).mp inferInstance zV)
    ((etale_iff_forall_etaleAt _).mp inferInstance
      ((b ∣_ V) zV))).mpr hz'

/-- Membership in the largest open locus is unchanged by a comparison morphism to the fibre
product which is étale at the given point. -/
lemma mem_largestOpen_iff_of_comparison_etaleAt
    {X' X Y' Y : Scheme.{u}} [Y'.Over S] [Y.Over S] [Fact (B.Contains X')] [Fact (B.Contains X)]
      [Fact (B.Contains Y')] [Fact (B.Contains Y)]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [g.IsOver S] (g' : X' ⟶ X)
    (hcomm : g' ≫ f = f' ≫ g) (x' : X')
    (hg' : EtaleAt
      (pullback.lift g' f' hcomm) x') :
    (pullback.lift g' f' hcomm).base x' ∈
        relativeLargestOpen B S hS P (pullback.snd f g) ↔
      x' ∈ relativeLargestOpen B S hS P f' := by
  have h := mem_relativeLargestOpen_etaleAt B S hS P
    (pullback.snd f g) f' (𝟙 Y') (pullback.lift g' f' hcomm)
    (by simp only [Category.comp_id, pullback.lift_snd]) x'
    hg'
    ((etale_iff_forall_etaleAt (𝟙 Y')).mp
      (inferInstance : Etale (𝟙 Y')) (f'.base x'))
  simpa only [Category.id_comp] using h

/-- A morphism over `S` which is smooth at a point is, on an open neighbourhood of that point,
the composite of an étale morphism over `S` to a relative affine space with its projection. -/
private lemma exists_etale_affineSpace_isOver_of_smoothAt
    {Y Y' : Scheme.{u}} [Y.Over S] [Y'.Over S] (g : Y' ⟶ Y) [g.IsOver S] (y : Y')
    (hg : InfinitesimalLifting.SmoothAt g y) :
    ∃ (d : ℕ) (U : Y'.Opens) (_ : y ∈ U)
      (π' : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) Y), Etale π' ∧
        π' ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = U.ι ≫ g ∧ π'.IsOver S := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g y)) isOpen_univ
  let VY : Y.Opens := V
  obtain ⟨d, U, hU, hzU, hUV, π, hπ, hπover⟩ :=
    AlgebraicGeometry.exists_affine_open_etale_affineSpace g y VY hV (by simpa using hyV) hg
  let n := ULift.{u} (Fin d)
  have : Etale π := hπ
  have : Etale (AffineSpace.map n VY.ι) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (AffineSpace.isPullback_map (n := n) VY.ι).flip inferInstance
  let π' := π ≫ AffineSpace.map n VY.ι
  have : Etale π' := by
    dsimp [π']
    infer_instance
  have hπ' : π' ≫ (AffineSpace n Y ↘ Y) = U.ι ≫ g := by
    dsimp [π']
    rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, hπover]
    exact Scheme.Hom.resLE_comp_ι g hUV
  have : π'.IsOver S := ⟨by
    show π' ≫ ((AffineSpace n Y ↘ Y) ≫ Y ↘ S) = U.ι ≫ Y' ↘ S
    rw [← Category.assoc, hπ', Category.assoc, comp_over]⟩
  exact ⟨d, U, hzU, π', inferInstance, hπ', inferInstance⟩

/-- A point of the fibre product lies over the largest open locus of `f` as soon as it lies in
the largest open locus of the second projection and `g` is smooth at its image. -/
private lemma mem_largestOpen_of_mem_largestOpen_pullback_snd
    {X Y Y' : Scheme.{u}} [Y.Over S] [Y'.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)]
      [Fact (B.Contains Y')] (f : X ⟶ Y) (g : Y' ⟶ Y) [g.IsOver S]
    (z : (pullback f g : Scheme.{u}))
    (hg : InfinitesimalLifting.SmoothAt g
      ((pullback.snd f g).base z))
    (hz : z ∈ relativeLargestOpen B S hS P (pullback.snd f g)) :
    (pullback.fst f g).base z ∈ relativeLargestOpen B S hS P f := by
  let a := pullback.fst f g
  let b := pullback.snd f g
  obtain ⟨d, U, hzU, π', _, hπ', _⟩ := exists_etale_affineSpace_isOver_of_smoothAt S g (b z) hg
  let n := ULift.{u} (Fin d)
  let j := (b ⁻¹ᵁ U).ι
  let c := b ∣_ U
  let zU : (b ⁻¹ᵁ U).toScheme := ⟨z, hzU⟩
  have hzUW : zU ∈ relativeLargestOpen B S hS P c :=
    preimage_largestOpen_le_of_smooth_isPullback B S hS P
      (isPullback_morphismRestrict b U).flip hz
  have hbc : IsPullback (j ≫ a) c f (U.ι ≫ g) :=
    ((isPullback_morphismRestrict b U).paste_vert
      (IsPullback.of_hasPullback f g).flip).flip
  let hA := (AffineSpace.isPullback_map (n := n) f).flip
  have hc : (j ≫ a) ≫ f = (c ≫ π') ≫ (AffineSpace n Y ↘ Y) := by
    rw [Category.assoc c π', hπ']
    exact hbc.w
  let r := hA.lift (j ≫ a) (c ≫ π') hc
  have hr₁ : r ≫ (AffineSpace n X ↘ X) = j ≫ a := hA.lift_fst _ _ _
  have hr₂ : r ≫ AffineSpace.map n f = c ≫ π' := hA.lift_snd _ _ _
  have houter : IsPullback c (r ≫ (AffineSpace n X ↘ X))
      (π' ≫ (AffineSpace n Y ↘ Y)) f := by
    rw [hr₁, hπ']
    exact hbc.flip
  have hsmall : IsPullback r c (AffineSpace.map n f) π' :=
    (houter.of_bot hr₂.symm hA.flip).flip
  have : Etale r := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsmall.flip
    inferInstance
  have hrW : r zU ∈ relativeLargestOpen B S hS P (AffineSpace.map n f) :=
    (mem_relativeLargestOpen_etaleAt B S hS P
      (AffineSpace.map n f) c π' r hr₂ zU
      ((etale_iff_forall_etaleAt r).mp inferInstance zU)
      ((etale_iff_forall_etaleAt π').mp inferInstance (c zU))).mpr hzUW
  have hx := mem_largestOpen_of_affineSpace_any B S hS P f d (r zU) hrW
  have he : (AffineSpace n X ↘ X) (r zU) = a z :=
    congrArg (fun k => k zU) hr₁
  rwa [he] at hx

/-- For the cartesian square attached to `f` and `g`, the two source points lie in their
largest open loci simultaneously as soon as `g` is smooth at the image point. -/
lemma mem_largestOpen_iff_of_smooth_pullback
    {X Y Y' : Scheme.{u}} [Y.Over S] [Y'.Over S] [Fact (B.Contains X)] [Fact (B.Contains Y)]
      [Fact (B.Contains Y')] (f : X ⟶ Y) (g : Y' ⟶ Y) [g.IsOver S]
    (z : (pullback f g : Scheme.{u}))
    (hg : InfinitesimalLifting.SmoothAt g
      ((pullback.snd f g).base z)) :
    (pullback.fst f g).base z ∈ relativeLargestOpen B S hS P f ↔
      z ∈ relativeLargestOpen B S hS P (pullback.snd f g) :=
  ⟨mem_largestOpen_of_smoothAt_isPullback B S hS P (IsPullback.of_hasPullback f g) z hg,
    mem_largestOpen_of_mem_largestOpen_pullback_snd B S hS P f g z hg⟩

end RelativeSmoothLocus

end AlgebraicGeometry

end
