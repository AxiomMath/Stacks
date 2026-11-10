module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.FibreSeparation.Basic

/-!
# Testing universal closedness by affine-space base changes

For a quasi-compact morphism of schemes `f : X ⟶ S`, universal closedness is equivalent to
closedness of every base change along a morphism locally of finite presentation, and also to
closedness of the finitely many extra affine coordinates: `𝔸(n; X) ⟶ 𝔸(n; S)` closed for all
`n : ℕ`.  This is Stacks 05JX, and this file proves it with no hypothesis on `f` beyond
quasi-compactness — in particular no affineness.

The two nontrivial implications run in opposite directions and use disjoint machinery.

* (2) ⇒ (1) upgrades "closed after every base change locally of finite presentation" to "closed
  after every base change", by the specialization criterion: a closed point-pair that fails to
  specialize is separated by a closed subscheme avoiding a fibre, and
  `FibreSeparation/Basic.lean`'s Stacks 05BD pushes that separation down to a base locally of
  finite presentation, where the hypothesis applies.  This is the only place the approximation
  enters.
* (3) ⇒ (2) is Zariski bookkeeping with no approximation: over affine opens `V ⊆ S` and
  `U ⊆ S'` with `U ⊆ g⁻¹ V`, a morphism locally of finite presentation of affine schemes
  presents its source as a closed subscheme of a finite-dimensional affine space over `V`, so
  the base change along it is cut out of the base change along `𝔸(n; S) ↘ S`, which is closed
  by hypothesis.

## Main results

* `universallyClosed_of_forall_isClosedMap_affineSpaceMap`: the implication (3) ⇒ (1) on its
  own, which is the form the Nagata equivalence of tag 0GWV consumes.
* `baseChange_closed_of_lfp_closed`: the (2) ⇒ (1) upgrade, stated for a single base change.
* `exists_closedImmersion_affineSpace_of_lfp`: a morphism locally of finite presentation of
  affine schemes closed-immerses into a finite-dimensional affine space over its target.

## Implementation notes

A base change along `g : S' ⟶ S` is represented by `pullback.snd f g`, and the morphism on
products with affine `n`-space by `AffineSpace.map` indexed by `ULift (Fin n)`, in the same
universe as `f`.

The chain of "a base change along an immersion preserves closedness" lemmas is spelled out
rather than quoted from a single `MorphismProperty` instance, because the property being
transported is `IsClosedMap` of the *other* projection, which is not stable under base change;
what makes each step work is that the morphism being pulled back along is an immersion.

## References

* [Stacks Project, Tag 05JX](https://stacks.math.columbia.edu/tag/05JX)
* [Stacks Project, Tag 05BD](https://stacks.math.columbia.edu/tag/05BD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.Tag05JXGeneral

/-! ### (2) ⇒ (1): from finitely presented base changes to all base changes -/

/-- If every base change of a quasi-compact `f` along a morphism locally of finite presentation
is closed, then *every* base change of `f` is closed.

The proof is by the specialization criterion.  A specialization `x ⤳ y` downstairs with no lift
exhibits the closure of `{x}` as a closed subscheme of `X ×_S T` missing the fibre over `y`;
Stacks 05BD separates it from that fibre over a base locally of finite presentation, where the
hypothesis makes the image closed, and closedness contradicts the missing lift. -/
theorem baseChange_closed_of_lfp_closed {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f]
    (h : ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
      LocallyOfFinitePresentation g → IsClosedMap (pullback.snd f g))
    {T : Scheme.{u}} (g : T ⟶ S) : IsClosedMap (pullback.snd f g) := by
  let q := pullback.snd f g
  have : QuasiCompact q := by
    dsimp [q]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f g) inferInstance
  apply (isClosedMap_iff_specializingMap q).2
  intro x y hxy
  by_contra hno
  change ¬ ∃ x' : ↑(pullback f g), x ⤳ x' ∧ q x' = y at hno
  let Z : TopologicalSpace.Closeds (↑(pullback f g)) :=
    ⟨closure ({x} : Set ↑(pullback f g)), isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hy : y ∉ Set.image q (I.support : Set ↑(pullback f g)) := by
    rintro ⟨z, hzI, hz⟩
    have hxz : x ⤳ z := (specializes_iff_mem_closure).2 hzI
    exact hno ⟨z, hxz, hz⟩
  obtain ⟨V, hyV, T', _, b, hb, a, hab, I', p, q', hp₁, hp₂, hq₁, hq₂,
      ha, hle⟩ :=
    exists_affine_locallyFinitePresentation_separation f g y I hy
  have hqxV : q x ∈ V.1 := hxy.mem_open V.1.2 hyV
  let specx := (pullback f g).fromSpecResidueField x
  have hspecRange : Set.range (specx ≫ q) ⊆ Set.range V.1.ι := by
    rintro z ⟨w, rfl⟩
    refine ⟨⟨q x, hqxV⟩, ?_⟩
    simp [specx]
  let d := IsOpenImmersion.lift V.1.ι (specx ≫ q) hspecRange
  have hd : d ≫ V.1.ι = specx ≫ q := IsOpenImmersion.lift_fac _ _ _
  let m : Spec ((pullback f g).residueField x) ⟶ pullback f (V.1.ι ≫ g) :=
    pullback.lift (specx ≫ pullback.fst f g) d (by
      calc
        (specx ≫ pullback.fst f g) ≫ f = specx ≫ (pullback.fst f g ≫ f) := by simp
        _ = specx ≫ (pullback.snd f g ≫ g) := by rw [pullback.condition]
        _ = (specx ≫ q) ≫ g := by simp [q, Category.assoc]
        _ = (d ≫ V.1.ι) ≫ g := by rw [hd]
        _ = d ≫ (V.1.ι ≫ g) := by simp)
  have hmp : m ≫ p = specx := by
    apply (IsPullback.of_hasPullback f g).hom_ext
    · calc
        (m ≫ p) ≫ pullback.fst f g = m ≫ (p ≫ pullback.fst f g) := by simp
        _ = m ≫ pullback.fst f (V.1.ι ≫ g) := by rw [hp₁]
        _ = specx ≫ pullback.fst f g := by
          dsimp [m]
          simp only [pullback.lift_fst]
    · calc
        (m ≫ p) ≫ pullback.snd f g = m ≫ (p ≫ pullback.snd f g) := by simp
        _ = m ≫ (pullback.snd f (V.1.ι ≫ g) ≫ V.1.ι) := by rw [hp₂]
        _ = d ≫ V.1.ι := by
          rw [← Category.assoc]
          dsimp [m]
          simp only [pullback.lift_snd]
        _ = specx ≫ q := hd
  let xV := m (genericPoint (Spec ((pullback f g).residueField x)))
  have hpx : p xV = x := by
    change (m ≫ p) (genericPoint (Spec ((pullback f g).residueField x))) = x
    rw [hmp, Scheme.fromSpecResidueField_apply]
  have hmsnd : m ≫ pullback.snd f (V.1.ι ≫ g) = d := by
    dsimp [m]
    exact pullback.lift_snd _ _ _
  have hlocal : (pullback.snd f (V.1.ι ≫ g)) xV = ⟨q x, hqxV⟩ := by
    apply Subtype.ext
    change V.1.ι ((pullback.snd f (V.1.ι ≫ g)) xV) = q x
    calc
      V.1.ι ((pullback.snd f (V.1.ι ≫ g)) xV) =
          ((m ≫ pullback.snd f (V.1.ι ≫ g)) ≫ V.1.ι)
            (genericPoint (Spec ((pullback f g).residueField x))) := by
            simp only [xV, Scheme.Hom.comp_apply]
      _ = (d ≫ V.1.ι) (genericPoint (Spec ((pullback f g).residueField x))) := by rw [hmsnd]
      _ = (specx ≫ q) (genericPoint (Spec ((pullback f g).residueField x))) := by rw [hd]
      _ = q x := by
        rw [Scheme.Hom.comp_apply]
        exact congrArg q (Scheme.fromSpecResidueField_apply _ _)
  have hxSupport : p xV ∈ I.support := by
    rw [hpx]
    change x ∈ ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set ↑(pullback f g))
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact subset_closure (Set.mem_singleton x)
  have hxq : q' xV ∈ I'.support := by
    have hxcomp : xV ∈ (I.comap p).support := by
      rw [Scheme.IdealSheafData.support_comap]
      exact hxSupport
    have hsupport : (I.comap p).support ≤ (I'.comap q').support :=
      (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal).2 <| by
        calc
          I'.comap q' ≤ I.comap p := hle
          _ ≤ Scheme.IdealSheafData.vanishingIdeal (I.comap p).support :=
            (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal).mp le_rfl
    have : xV ∈ (I'.comap q').support := hsupport hxcomp
    rw [Scheme.IdealSheafData.support_comap] at this
    change q' xV ∈ I'.support at this
    exact this
  have himage : a ⟨q x, hqxV⟩ ∈
      Set.image (pullback.snd f b) (I'.support : Set ↑(pullback f b)) := by
    refine ⟨q' xV, hxq, ?_⟩
    have hp := congrArg (fun k => k xV) hq₂
    simpa [Category.assoc, hlocal] using hp
  have hclosed_image : IsClosed (Set.image (pullback.snd f b) (I'.support : Set ↑(pullback f b))) :=
    h T' b hb _ I'.support.isClosed
  have hspec : a ⟨q x, hqxV⟩ ⤳ a ⟨y, hyV⟩ :=
    ((subtype_specializes_iff ⟨q x, hqxV⟩ ⟨y, hyV⟩).2 hxy).map a.continuous
  have hpoint : a ⟨y, hyV⟩ ∈ Set.image (pullback.snd f b) (I'.support : Set ↑(pullback f b)) :=
    hclosed_image.stableUnderSpecialization hspec himage
  exact ha hpoint

/-! ### Base change along an immersion preserves closedness -/

/-- A base change along a closed immersion carries a closed map to a closed map.  (Unlike an
arbitrary base change, which is exactly what universal closedness is about.) -/
theorem isClosedMap_pullback_of_closedImmersion
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsClosedImmersion g] (hf : IsClosedMap f) :
    IsClosedMap (pullback.snd f g) := by
  let p := pullback.fst f g
  let q := pullback.snd f g
  have : IsClosedImmersion p := inferInstance
  intro C hC
  apply g.isClosedEmbedding.isClosed_iff_image_isClosed.mpr
  have hfun : (fun x => g (q x)) = fun x => f (p x) := by
    funext x
    exact congrArg (fun k : pullback f g ⟶ Z => k x) pullback.condition.symm
  rw [Set.image_image, hfun, ← Set.image_image]
  exact hf _ (p.isClosedEmbedding.isClosedMap C hC)

/-- The restriction of a closed map to an open of the target is a closed map. -/
theorem isClosedMap_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (hf : IsClosedMap f) :
    IsClosedMap (f ∣_ U) := by
  rw [morphismRestrict_base]
  exact hf.restrictPreimage U.1

/-- A base change along the inclusion of an open carries a closed map to a closed map. -/
theorem isClosedMap_pullback_of_openImmersion_inclusion
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (hf : IsClosedMap f) :
    IsClosedMap (pullback.snd f U.ι) := by
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f U]
  exact (isClosedMap_morphismRestrict f U hf).comp (Scheme.Hom.isClosedMap _)

/-- A base change along an open immersion carries a closed map to a closed map. -/
theorem isClosedMap_pullback_of_openImmersion
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion g] (hf : IsClosedMap f) :
    IsClosedMap (pullback.snd f g) := by
  let V := g.opensRange
  let e : Y ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq g V.ι (by simp [V])
  have hfac : e.hom ≫ V.ι = g :=
    IsOpenImmersion.isoOfRangeEq_hom_fac g V.ι (by simp [V])
  have hpaste : IsPullback
      (pullback.snd f g ≫ e.hom) (pullback.fst f g) V.ι f := by
    have hIso : IsPullback e.hom g V.ι (𝟙 Z) :=
      IsPullback.of_horiz_isIso ⟨by rw [hfac]; simp⟩
    exact (IsPullback.of_hasPullback f g).flip.paste_horiz hIso
  let hcan : IsPullback (pullback.snd f V.ι) (pullback.fst f V.ι) V.ι f :=
    (IsPullback.of_hasPullback f V.ι).flip
  have hcustom : IsClosedMap (pullback.snd f g ≫ e.hom) := by
    rw [← hpaste.isoIsPullback_hom_fst _ _ hcan]
    exact (isClosedMap_pullback_of_openImmersion_inclusion f V hf).comp
      (Scheme.Hom.isClosedMap _)
  convert e.inv.isClosedMap.comp hcustom using 1
  funext x
  simp

/-- Closedness of a map transfers along an isomorphism of sources compatible with the maps. -/
private theorem isClosedMap_of_inv_comp_eq {A B C : Scheme.{u}} (e : A ≅ B) (a : A ⟶ C)
    (b : B ⟶ C) (h : e.inv ≫ a = b) (ha : IsClosedMap a) : IsClosedMap b := by
  rw [← h]
  exact ha.comp (Scheme.Hom.isClosedMap e.inv)

/-- Closedness of base changes composes: a base change along `h ≫ g` is a base change along `h`
of a base change along `g`. -/
theorem isClosedMap_pullback_comp
    {X Y Z W : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Y)
    (hh : IsClosedMap (pullback.snd (pullback.snd f g) h)) :
    IsClosedMap (pullback.snd f (h ≫ g)) := by
  exact isClosedMap_of_inv_comp_eq (pullbackLeftPullbackSndIso f g h) _ _
    (pullbackLeftPullbackSndIso_inv_snd_snd f g h) hh

/-- A base change along an immersion carries a closed map to a closed map, by factoring the
immersion as a closed immersion followed by an open immersion. -/
theorem isClosedMap_pullback_of_immersion
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsImmersion g] (hf : IsClosedMap f) :
    IsClosedMap (pullback.snd f g) := by
  obtain ⟨W, g₁, g₂, hg₁, hg₂, rfl⟩ :=
    (IsImmersion.isImmersion_iff_exists (f := g)).mp inferInstance
  let : IsClosedImmersion g₁ := hg₁
  let : IsOpenImmersion g₂ := hg₂
  have h₁ := isClosedMap_pullback_of_openImmersion f g₂ hf
  have h₂ := isClosedMap_pullback_of_closedImmersion (pullback.snd f g₂) g₁ h₁
  exact isClosedMap_pullback_comp f g₂ g₁ h₂

/-! ### (3) ⇒ (2): from affine-space base changes to finitely presented base changes -/

/-- If `g : T ⟶ S` factors as an immersion into `𝔸(n; S)` followed by the projection, then the
base change of `f` along `g` is closed as soon as `𝔸(n; X) ⟶ 𝔸(n; S)` is. -/
theorem isClosedMap_pullback_of_affineSpaceImmersion
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (n : ℕ)
    (i : T ⟶ AffineSpace (ULift.{u} (Fin n)) S) [IsImmersion i]
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = g)
    (hclosed : IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f)) :
    IsClosedMap (pullback.snd f g) := by
  let fₙ := AffineSpace.map (ULift.{u} (Fin n)) f
  let pX := AffineSpace (ULift.{u} (Fin n)) X ↘ X
  let pS := AffineSpace (ULift.{u} (Fin n)) S ↘ S
  have htop : IsPullback (pullback.snd fₙ i) (pullback.fst fₙ i) i fₙ :=
    (IsPullback.of_hasPullback fₙ i).flip
  have hbottom : IsPullback fₙ pX pS f :=
    AffineSpace.isPullback_map f
  have hpaste : IsPullback (pullback.snd fₙ i)
      (pullback.fst fₙ i ≫ pX) g f := by
    rw [← hi]
    exact htop.paste_vert hbottom
  let hcan : IsPullback (pullback.snd f g) (pullback.fst f g) g f :=
    (IsPullback.of_hasPullback f g).flip
  exact isClosedMap_of_inv_comp_eq (hpaste.isoIsPullback _ _ hcan) _ _
    (hpaste.isoIsPullback_inv_fst _ _ hcan) (isClosedMap_pullback_of_immersion fₙ i hclosed)

/-- A morphism locally of finite presentation between affine schemes presents its source as a
closed subscheme of a finite-dimensional affine space over its target.  This is the geometric
form of "a finitely presented algebra is a quotient of a polynomial ring in finitely many
variables"; no approximation of the base is involved. -/
theorem exists_closedImmersion_affineSpace_of_lfp
    {T V : Scheme.{u}} (g : T ⟶ V) [IsAffine T] [IsAffine V]
    [LocallyOfFinitePresentation g] :
    ∃ n : ℕ, ∃ i : T ⟶ AffineSpace (ULift.{u} (Fin n)) V,
      IsClosedImmersion i ∧ i ≫ (AffineSpace (ULift.{u} (Fin n)) V ↘ V) = g := by
  let φ := (g.appTop).hom
  let : Algebra (↑(Γ(V, ⊤))) (↑(Γ(T, ⊤))) := φ.toAlgebra
  have hfp : φ.FinitePresentation := by
    change (g.appTop).hom.FinitePresentation
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]
    exact g.finitePresentation_appLE (isAffineOpen_top V) (isAffineOpen_top T) (by simp)
  have hft : φ.FiniteType := RingHom.FiniteType.of_finitePresentation hfp
  let : Algebra.FiniteType (↑(Γ(V, ⊤))) (↑(Γ(T, ⊤))) := hft
  obtain ⟨n, p, hp⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
      (inferInstance : Algebra.FiniteType (↑(Γ(V, ⊤))) (↑(Γ(T, ⊤))))
  let e : MvPolynomial (Fin n) (↑(Γ(V, ⊤)) ) ≃ₐ[↑(Γ(V, ⊤))]
      MvPolynomial (ULift.{u} (Fin n)) (↑(Γ(V, ⊤)) ) :=
    MvPolynomial.renameEquiv _ (Equiv.ulift.{u, 0} (α := Fin n)).symm
  let p' : MvPolynomial (ULift.{u} (Fin n)) (↑(Γ(V, ⊤))) →ₐ[↑(Γ(V, ⊤))]
      ↑(Γ(T, ⊤)) := p.comp e.symm.toAlgHom
  have hp' : Function.Surjective p' := hp.comp e.symm.surjective
  let R := Γ(V, ⊤)
  let A := Γ(T, ⊤)
  let P := CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) (↑R))
  let η : P ⟶ A := CommRingCat.ofHom p'.toRingHom
  let i : T ⟶ AffineSpace (ULift.{u} (Fin n)) V :=
    T.isoSpec.hom ≫ Spec.map η ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv ≫
      AffineSpace.map (ULift.{u} (Fin n)) V.isoSpec.inv
  let : IsClosedImmersion (Spec.map η) := IsClosedImmersion.spec_of_surjective η hp'
  let : IsIso (AffineSpace.map (ULift.{u} (Fin n)) V.isoSpec.inv) := by
    change IsIso ((AffineSpace.functor.obj (Opposite.op (ULift.{u} (Fin n)))).map V.isoSpec.inv)
    infer_instance
  have hi : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  have hcoeff : CommRingCat.ofHom
      (MvPolynomial.C : (↑R) →+* MvPolynomial (ULift.{u} (Fin n)) (↑R)) ≫ η =
        CommRingCat.ofHom φ := by
    ext r
    exact p'.commutes r
  have hbase : i ≫ AffineSpace (ULift.{u} (Fin n)) V ↘ V = g := by
    dsimp [i]
    calc
      T.isoSpec.hom ≫ Spec.map η ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv ≫
          AffineSpace.map (ULift.{u} (Fin n)) V.isoSpec.inv ≫
            AffineSpace (ULift.{u} (Fin n)) V ↘ V =
        T.isoSpec.hom ≫ Spec.map η ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv ≫
          (AffineSpace (ULift.{u} (Fin n)) (Spec R) ↘ Spec R) ≫ V.isoSpec.inv := by
            simp only [AffineSpace.map_over]
      _ = T.isoSpec.hom ≫ Spec.map η ≫
          ((AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv ≫
            (AffineSpace (ULift.{u} (Fin n)) (Spec R) ↘ Spec R)) ≫ V.isoSpec.inv := by
            simp only [Category.assoc]
      _ = T.isoSpec.hom ≫ Spec.map η ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫
          V.isoSpec.inv := by rw [AffineSpace.SpecIso_inv_over]
      _ = T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C ≫ η) ≫ V.isoSpec.inv := by
            have hs := (Spec.map_comp (CommRingCat.ofHom MvPolynomial.C) η).symm
            simpa only [Category.assoc] using
              congrArg (fun k => T.isoSpec.hom ≫ k ≫ V.isoSpec.inv) hs
      _ = T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ V.isoSpec.inv := by rw [hcoeff]
      _ = g := by
            have hphi : CommRingCat.ofHom φ = g.appTop := by ext; rfl
            rw [hphi]
            change T.toSpecΓ ≫ Spec.map g.appTop ≫ V.isoSpec.inv = g
            calc
              T.toSpecΓ ≫ Spec.map g.appTop ≫ V.isoSpec.inv =
                  (T.toSpecΓ ≫ Spec.map g.appTop) ≫ V.isoSpec.inv := by simp only [Category.assoc]
              _ = (g ≫ V.toSpecΓ) ≫ V.isoSpec.inv := by
                rw [← Scheme.toSpecΓ_naturality g]
              _ = g := by simp [Scheme.isoSpec]
  exact ⟨n, i, hi, hbase⟩

/-- **Stacks Project, Tag 05JX**, implication (3) ⇒ (2): if every finite-dimensional
affine-space base change of `f` is closed, then so is every base change along a morphism
locally of finite presentation.

This half needs no approximation: it is a Zariski reduction to affine opens `V ⊆ S` and
`U ⊆ g⁻¹ V`, over which `g` closed-immerses into a finite-dimensional affine space. -/
theorem isClosedMap_pullbackSnd_of_forall_isClosedMap_affineSpaceMap
    {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f))
    (S' : Scheme.{u}) (g : S' ⟶ S) [LocallyOfFinitePresentation g] :
    IsClosedMap (pullback.snd f g) := by
  let q := pullback.snd f g
  let ι := Σ V : S.affineOpens, {U : S'.affineOpens // U.1 ≤ g ⁻¹ᵁ V.1}
  let W : ι → S'.Opens := fun a => a.2.1.1
  have hcover : iSup W = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨V, hyV⟩ : ∃ V : S.affineOpens, g y ∈ V.1 := by
      have hmem : g y ∈ (⨆ V : S.affineOpens, V.1) := by
        rw [iSup_affineOpens_eq_top]
        exact Set.mem_univ _
      exact TopologicalSpace.Opens.mem_iSup.mp hmem
    have hyPre : y ∈ g ⁻¹ᵁ V.1 := by simpa using hyV
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
      S'.isBasis_affineOpens.exists_subset_of_mem_open hyPre (g ⁻¹ᵁ V.1).2
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨V, ⟨⟨U, hU⟩, hUV⟩⟩, hyU⟩
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := topologically @IsClosedMap) W hcover).2
  intro c
  let V : S.affineOpens := c.1
  let U : S'.affineOpens := c.2.1
  let eUV : U.1 ≤ g ⁻¹ᵁ V.1 := c.2.2
  let gUV := g.resLE V.1 U.1 eUV
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  have : LocallyOfFinitePresentation gUV := inferInstance
  obtain ⟨n, i, hiClosed, hiBase⟩ :=
    exists_closedImmersion_affineSpace_of_lfp gUV
  let m := AffineSpace.map (ULift.{u} (Fin n)) V.1.ι
  have hmPB : IsPullback m
      (AffineSpace (ULift.{u} (Fin n)) V.1 ↘ V.1)
      (AffineSpace (ULift.{u} (Fin n)) S ↘ S) V.1.ι :=
    AffineSpace.isPullback_map V.1.ι
  have : IsOpenImmersion m :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hmPB.flip inferInstance
  let j := i ≫ m
  have : IsImmersion j := inferInstance
  have hj : j ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = U.1.ι ≫ g := by
    calc
      j ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) =
          i ≫ ((AffineSpace (ULift.{u} (Fin n)) V.1 ↘ V.1) ≫ V.1.ι) := by
            simp [j, m, AffineSpace.map_over]
      _ = gUV ≫ V.1.ι := by rw [← Category.assoc, hiBase]
      _ = U.1.ι ≫ g := by
        simp [gUV]
  have hlocal := isClosedMap_pullback_of_affineSpaceImmersion
    f (U.1.ι ≫ g) n j hj (h n)
  let e₁ := pullbackLeftPullbackSndIso f g U.1.ι
  let e₂ := pullbackRestrictIsoRestrict q U.1
  let d := e₁.inv ≫ e₂.hom
  have hd : d ≫ (q ∣_ U.1) = pullback.snd f (U.1.ι ≫ g) := by
    dsimp [d]
    rw [Category.assoc, pullbackRestrictIsoRestrict_hom_morphismRestrict,
      pullbackLeftPullbackSndIso_inv_snd_snd]
  have : IsIso d := by dsimp [d]; infer_instance
  exact isClosedMap_of_inv_comp_eq (asIso d) _ (q ∣_ U.1) (by rw [← hd]; simp) hlocal

/-! ### The theorem -/

/-- **Stacks Project, Tag 05JX**, implication (2) ⇒ (1): a quasi-compact morphism all of whose
base changes along morphisms locally of finite presentation are closed is universally closed.
This is where the Stacks 05BD approximation is consumed, and it is the only place. -/
theorem universallyClosed_of_forall_isClosedMap_pullbackSnd {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f]
    (h : ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
      LocallyOfFinitePresentation g → IsClosedMap (pullback.snd f g)) :
    UniversallyClosed f := by
  refine ⟨fun X' S' i₁ i₂ f' hp ↦ ?_⟩
  rw [← hp.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback f i₂).flip]
  exact (baseChange_closed_of_lfp_closed f h i₂).comp (Scheme.Hom.isClosedMap _)

/-- **Stacks Project, Tag 05JX**, implication (3) ⇒ (1), with no hypothesis on `f` beyond
quasi-compactness: a quasi-compact morphism which stays closed after adjoining finitely many
affine coordinates is universally closed.

This is the implication the Nagata equivalence of tag 0GWV consumes.  It is proved by composing
`isClosedMap_pullbackSnd_of_forall_isClosedMap_affineSpaceMap` (the Zariski half, no
approximation) with `universallyClosed_of_forall_isClosedMap_pullbackSnd` (the Stacks 05BD
half).  In particular `f` is *not* assumed affine. -/
theorem universallyClosed_of_forall_isClosedMap_affineSpaceMap {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] (h : ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f)) :
    UniversallyClosed f :=
  universallyClosed_of_forall_isClosedMap_pullbackSnd f
    fun S' g _ => isClosedMap_pullbackSnd_of_forall_isClosedMap_affineSpaceMap f h S' g

end Stacks.AlgebraicGeometry.Tag05JXGeneral
