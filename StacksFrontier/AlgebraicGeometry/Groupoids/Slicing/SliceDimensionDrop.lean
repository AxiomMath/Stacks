module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.Ideal.Operations
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite
public import StacksFrontier.AlgebraicGeometry.Flatness.EssentialFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.LocalStructure.StalkConormal
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.StabilizerDimension
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SourceFiberIdentity
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionStabilizer
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.ZeroScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
public import StacksFrontier.RingTheory.Flat.RegularSequenceOverBase
public import StacksFrontier.Topology.Dimension.Krull
import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.TangentIdentity
import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.RestrictedArrowStalk
import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.SmoothPullback
import StacksFrontier.RingTheory.CohenMacaulay.SliceDimensionDrop

/-!
# A dimension-reducing slice of a groupoid scheme

Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t` Cohen--Macaulay and locally of
finite presentation, and let `u` be a finite type point of `U`. If the source fibre `F_u` has
larger dimension at the identity arrow than the stabilizer fibre `G_u` has in total, then an
affine locally closed slice through `u`, locally of finite presentation, drops that dimension
by one while keeping the induced morphism `U' ×_{g,U,t} R ⟶ U` Cohen--Macaulay at the identity
arrow.

## Main results

* `AlgebraicGeometry.exists_affine_slice_dim_sub_one` constructs the slice, with all five
  conclusions of the source: the slice is an affine immersion through `u`, it is locally of
  finite presentation, the induced morphism is Cohen--Macaulay at the identity arrow, and the
  restricted source fibre has dimension one less there.

## Implementation notes

The output slice is packaged as an `AlgebraicGeometry.SliceSituation`, so its restricted source
fibre and identity point are the canonical ones of Tag 04MY, and the point at which the induced
morphism is Cohen--Macaulay is characterised by its two pullback projections. The dimension drop
is stated as `dim + 1 = d₂` rather than `dim = d₂ - 1`, which avoids truncated subtraction in
`WithBot ℕ∞`.

The commutative-algebra core is
`IsCohenMacaulayLocalRing.exists_mem_maximalIdeal_isSMulRegular_map_of_ringKrullDim_lt`: in a
Cohen--Macaulay Noetherian local ring, if extending the maximal ideal of a local base drops the
dimension, then some element of that maximal ideal maps to a nonzerodivisor whose quotient drops
the dimension by exactly one. Everything else here is geometry.

Stalk maps are taken at prescribed image points throughout, using
`AlgebraicGeometry.Scheme.Hom.stalkMapAt`. Hypotheses that are classes are passed explicitly
wherever the point they concern is built from the chosen slice, since instance search does not
see through the projections of the slice situation.

## References

* [Stacks Project, Tag 0461](https://stacks.math.columbia.edu/tag/0461)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

open GroupoidScheme

/-- The stalk map at the literal image point is Mathlib's stalk map. -/
private lemma stalkMapAt_self {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.stalkMapAt x (f x) rfl = (f.stalkMap x).hom := by
  change (eqToHom (congrArg Y.presheaf.stalk (rfl : f x = f x).symm) ≫ f.stalkMap x).hom = _
  simp

/-- The stalk map at a prescribed image point, read on an element, is the stalk map applied
after the stalk congruence along the equality of points. -/
private lemma stalkMapAt_apply_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) (b : Y.presheaf.stalk y) :
    f.stalkMapAt x y h b =
      (f.stalkMap x).hom ((Y.presheaf.stalkCongr (.of_eq h.symm)).hom b) := by
  rw [stalkCongr_of_eq Y.presheaf h.symm]
  rfl

/-- **The kernel of the stalk map of the first projection of a fibre product**, for a second
leg that is merely surjective on stalks: it is generated by the image of the kernel of the
stalk map of that second leg. -/
private theorem ker_stalkMap_pullback_fst' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    [SurjectiveOnStalks g] (z : (pullback f g).carrier) :
    RingHom.ker ((pullback.fst f g).stalkMap z).hom =
      Ideal.map (f.stalkMap (pullback.fst f g z)).hom
        (RingHom.ker ((eqToHom (congrArg Y.presheaf.stalk
          (congrArg (fun k : pullback f g ⟶ Y => k z) pullback.condition)) ≫
            g.stalkMap (pullback.snd f g z)).hom)) := by
  let : Algebra (Y.presheaf.stalk ((pullback.fst f g ≫ f) z))
      (X.presheaf.stalk (pullback.fst f g z)) :=
    (f.stalkMap (pullback.fst f g z)).hom.toAlgebra
  let : Algebra (Y.presheaf.stalk ((pullback.fst f g ≫ f) z))
      (Z.presheaf.stalk (pullback.snd f g z)) :=
    ((eqToHom (congrArg Y.presheaf.stalk
      (congrArg (fun k : pullback f g ⟶ Y => k z) pullback.condition))) ≫
    g.stalkMap (pullback.snd f g z)).hom.toAlgebra
  obtain ⟨φ, hφ, _, hloc⟩ := BaseChangeStalk.pullback_stalk_isLocalization f g z
  have : IsLocalHom (φ.comp Algebra.TensorProduct.includeLeftRingHom) := by
    rw [hφ]
    infer_instance
  rw [← hφ]
  refine Algebra.TensorProduct.ker_comp_includeLeftRingHom_of_isLocalization _ _ _ _ φ ?_ hloc
  exact (g.stalkMap_surjective _).comp
    (ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg Y.presheaf.stalk
        (congrArg (fun k : pullback f g ⟶ Y => k z) pullback.condition)))).2

/-- The same kernel computation, phrased with stalk maps at prescribed image points. -/
private lemma ker_stalkMapAt_pullback_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [SurjectiveOnStalks g]
    (p : (pullback f g : Scheme)) (x : X) (y : Y) (z : Z)
    (hx : pullback.fst f g p = x) (hy : pullback.snd f g p = y)
    (hf : f x = z) (hg : g y = z) :
    RingHom.ker ((pullback.fst f g).stalkMapAt p x hx) =
      Ideal.map (f.stalkMapAt x z hf) (RingHom.ker (g.stalkMapAt y z hg)) := by
  subst hx
  subst hy
  subst hf
  rw [stalkMapAt_self, stalkMapAt_self]
  exact ker_stalkMap_pullback_fst' f g p

/-- Precomposing with an isomorphism does not change the kernel of a stalk map. -/
private lemma ker_stalkMapAt_comp_iso {X Y Z : Scheme.{u}} (e : X ≅ Y)
    (f : Y ⟶ Z) (x : X) (y : Y) (z : Z) (hxy : e.hom x = y) (hyz : f y = z)
    (hxz : (e.hom ≫ f) x = z) :
    RingHom.ker ((e.hom ≫ f).stalkMapAt x z hxz) =
      RingHom.ker (f.stalkMapAt y z hyz) := by
  have hcomp : (e.hom ≫ f).stalkMapAt x z hxz =
      (e.hom.stalkMapAt x y hxy).comp (f.stalkMapAt y z hyz) :=
    (Scheme.Hom.stalkMapAt_comp e.hom f x y z hxy hyz).symm
  have hbij : Function.Bijective (e.hom.stalkMapAt x y hxy) := by
    subst hxy
    rw [stalkMapAt_self]
    exact ConcreteCategory.bijective_of_isIso _
  rw [hcomp]
  exact RingHom.ker_comp_of_injective _ hbij.injective

/-- **The kernel of the stalk map of one projection of a pullback square.**  If the opposite
leg is surjective on stalks, the conormal ideal of the projection at a point is generated by
the image of the conormal ideal of that leg. -/
private lemma ker_stalkMapAt_of_isPullback {P X Y Z : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (H : IsPullback a b f g) [SurjectiveOnStalks g]
    (p : P) (x : X) (y : Y) (z : Z)
    (ha : a p = x) (hb : b p = y) (hf : f x = z) (hg : g y = z) :
    RingHom.ker (a.stalkMapAt p x ha) =
      Ideal.map (f.stalkMapAt x z hf) (RingHom.ker (g.stalkMapAt y z hg)) := by
  have hx : pullback.fst f g (H.isoPullback.hom p) = x := by
    rwa [← Scheme.Hom.comp_apply, H.isoPullback_hom_fst]
  have hy : pullback.snd f g (H.isoPullback.hom p) = y := by
    rwa [← Scheme.Hom.comp_apply, H.isoPullback_hom_snd]
  have hxz : (H.isoPullback.hom ≫ pullback.fst f g) p = x := by
    rwa [H.isoPullback_hom_fst]
  have h1 : a.stalkMapAt p x ha =
      (H.isoPullback.hom ≫ pullback.fst f g).stalkMapAt p x hxz :=
    Scheme.Hom.stalkMapAt_congr a _ H.isoPullback_hom_fst.symm p x ha hxz
  rw [h1, ker_stalkMapAt_comp_iso H.isoPullback (pullback.fst f g) p
      (H.isoPullback.hom p) x rfl hx hxz]
  exact ker_stalkMapAt_pullback_fst f g (H.isoPullback.hom p) x y z hx hy hf hg

/-- The quotient of a ring by the kernel of a surjection, identified with the target. -/
private noncomputable def quotientEquivOfSurjectiveOfKer
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal A) (hI : RingHom.ker f = I) :
    A ⧸ I ≃+* B :=
  (Ideal.quotEquivOfEq hI.symm).trans (RingHom.quotientKerEquivOfSurjective hf)

/-- The identification of the quotient with the target sends a class to the image. -/
private lemma quotientEquivOfSurjectiveOfKer_mk
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal A) (hI : RingHom.ker f = I) (a : A) :
    quotientEquivOfSurjectiveOfKer f hf I hI (Ideal.Quotient.mk I a) = f a := by
  simp [quotientEquivOfSurjectiveOfKer]

/-- **Cohen–Macaulayness of a quotient by one regular element.**  A surjection of Noetherian
local rings whose kernel is generated by a single regular element of the maximal ideal carries
Cohen–Macaulayness to the target. -/
private lemma cm_of_principal_kernel {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : Function.Surjective f) (a : A)
    (hker : RingHom.ker f = Ideal.span {a})
    (hCM : IsCohenMacaulayLocalRing A) (hreg : IsSMulRegular A a)
    (ha : a ∈ IsLocalRing.maximalIdeal A) : IsCohenMacaulayLocalRing B := by
  let e := quotientEquivOfSurjectiveOfKer f hf (Ideal.span {a}) hker
  have : Nontrivial (A ⧸ Ideal.span {a}) := e.toEquiv.nontrivial
  have : IsLocalRing (A ⧸ Ideal.span {a}) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  exact (isCohenMacaulayLocalRing_iff_of_ringEquiv e).mp
    (cohenMacaulay_quotient_span_singleton_of_isSMulRegular hCM hreg ha)

/-- **Flatness of a composite through a principal quotient.**  If `A → B` is flat and
essentially of finite presentation and `B → C` is a surjection whose kernel is generated by an
element regular on the closed fibre, then `A → C` is flat. -/
private lemma flat_comp_of_principal_kernel
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (q : B →+* C) (hq : Function.Surjective q)
    (b : B) (hker : RingHom.ker q = Ideal.span {b})
    (hflat : f.Flat) (hfp : f.EssentiallyOfFinitePresentation)
    (hreg : IsSMulRegular (B ⧸ Ideal.map f (IsLocalRing.maximalIdeal A)) b) :
    (q.comp f).Flat := by
  let : Algebra A B := f.toAlgebra
  have halg : (algebraMap A B) = f := RingHom.algebraMap_toAlgebra f
  have : Module.Flat A B := hflat
  have hmul (J : Ideal B) : J • (⊤ : Submodule B B) = J :=
    (Ideal.smul_eq_mul J ⊤).trans (Ideal.mul_top J)
  have hr : IsSMulRegular
      (B ⧸ (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) •
        (⊤ : Submodule B B))) b := by
    rw [halg]
    exact ((Submodule.quotEquivOfEq _ _ (hmul
      (Ideal.map f (IsLocalRing.maximalIdeal A)))).isSMulRegular_congr b).mpr hreg
  have := (Module.Flat.isSMulRegular_and_flat_quotient_smul_of_isSMulRegular_maximalIdeal
    (M := B) (by rwa [halg]) hr).2
  have : Module.Flat A (B ⧸ Ideal.span {b}) :=
    Module.Flat.of_linearEquiv ((Submodule.quotEquivOfEq _ _
      (hmul (Ideal.span {b}))).restrictScalars A).symm
  have hflat' : ((Ideal.Quotient.mk (Ideal.span {b})).comp f).Flat := by
    rw [← halg]
    change (algebraMap A (B ⧸ Ideal.span {b})).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  let E := quotientEquivOfSurjectiveOfKer q hq (Ideal.span {b}) hker
  have hEq : q.comp f = E.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {b})).comp f) := by
    ext a
    exact (quotientEquivOfSurjectiveOfKer_mk q hq _ hker (f a)).symm
  rw [hEq]
  exact hflat'.comp (RingHom.Flat.of_bijective E.bijective)

/-- A point of the fibre over `f x` whose image in the source is `x` is the canonical point of
the fibre determined by `x`. -/
private lemma eq_asFiber_of_fiberι_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    {z : f.fiber (f x)} (hz : f.fiberι (f x) z = x) : z = f.asFiber x :=
  f.fiberι_injective _ (hz.trans (f.fiberι_asFiber x).symm)

/-- **Flatness of a composite at a point from regularity on the fibre.**  If the conormal ideal
of `p` at `x` is generated by one element whose image in the local ring of the fibre of `f` is
regular, and `f` is flat at the image, then `p ≫ f` is flat at `x`. -/
private lemma flatAt_comp_of_regular_fiber {X Y Z : Scheme.{u}}
    (p : X ⟶ Y) (f : Y ⟶ Z) [SurjectiveOnStalks p] [LocallyOfFinitePresentation f]
    (x : X) (y : Y) (hxy : p x = y) (u : Z) (hyu : f y = u)
    (z : f.fiber u) (hz : f.fiberι u z = y)
    (b : Y.presheaf.stalk y)
    (hker : RingHom.ker (p.stalkMapAt x y hxy) = Ideal.span {b})
    (hreg : IsSMulRegular ((f.fiber u).presheaf.stalk z)
      ((f.fiberι u).stalkMapAt z y hz b))
    (hflat : AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom y) :
    AlgebraicGeometry.IsFlatAt (p ≫ f).toLRSHom.toShHom x := by
  subst hxy
  subst hyu
  obtain rfl := eq_asFiber_of_fiberι_eq f hz
  have hstalk : ((p ≫ f).stalkMap x).hom =
      (p.stalkMap x).hom.comp (f.stalkMap (p x)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp p f x)
  change ((p ≫ f).stalkMap x).hom.Flat
  rw [hstalk]
  refine flat_comp_of_principal_kernel (f.stalkMap (p x)).hom
    (p.stalkMap x).hom (p.stalkMap_surjective x) b
    (by rwa [← stalkMapAt_self]) hflat
    (LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap f (p x)) ?_
  have hsmul : ∀ v : Y.presheaf.stalk (p x) ⧸
      Ideal.map (f.stalkMap (p x)).hom
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk (f (p x)))),
      b • v = (Ideal.Quotient.mk _ b) * v := fun v => by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  have hE : quotientStalkEquivFiberStalk f (p x) (Ideal.Quotient.mk _ b) =
      (f.fiberι (f (p x))).stalkMapAt (f.asFiber (p x)) (p x) hz b := by
    rw [stalkMapAt_apply_eq]
    exact quotientStalkEquivFiberStalk_mk f (p x) b
  intro v v' hvv'
  have hvv : (Ideal.Quotient.mk (Ideal.map (f.stalkMap (p x)).hom
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk (f (p x))))) b) * v =
      (Ideal.Quotient.mk (Ideal.map (f.stalkMap (p x)).hom
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk (f (p x))))) b) * v' := by
    rwa [← hsmul, ← hsmul]
  have hmul : (f.fiberι (f (p x))).stalkMapAt (f.asFiber (p x)) (p x) hz b *
        quotientStalkEquivFiberStalk f (p x) v =
      (f.fiberι (f (p x))).stalkMapAt (f.asFiber (p x)) (p x) hz b *
        quotientStalkEquivFiberStalk f (p x) v' := by
    rw [← hE, ← map_mul, ← map_mul]
    exact congrArg (quotientStalkEquivFiberStalk f (p x)) hvv
  exact (quotientStalkEquivFiberStalk f (p x)).injective (hreg hmul)

/-- **Cohen–Macaulayness at a point from flatness and the fibre.**  A morphism flat at `x`
whose fibre has a Cohen–Macaulay local ring at the point above `x` is Cohen–Macaulay at `x`. -/
private lemma cmAt_of_flat_of_fiberPoint {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hn : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (x : X) (y : Y) (hxy : f x = y) (z : f.fiber y) (hz : f.fiberι y z = x)
    (hflat : AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x)
    (hCM : letI := hn y; IsCohenMacaulayLocalRing ((f.fiber y).presheaf.stalk z)) :
    Scheme.Hom.IsCohenMacaulayAt f hn x := by
  subst hxy
  obtain rfl := eq_asFiber_of_fiberι_eq f hz
  exact ⟨hflat, hCM⟩

/-- An affine open neighbourhood on which a given element of the local ring is the germ of a
section. -/
private theorem exists_affine_germ_representative {X : Scheme.{u}} (x : X)
    (a : X.presheaf.stalk x) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (hx : x ∈ V) (s : Γ(X, V)),
      (X.presheaf.germ V x hx).hom s = a := by
  obtain ⟨V, hx, hV, s, hs⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens X.presheaf x a
  exact ⟨V, hV, hx, s, hs⟩

/-- The extension of an ideal of sections over an affine open to the global-section spectrum,
pushed into a stalk, is the image of its extension into the stalk of the ambient scheme. -/
private lemma map_germ_top_of_affineOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (J : Ideal Γ(X, U)) (q : Spec Γ(X, U)) (hq : hU.fromSpec q ∈ U) :
    Ideal.map ((Spec Γ(X, U)).presheaf.germ ⊤ q trivial).hom
        (Ideal.map ((Scheme.ΓSpecIso Γ(X, U)).inv).hom J) =
      Ideal.map (hU.fromSpec.stalkMap q).hom
        (Ideal.map (X.presheaf.germ U (hU.fromSpec q) hq).hom J) := by
  rw [Ideal.map_map, Ideal.map_map]
  simp only [← CommRingCat.hom_comp]
  rw [germ_fromSpec_stalkMap hU q hq]

/-- A point of a scheme at which an ideal of global sections has germs in the maximal ideal
lies on the zero scheme of that ideal. -/
private lemma mem_support_ofIdealTop_of_map_germ_le {W : Scheme.{u}} (J : Ideal Γ(W, ⊤))
    (q : W) (hle : Ideal.map (W.presheaf.germ ⊤ q trivial).hom J ≤
      IsLocalRing.maximalIdeal (W.presheaf.stalk q)) :
    q ∈ (Scheme.IdealSheafData.ofIdealTop J).support := by
  rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_ofIdealTop,
    Scheme.mem_zeroLocus_iff]
  intro s hs hq
  exact (IsLocalRing.mem_maximalIdeal _).mp
    (hle (Ideal.mem_map_of_mem _ hs)) ((W.mem_basicOpen_top s q).mp hq)

/-- The conormal ideal at a point of a closed subscheme composed with an open immersion: it is
the ideal whose extension along the open immersion is the conormal ideal of the closed
subscheme. -/
private lemma ker_stalkMapAt_subschemeι_comp {W X : Scheme.{u}} (ι : W ⟶ X)
    [IsOpenImmersion ι] (D : W.IdealSheafData) (y : D.subscheme)
    (J : Ideal (X.presheaf.stalk (ι (D.subschemeι y))))
    (hJ : RingHom.ker (D.subschemeι.stalkMap y).hom =
      Ideal.map (ι.stalkMap (D.subschemeι y)).hom J)
    (hx' : (D.subschemeι ≫ ι) y = ι (D.subschemeι y)) :
    RingHom.ker ((D.subschemeι ≫ ι).stalkMapAt y (ι (D.subschemeι y)) hx') = J := by
  have hgoal : (D.subschemeι ≫ ι).stalkMapAt y (ι (D.subschemeι y)) hx' =
      ((D.subschemeι.stalkMap y).hom).comp (ι.stalkMap (D.subschemeι y)).hom := by
    rw [← stalkMapAt_self ι (D.subschemeι y), ← stalkMapAt_self D.subschemeι y]
    exact (Scheme.Hom.stalkMapAt_comp D.subschemeι ι y (D.subschemeι y)
      (ι (D.subschemeι y)) rfl rfl).symm
  rw [hgoal, ← RingHom.comap_ker, hJ]
  exact Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (ι.stalkMap (D.subschemeι y)))

/-- **An affine locally closed slice cutting out a prescribed element of a local ring.**  For a
non-unit `a` of the local ring of `X` at `x` there is an affine scheme immersed in `X`, locally
of finite presentation, through a point above `x`, whose conormal ideal at that point is
generated by `a`. -/
private theorem exists_affine_slice_from_stalk_element {X : Scheme.{u}} (x : X)
    (a : X.presheaf.stalk x)
    (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∃ (U' : Scheme.{u}) (g : U' ⟶ X) (x' : U') (hx' : g x' = x),
      IsAffine U' ∧ IsImmersion g ∧ LocallyOfFinitePresentation g ∧
        RingHom.ker (g.stalkMapAt x' x hx') = Ideal.span {a} := by
  classical
  obtain ⟨V, hV, hxV, sec, hsec⟩ := exists_affine_germ_representative x a
  obtain ⟨w, hwx⟩ : ∃ w : Spec Γ(X, V), hV.fromSpec w = x :=
    ⟨hV.primeIdealOf ⟨x, hxV⟩, hV.fromSpec_primeIdealOf ⟨x, hxV⟩⟩
  subst hwx
  obtain ⟨t, ht⟩ : ∃ t : Γ(Spec Γ(X, V), ⊤),
      Ideal.map ((Spec Γ(X, V)).presheaf.germ ⊤ w trivial).hom (Ideal.span {t}) =
        Ideal.map (hV.fromSpec.stalkMap w).hom (Ideal.span {a}) := by
    refine ⟨((Scheme.ΓSpecIso Γ(X, V)).inv).hom sec, ?_⟩
    have h1 : Ideal.span {((Scheme.ΓSpecIso Γ(X, V)).inv).hom sec} =
        Ideal.map ((Scheme.ΓSpecIso Γ(X, V)).inv).hom (Ideal.span {sec}) := by
      rw [Ideal.map_span, Set.image_singleton]
    have h2 : Ideal.map (X.presheaf.germ V (hV.fromSpec w) hxV).hom (Ideal.span {sec}) =
        Ideal.span {a} := by
      rw [Ideal.map_span, Set.image_singleton, hsec]
    rw [h1, map_germ_top_of_affineOpen hV (Ideal.span {sec}) w hxV, h2]
  have hwmem : w ∈ (Scheme.IdealSheafData.ofIdealTop (Ideal.span {t})).support := by
    refine mem_support_ofIdealTop_of_map_germ_le (Ideal.span {t}) w ?_
    rw [ht]
    refine le_trans (Ideal.map_mono (Ideal.span_le.mpr ?_))
      (IsLocalRing.map_maximalIdeal_le (hV.fromSpec.stalkMap w).hom)
    simpa using ha
  have hfpι : LocallyOfFinitePresentation
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {t})).subschemeι :=
    Stacks.AlgebraicGeometry.locallyOfFinitePresentation_subschemeι_ofIdealTop
      (Ideal.span {t}) (Submodule.fg_span_singleton t)
  refine ⟨(Scheme.IdealSheafData.ofIdealTop (Ideal.span {t})).subscheme,
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span {t})).subschemeι ≫ hV.fromSpec,
    ⟨w, hwmem⟩, rfl, ?_, inferInstance, inferInstance, ?_⟩
  · exact (IsClosedImmersion.isAffine_surjective_of_isAffine
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {t})).subschemeι).1
  · exact ker_stalkMapAt_subschemeι_comp hV.fromSpec _ ⟨w, hwmem⟩ (Ideal.span {a})
      ((Stacks.AlgebraicGeometry.ker_stalkMap_subschemeι_ofIdealTop
        (Ideal.span {t}) w hwmem).trans ht) rfl

/-- An isomorphism of residue fields has transcendence degree zero. -/
private theorem trdeg_zero_of_isIso_residueFieldMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) [IsIso (f.residueFieldMap x)] :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg (Y.residueField (f x)) (X.residueField x) = 0 := by
  let _ := (f.residueFieldMap x).hom.toAlgebra
  have hsurj : Function.Surjective
      (algebraMap (Y.residueField (f x)) (X.residueField x)) := by
    change Function.Surjective (f.residueFieldMap x).hom
    exact (ConcreteCategory.bijective_of_isIso (f.residueFieldMap x)).surjective
  rw [trdeg_eq_zero_iff, Algebra.isAlgebraic_def]
  intro z
  obtain ⟨a, ha⟩ := hsurj z
  exact ⟨Polynomial.X - Polynomial.C a, Polynomial.X_sub_C_ne_zero a, by simp [ha]⟩

/-- Where the residue field extension of a morphism locally of finite type is trivial, the
dimension of its fibre equals the Krull dimension of the local ring of the fibre. -/
private lemma dimensionAt_fiber_eq_of_isIso_residueFieldMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) [IsIso (f.residueFieldMap x)] (y : Y) (hxy : f x = y)
    (z : f.fiber y) (hz : f.fiberι y z = x) :
    topologicalKrullDimAt (f.fiber y) z = ringKrullDim ((f.fiber y).presheaf.stalk z) := by
  subst y
  obtain rfl := eq_asFiber_of_fiberι_eq f hz
  have hd := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f x
  rw [trdeg_zero_of_isIso_residueFieldMap f x] at hd
  simpa using hd

/-- At the identity arrow the dimension of the source fibre is the Krull dimension of the local
ring of the source fibre there. -/
private theorem sourceFiberIdentity_dimension_eq {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left)
    [LocallyOfFiniteType G.source.left] :
    topologicalKrullDimAt (G.source.left.fiber u) (sourceFiberIdentity G u) =
      ringKrullDim ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u)) := by
  have : IsIso (G.source.left.residueFieldMap (G.identity.left u)) :=
    isIso_residueFieldMap_of_mem_range_section G.source.left G.identity.left
      (identity_left_comp_source_left G) u
  exact dimensionAt_fiber_eq_of_isIso_residueFieldMap G.source.left (G.identity.left u) u
    (source_identity_apply G u) (sourceFiberIdentity G u) (fiberι_sourceFiberIdentity G u)

/-- The local ring of the source fibre at the identity arrow, cut by the maximal ideal pulled
back along the restricted target map, is the local ring of the fibre of that map. -/
private theorem ringKrullDim_sourceFiber_targetCut_stalk_eq_quotient
    {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.objects.left) :
    ringKrullDim (((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u)) ⧸
      Ideal.map ((targetOnSourceFiber G u).stalkMap (sourceFiberIdentity G u)).hom
        (IsLocalRing.maximalIdeal (G.objects.left.presheaf.stalk
          ((targetOnSourceFiber G u) (sourceFiberIdentity G u))))) =
      ringKrullDim (((targetOnSourceFiber G u).fiber
          ((targetOnSourceFiber G u) (sourceFiberIdentity G u))).presheaf.stalk
        ((targetOnSourceFiber G u).asFiber (sourceFiberIdentity G u))) :=
  (quotientStalkEquivFiberStalk (targetOnSourceFiber G u)
    (sourceFiberIdentity G u)).ringKrullDim

/-- Cutting the local ring of the source fibre at the identity arrow by the maximal ideal of the
image point of the restricted target map gives a ring of dimension at most that of the
stabilizer fibre. -/
private theorem sourceFiberTargetCut_dimension_le_stabilizerFiber
    {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.objects.left)
    (hu : AlgebraicGeometry.IsFiniteTypePoint u)
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    ringKrullDim (((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u)) ⧸
      Ideal.map ((targetOnSourceFiber G u).stalkMap (sourceFiberIdentity G u)).hom
        (IsLocalRing.maximalIdeal (G.objects.left.presheaf.stalk
          ((targetOnSourceFiber G u) (sourceFiberIdentity G u))))) ≤
      topologicalKrullDim ((stabilizer G).hom.fiber u) := by
  have hdimIso : topologicalKrullDim
        (GroupoidScheme.restrict G (residueChart G u)).groupoid.arrows.left =
      topologicalKrullDim ((targetOnSourceFiber G u).fiber
        ((targetOnSourceFiber G u) (sourceFiberIdentity G u))) :=
    IsHomeomorph.topologicalKrullDim_eq _
      (restrictedArrows_iso_sourceFiberTargetCut G u).hom.homeomorph.isHomeomorph
  calc
    _ = ringKrullDim (((targetOnSourceFiber G u).fiber
          ((targetOnSourceFiber G u) (sourceFiberIdentity G u))).presheaf.stalk
        ((targetOnSourceFiber G u).asFiber (sourceFiberIdentity G u))) :=
      ringKrullDim_sourceFiber_targetCut_stalk_eq_quotient G u
    _ ≤ topologicalKrullDim ((targetOnSourceFiber G u).fiber
        ((targetOnSourceFiber G u) (sourceFiberIdentity G u))) :=
      Stacks.AlgebraicGeometry.NormalizationQuotient.ringKrullDim_stalk_le_topologicalKrullDim
        _ _
    _ = topologicalKrullDim
        (GroupoidScheme.restrict G (residueChart G u)).groupoid.arrows.left := hdimIso.symm
    _ = topologicalKrullDim ((stabilizer G).hom.fiber u) :=
      restrictedArrows_dimension_eq_stabilizerFiber G u hu

/-- Cohen–Macaulayness of the local ring of a scheme-theoretic fibre, transported along an
equality of base points. -/
private theorem cm_fiber_point_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : f x = y)
    [IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))]
    [IsNoetherianRing ((f.fiber y).presheaf.stalk (h ▸ f.asFiber x))]
    (hCM : IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) :
    IsCohenMacaulayLocalRing ((f.fiber y).presheaf.stalk (h ▸ f.asFiber x)) := by
  cases h
  exact hCM

/-- The residue field map of a morphism surjective on stalks is an isomorphism. -/
private lemma residueFieldMap_isIso_of_surjectiveOnStalks {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : SurjectiveOnStalks f) (x : X) : IsIso (f.residueFieldMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  apply Function.Surjective.of_comp (g := (Y.residue (f x)).hom)
  change Function.Surjective (Y.residue (f x) ≫ f.residueFieldMap x).hom
  rw [Scheme.residue_residueFieldMap]
  exact (IsLocalRing.residue_surjective).comp (f.stalkMap_surjective x)

/-- The stalk map at a prescribed image point of a morphism surjective on stalks is
surjective. -/
private lemma stalkMapAt_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : SurjectiveOnStalks f) (x : X) (y : Y) (h : f x = y) :
    Function.Surjective (f.stalkMapAt x y h) := by
  subst y
  rw [stalkMapAt_self]
  exact f.stalkMap_surjective x

/-- A base change of an immersion is an immersion. -/
private lemma immersion_of_isPullback {P X Y Z : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (H : IsPullback a b f g) (hg : IsImmersion g) : IsImmersion a := by
  rw [← H.isoPullback_hom_fst]
  infer_instance

/-- **Stacks Project, Tag 0461.** Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t`
Cohen--Macaulay and locally of finite presentation, let `u` be a finite type point of `U`, and
suppose the source fibre `F_u` has larger dimension at the identity arrow than the stabilizer
fibre `G_u`. Then there are an affine scheme `U'` and a morphism `g : U' ⟶ U` which is an
immersion through `u` and locally of finite presentation, such that `h : U' ×_{g,U,t} R ⟶ U`
is Cohen--Macaulay at the identity arrow and the restricted source fibre has dimension one
less at the restricted identity arrow. -/
@[stacks 0461]
public theorem exists_affine_slice_dim_sub_one {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left)
    (hs : ∃ h : ∀ y : G.objects.left, IsLocallyNoetherian (G.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.source.left h)
    (_ht : ∃ h : ∀ y : G.objects.left, IsLocallyNoetherian (G.target.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.target.left h)
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left]
    (hu : IsFiniteTypePoint u)
    (hdim : topologicalKrullDim ((stabilizer G).hom.fiber u) <
      topologicalKrullDimAt (G.source.left.fiber u) (sourceFiberIdentity G u))
    :
    ∃ (U' : Over S) (g : U' ⟶ G.objects) (u' : U'.left) (hu' : g.left u' = u),
      let E : SliceSituation := ⟨S, G, U', g, u, u', hu'⟩
      IsAffine U'.left ∧ IsImmersion g.left ∧ LocallyOfFinitePresentation g.left ∧
        (∃ (x : E.arrowSource.left)
          (_ : (pullback.fst E.g E.groupoid.target).left x = u')
          (_ : (pullback.snd E.g E.groupoid.target).left x = E.groupoid.identity.left E.u)
          (hnoeth : ∀ y : E.groupoid.objects.left,
            IsLocallyNoetherian (E.sourceMap.left.fiber y)),
          Scheme.Hom.IsCohenMacaulayAt E.sourceMap.left hnoeth x) ∧
        topologicalKrullDimAt E.restrictedSourceFiber
            E.sliceIdentityPoints.restrictedSourceIdentity + 1 =
          topologicalKrullDimAt (G.source.left.fiber u) (sourceFiberIdentity G u) := by
  classical
  obtain ⟨hsourceNoeth, hsourceCM⟩ := hs
  have he : G.source.left (G.identity.left u) = u := source_identity_apply G u
  have := hsourceNoeth (G.source.left (G.identity.left u))
  have := hsourceNoeth u
  have hCMFiber : IsCohenMacaulayLocalRing
      ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u)) :=
    cm_fiber_point_eq G.source.left (G.identity.left u) u he
      (hsourceCM (G.identity.left u)).2
  have hz : targetOnSourceFiber G u (sourceFiberIdentity G u) = u :=
    targetOnSourceFiber_sourceFiberIdentity G u
  have hquotlt : ringKrullDim
      (((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u)) ⧸
      Ideal.map ((targetOnSourceFiber G u).stalkMap (sourceFiberIdentity G u)).hom
        (IsLocalRing.maximalIdeal (G.objects.left.presheaf.stalk
          ((targetOnSourceFiber G u) (sourceFiberIdentity G u))))) <
      ringKrullDim ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u)) := by
    rw [← sourceFiberIdentity_dimension_eq G u]
    exact lt_of_le_of_lt (sourceFiberTargetCut_dimension_le_stabilizerFiber G u hu) hdim
  obtain ⟨a, ha, hregular, hdrop⟩ :=
    IsCohenMacaulayLocalRing.exists_mem_maximalIdeal_isSMulRegular_map_of_ringKrullDim_lt
      _ _ hCMFiber
      ((targetOnSourceFiber G u).stalkMap (sourceFiberIdentity G u)).hom inferInstance hquotlt
  obtain ⟨U0, g0, u0, hu0, hU0, hg0, hfp0, hker0⟩ :=
    exists_affine_slice_from_stalk_element
      ((targetOnSourceFiber G u) (sourceFiberIdentity G u)) a ha
  let U' : Over S := Over.mk (g0 ≫ G.objects.hom)
  let g : U' ⟶ G.objects := Over.homMk g0 rfl
  have hu' : g.left u0 = u := hu0.trans hz
  let E : SliceSituation := ⟨S, G, U', g, u, u0, hu'⟩
  have : LocallyOfFinitePresentation E.g.left := hfp0
  have hsourcefp : LocallyOfFinitePresentation E.sourceMap.left := by
    change LocallyOfFinitePresentation
      ((pullback.snd E.g E.groupoid.target).left ≫ E.groupoid.source.left)
    have hfpSnd : LocallyOfFinitePresentation
        ((pullback.snd E.g E.groupoid.target).left) := by
      rw [← overPullbackLeftIso_hom_snd E.g E.groupoid.target]
      infer_instance
    infer_instance
  have hnoeth : ∀ y : E.groupoid.objects.left,
      IsLocallyNoetherian (E.sourceMap.left.fiber y) := fun y =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation E.sourceMap.left y
  have hsurjg : SurjectiveOnStalks g0 := hg0.toIsPreimmersion.toSurjectiveOnStalks
  have H : IsPullback (pullback.snd E.g E.groupoid.target).left
      (pullback.fst E.g E.groupoid.target).left G.target.left g0 :=
    (IsPullback.of_isLimit_cone
      (isLimitOfPreserves (Over.forget S) (pullback.isLimit E.g E.groupoid.target))).flip
  have himmsnd : IsImmersion (pullback.snd E.g E.groupoid.target).left :=
    immersion_of_isPullback H hg0
  have hsurjsnd : SurjectiveOnStalks (pullback.snd E.g E.groupoid.target).left :=
    himmsnd.toIsPreimmersion.toSurjectiveOnStalks
  have : IsIso (E.g.left.residueFieldMap E.u') :=
    residueFieldMap_isIso_of_surjectiveOnStalks E.g.left hsurjg E.u'
  have hresspec : IsIso E.residueSpectrumMap := by
    dsimp only [SliceSituation.residueSpectrumMap]
    infer_instance
  have hfstiso : IsIso (pullback.fst (E.sourceMap.left.fiberToSpecResidueField E.u)
      E.residueSpectrumMap) := (IsPullback.of_hasPullback _ _).isIso_fst_of_isIso hresspec
  let d : E.restrictedSourceFiber ≅ E.sourceMap.left.fiber E.u :=
    E.sliceFiberComparison.iso ≪≫ @asIso _ _ _ _
      (pullback.fst (E.sourceMap.left.fiberToSpecResidueField E.u) E.residueSpectrumMap)
      hfstiso
  let y := d.hom E.sliceIdentityPoints.restrictedSourceIdentity
  let x := E.sourceMap.left.fiberι E.u y
  have hd : d.hom ≫ (E.sourceMap.left.fiberι E.u ≫
        (pullback.snd E.g E.groupoid.target).left) =
      E.restrictedSource.fiberι E.u' ≫ (restrictionArrowsToArrows E.groupoid E.g).left :=
    (Category.assoc _ _ _).trans E.sliceFiberComparison.iso_hom_arrow
  have hx2 : (pullback.snd E.g E.groupoid.target).left x =
      E.groupoid.identity.left E.u := by
    have e1 := Scheme.Hom.comp_apply d.hom
      (E.sourceMap.left.fiberι E.u ≫ (pullback.snd E.g E.groupoid.target).left)
      E.sliceIdentityPoints.restrictedSourceIdentity
    have e2 := Scheme.Hom.comp_apply (E.sourceMap.left.fiberι E.u)
      (pullback.snd E.g E.groupoid.target).left y
    have e3 := congrArg (fun k : E.restrictedSourceFiber ⟶ E.groupoid.arrows.left =>
      k E.sliceIdentityPoints.restrictedSourceIdentity) hd
    have e4 := Scheme.Hom.comp_apply (E.restrictedSource.fiberι E.u')
      (restrictionArrowsToArrows E.groupoid E.g).left
      E.sliceIdentityPoints.restrictedSourceIdentity
    calc (pullback.snd E.g E.groupoid.target).left x
        = (E.sourceMap.left.fiberι E.u ≫
            (pullback.snd E.g E.groupoid.target).left) y := e2.symm
      _ = (d.hom ≫ (E.sourceMap.left.fiberι E.u ≫
            (pullback.snd E.g E.groupoid.target).left))
            E.sliceIdentityPoints.restrictedSourceIdentity := e1.symm
      _ = (E.restrictedSource.fiberι E.u' ≫
            (restrictionArrowsToArrows E.groupoid E.g).left)
            E.sliceIdentityPoints.restrictedSourceIdentity := e3
      _ = (restrictionArrowsToArrows E.groupoid E.g).left
            (E.restrictedSource.fiberι E.u'
              E.sliceIdentityPoints.restrictedSourceIdentity) := e4
      _ = E.groupoid.identity.left E.u := by
          rw [E.sliceIdentityPoints.restrictedSourceIdentity_fiberι]
          exact E.sliceIdentityPoints.restrictedIdentity_arrow
  have htid : G.target.left (G.identity.left u) = u := by
    simpa using congrArg (fun k : G.objects.left ⟶ G.objects.left => k u)
      (identity_left_comp_target_left G)
  have hx1 : (pullback.fst E.g E.groupoid.target).left x = u0 := by
    apply g0.isEmbedding.injective
    calc
      g0 ((pullback.fst E.g E.groupoid.target).left x) =
          G.target.left ((pullback.snd E.g E.groupoid.target).left x) :=
        congrArg (fun k : E.arrowSource.left ⟶ G.objects.left => k x) H.w.symm
      _ = u := by rw [hx2, htid]
      _ = g0 u0 := hu'.symm
  have hx : E.sourceMap.left x = u := by
    change E.groupoid.source.left ((pullback.snd E.g E.groupoid.target).left x) = u
    rwa [hx2]
  have Hq : IsPullback
      (fiberMapOfComp (pullback.snd E.g E.groupoid.target).left G.source.left u)
      (E.sourceMap.left.fiberι u) (G.source.left.fiberι u)
      (pullback.snd E.g E.groupoid.target).left :=
    isPullback_fiberMapOfComp (pullback.snd E.g E.groupoid.target).left G.source.left u
  have himmq : IsImmersion
      (fiberMapOfComp (pullback.snd E.g E.groupoid.target).left G.source.left u) :=
    immersion_of_isPullback Hq himmsnd
  have hqz : fiberMapOfComp (pullback.snd E.g E.groupoid.target).left G.source.left u y =
      sourceFiberIdentity G u := by
    apply G.source.left.fiberι_injective u
    calc
      G.source.left.fiberι u
            (fiberMapOfComp (pullback.snd E.g E.groupoid.target).left G.source.left u y) =
          (pullback.snd E.g E.groupoid.target).left x :=
        congrArg (fun k : E.sourceMap.left.fiber u ⟶ G.arrows.left => k y) Hq.w
      _ = G.identity.left u := hx2
      _ = G.source.left.fiberι u (sourceFiberIdentity G u) :=
        (fiberι_sourceFiberIdentity G u).symm
  have hkerq : RingHom.ker
      ((fiberMapOfComp (pullback.snd E.g E.groupoid.target).left G.source.left u).stalkMapAt y
        (sourceFiberIdentity G u) hqz) =
      Ideal.span {((targetOnSourceFiber G u).stalkMap (sourceFiberIdentity G u)).hom a} := by
    have hk := @ker_stalkMapAt_of_isPullback _ _ _ _ _ _ _ _ (Hq.paste_vert H) hsurjg y
      (sourceFiberIdentity G u) u0
      ((targetOnSourceFiber G u) (sourceFiberIdentity G u)) hqz hx1 rfl hu0
    have hPhi : (G.source.left.fiberι u ≫ G.target.left).stalkMapAt
          (sourceFiberIdentity G u)
          ((targetOnSourceFiber G u) (sourceFiberIdentity G u)) rfl =
        ((targetOnSourceFiber G u).stalkMap (sourceFiberIdentity G u)).hom :=
      stalkMapAt_self (targetOnSourceFiber G u) (sourceFiberIdentity G u)
    rwa [hker0, Ideal.map_span, Set.image_singleton, hPhi] at hk
  have hfQ : Function.Surjective
      ((fiberMapOfComp (pullback.snd E.g E.groupoid.target).left G.source.left u).stalkMapAt y
        (sourceFiberIdentity G u) hqz) :=
    stalkMapAt_surjective _ himmq.toIsPreimmersion.toSurjectiveOnStalks _ _ hqz
  have hmem : ((targetOnSourceFiber G u).stalkMap (sourceFiberIdentity G u)).hom a ∈
      IsLocalRing.maximalIdeal
        ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u)) :=
    IsLocalRing.map_maximalIdeal_le _ (Ideal.mem_map_of_mem _ ha)
  have hnu := hnoeth u
  have hCMnew : IsCohenMacaulayLocalRing ((E.sourceMap.left.fiber u).presheaf.stalk y) :=
    cm_of_principal_kernel _ hfQ _ hkerq hCMFiber hregular hmem
  have hkerp : RingHom.ker
      ((pullback.snd E.g E.groupoid.target).left.stalkMapAt x (G.identity.left u) hx2) =
      Ideal.span {G.target.left.stalkMapAt (G.identity.left u)
                    ((targetOnSourceFiber G u) (sourceFiberIdentity G u)) (htid.trans hz.symm)
                    a} := by
    have hk := @ker_stalkMapAt_of_isPullback _ _ _ _ _ _ _ _ H hsurjg x (G.identity.left u) u0
      ((targetOnSourceFiber G u) (sourceFiberIdentity G u)) hx2 hx1
      (htid.trans hz.symm) hu0
    rwa [hker0, Ideal.map_span, Set.image_singleton] at hk
  have hb : (G.source.left.fiberι u).stalkMapAt (sourceFiberIdentity G u)
        (G.identity.left u) (fiberι_sourceFiberIdentity G u)
        (G.target.left.stalkMapAt (G.identity.left u)
          ((targetOnSourceFiber G u) (sourceFiberIdentity G u))
          (htid.trans hz.symm) a) =
      ((targetOnSourceFiber G u).stalkMap (sourceFiberIdentity G u)).hom a := by
    have hc := Scheme.Hom.stalkMapAt_comp (G.source.left.fiberι u) G.target.left
      (sourceFiberIdentity G u) (G.identity.left u)
      ((targetOnSourceFiber G u) (sourceFiberIdentity G u))
      (fiberι_sourceFiberIdentity G u) (htid.trans hz.symm)
    refine (congrArg (fun k => k a) hc).trans ?_
    rw [Scheme.Hom.stalkMapAt_congr (G.source.left.fiberι u ≫ G.target.left)
      (targetOnSourceFiber G u) rfl (sourceFiberIdentity G u)
      ((targetOnSourceFiber G u) (sourceFiberIdentity G u)) _ rfl, stalkMapAt_self]
  have hflat : IsFlatAt E.sourceMap.left.toLRSHom.toShHom x :=
    @flatAt_comp_of_regular_fiber _ _ _ (pullback.snd E.g E.groupoid.target).left
      G.source.left hsurjsnd inferInstance x (G.identity.left u) hx2 u he
      (sourceFiberIdentity G u)
      (fiberι_sourceFiberIdentity G u) _ hkerp
      (by rw [hb]; exact hregular) (hsourceCM (G.identity.left u)).1
  have hCM := cmAt_of_flat_of_fiberPoint E.sourceMap.left hnoeth x u hx y rfl hflat hCMnew
  have hr1 : IsIso (E.groupoid.source.left.residueFieldMap
      ((pullback.snd E.g E.groupoid.target).left x)) := by
    rw [hx2]
    exact isIso_residueFieldMap_of_mem_range_section E.groupoid.source.left E.groupoid.identity.left
      (identity_left_comp_source_left E.groupoid) E.u
  have hr2 : IsIso ((pullback.snd E.g E.groupoid.target).left.residueFieldMap x) :=
    residueFieldMap_isIso_of_surjectiveOnStalks _ hsurjsnd x
  have hr3 : IsIso (E.sourceMap.left.residueFieldMap x) := by
    have hc : E.sourceMap.left.residueFieldMap x =
        E.groupoid.source.left.residueFieldMap
            ((pullback.snd E.g E.groupoid.target).left x) ≫
          (pullback.snd E.g E.groupoid.target).left.residueFieldMap x :=
      Scheme.residueFieldMap_comp (pullback.snd E.g E.groupoid.target).left
        E.groupoid.source.left x
    rw [hc]
    exact CategoryTheory.IsIso.comp_isIso' hr1 hr2
  have hdnew := @dimensionAt_fiber_eq_of_isIso_residueFieldMap _ _ E.sourceMap.left
    inferInstance x hr3 u hx y rfl
  have hdq := (quotientEquivOfSurjectiveOfKer _ hfQ
    (Ideal.span {((targetOnSourceFiber G u).stalkMap (sourceFiberIdentity G u)).hom a})
    hkerq).ringKrullDim
  have hdcomp := topologicalKrullDimAt_eq_of_homeomorph d.hom.homeomorph
    E.sliceIdentityPoints.restrictedSourceIdentity
  refine ⟨U', g, u0, hu', hU0, hg0, hfp0, ⟨x, hx1, hx2, hnoeth, hCM⟩, ?_⟩
  change topologicalKrullDimAt E.restrictedSourceFiber
    E.sliceIdentityPoints.restrictedSourceIdentity + 1 = _
  rw [hdcomp]
  change topologicalKrullDimAt (E.sourceMap.left.fiber u) y + 1 = _
  rw [hdnew]
  exact (congrArg (fun n : WithBot ℕ∞ => n + 1) hdq.symm).trans
    (hdrop.trans (sourceFiberIdentity_dimension_eq G u).symm)

end AlgebraicGeometry

end
