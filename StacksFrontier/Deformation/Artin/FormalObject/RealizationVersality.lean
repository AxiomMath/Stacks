module

public import StacksFrontier.Deformation.Artin.FormalObject.OfPredeformation
public import StacksFrontier.Deformation.Artin.FormalObject.Realization
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityAffineOpenBase

/-!
# Versality read on a realizing object

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, and let `η` be a formal object of
the predeformation category of a point `x₀ : Spec k ⟶ 𝒳` over `𝒞_Λ` (**Stacks 07T4**) whose levels
are the restrictions of an object `y` over `Spec η.base`, by compatible arrows lying over the
inclusions of the infinitesimal thickenings. Then `η` is versal (**Stacks 06HR**) exactly when `y`
has the lifting property defining versality at a point (**Stacks 07XF**) at the residue point
`x₀ ⟶ y`. This is the comparison of **Stacks 0CXK** with the completion of a scheme at a point
replaced by `Spec η.base` itself. The lifting property of `y` only depends on `y` and on its
residue point, and it transports along a change of residue field
(`Deformation.Artin.liftsAtResiduePoint_changeResidueField`) and between an affine open and the
local ring of the base (`Deformation.Artin.liftsAtResiduePoint_iff_affineOpenBase`); this moves
versality between predeformation categories built at different points, residue fields and
deformation bases (`Deformation.Artin.isVersal_stalk_ofPredeformation_of_realization`).

## Main results

* `Deformation.Artin.exists_completeLocalAlgHom_of_specMap`: a morphism from the spectrum of an
  Artinian local `Λ`-algebra to `Spec A` over `Spec Λ`, inducing the residue point, is the spectrum
  of a morphism of `\widehat{𝒞}_Λ`.
* `Deformation.Artin.liftsAtResiduePoint_iff_isVersal_of_realizing`: versality of a formal object
  of a predeformation category is the lifting property of a realizing object.

## References

* [Stacks Project, Tag 06HR](https://stacks.math.columbia.edu/tag/06HR)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 0CXK](https://stacks.math.columbia.edu/tag/0CXK)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

/-! ### Points of a complete local spectrum -/

section Points

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}
  (iΛ : Spec (.of Λ) ⟶ S) [Mono iΛ]

/-- The residue map of a complete local `Λ`-algebra with residue field `k`. -/
abbrev completeResidueMap (A : CompleteLocalAlgCat.{u, u, u} Λ k) : A →+* k :=
  A.residueEquiv.toAlgHom.toRingHom.comp (residue A)

/-- **Points of `Spec A` with values in an Artinian local algebra.** A morphism
`f : Spec B ⟶ Spec A` over `Spec Λ ⟶ S`, from the spectrum of an object `B` of `𝒞_Λ`, which induces
the residue point `Spec k ⟶ Spec A`, is the spectrum of a morphism `A ⟶ B` of `\widehat{𝒞}_Λ`. -/
theorem exists_completeLocalAlgHom_of_specMap (A : CompleteLocalAlgCat.{u, u, u} Λ k)
    (B : ArtinianLocalAlgCat.{u, u, u} Λ k) (f : Spec (.of B) ⟶ Spec (.of A))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ)
    (hres : Spec.map (CommRingCat.ofHom (residueMap B)) ≫ f =
      Spec.map (CommRingCat.ofHom (completeResidueMap A))) :
    ∃ α : A ⟶ artinianToComplete.obj B, Spec.map (CommRingCat.ofHom α.hom.toRingHom) = f := by
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of A ⟶ CommRingCat.of B, Spec.map φ = f :=
    ⟨Spec.preimage f, Spec.map_preimage f⟩
  have hlin : φ.hom.comp (algebraMap Λ A) = algebraMap Λ B := by
    have h := (cancel_mono iΛ).mp (((Category.assoc _ _ _).trans hf :
      (Spec.map φ ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ A))) ≫ iΛ = _))
    rw [← Spec.map_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have hres' : (residueMap B).comp φ.hom = completeResidueMap A := by
    rw [← Spec.map_comp] at hres
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hres)
  let φΛ : A →ₐ[Λ] B := { φ.hom with commutes' := fun c => RingHom.congr_fun hlin c }
  refine ⟨{ hom := φΛ, isLocal := ⟨fun a ha => ?_⟩, residue_comm := fun a => ?_ }, rfl⟩
  · have h1 : residueMap B (φ.hom a) ≠ 0 := (ha.map (residueMap B)).ne_zero
    rw [← RingHom.comp_apply, hres'] at h1
    have h2 : residue A a ≠ 0 := fun h => h1 (by simp [completeResidueMap, h])
    exact (residue_ne_zero_iff_isUnit a).mp h2
  · exact RingHom.congr_fun hres' a

end Points

/-! ### Versality and the lifting property of a realizing object -/

section Lifting

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S} [Mono iΛ]
  {x₀ : F} (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- **Versality of a formal object of a predeformation category is the lifting property of an
object realizing it.** Let `η` be a formal object of the predeformation category of `x₀` over
`𝒞_Λ`, and let `y` be an object over `Spec η.base ⟶ Spec Λ ⟶ S` with compatible arrows `r_n` from
the levels of `η`, lying over the inclusions of the infinitesimal thickenings, and an arrow
`r₀ : x₀ ⟶ y` through which all arrows out of `x₀` factor and which lies over the residue point
`Spec k ⟶ Spec η.base`. Then `η` is versal exactly when `y` has the lifting property at `r₀`. -/
theorem liftsAtResiduePoint_iff_isVersal_of_realizing
    (η : Deformation.FormalObject
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    {y : F} (hy : (p ⋙ Over.post B.inclusion).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ η.base)) ≫ iΛ))
    (r : ∀ n, ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
      (η.level n)).point ⟶ y)
    (hr : ∀ n, ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).morphisms _ _
      (η.transition n)).arrow ≫ r (n + 1) = r n)
    (hbase : ∀ n,
      eqToHom (congrArg Over.left (deformationPointBase (predeformationCategory
          iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀) (η.level n)
          (AdicTruncation.obj η.base n) (η.level_eq n))).symm ≫
        ((p ⋙ Over.post B.inclusion).map (r n)).left ≫ eqToHom (congrArg Over.left hy) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (AdicTruncation.ideal η.base n))))
    (r₀ : x₀ ⟶ y)
    (hclosed : ∀ n, ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
      (η.level n)).arrow ≫ r n = r₀)
    (hκ : schemeMap (p ⋙ Over.post B.inclusion) hx₀ hy r₀ =
      Spec.map (CommRingCat.ofHom (completeResidueMap η.base))) :
    LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion)
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ η.base)) ≫ iΛ)) y hy
        (Spec.map (CommRingCat.ofHom (completeResidueMap η.base))) ↔
      Deformation.IsVersal (predeformationCategory_isPredeformationCategory
        B hS iΛ p x₀ hx₀ hp).cofibered η := by
  rw [← hκ]
  refine liftsAtResiduePoint_iff_isVersal_of_restrictions B S hS p hp hx₀ η _ hy (𝟙 _) r hr
    (fun n => (hbase n).trans (Category.comp_id _).symm) r₀ hclosed ?_ ?_
  · intro A f hfbase hfres
    obtain ⟨α, hα⟩ := exists_completeLocalAlgHom_of_specMap iΛ η.base A f hfbase
      (hfres.trans hκ)
    exact ⟨α, (Category.comp_id _).trans hα⟩
  · intro A α β h
    apply CompleteLocalAlgCat.Hom.ext
    apply AlgHom.coe_ringHom_injective
    have h' := (Category.comp_id _).symm.trans (h.trans (Category.comp_id _))
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')

end Lifting

/-! ### Moving versality to the local ring of the base -/

section Stalk

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- A morphism conjugated by comparison isomorphisms is any morphism heterogeneously equal to
it. -/
theorem eqToHom_comp_comp_eqToHom_of_heq {C : Type*} [Category C] {X X₁ X₂ Y Y₁ Y₂ : C}
    (e₁ : X₂ = X₁) (e₂ : X₁ = X) (f : X ⟶ Y) (e₃ : Y = Y₁) (e₄ : Y₁ = Y₂)
    (g : X₂ ⟶ Y₂) (h : HEq f g) :
    eqToHom e₁ ≫ (eqToHom e₂ ≫ f ≫ eqToHom e₃) ≫ eqToHom e₄ = g := by
  subst e₁ e₂ e₃ e₄
  simpa using eq_of_heq h

/-- The inclusion of the `n`-th infinitesimal thickening of a complete local algebra is the
spectrum of the quotient map onto its `n`-th adic truncation. -/
theorem adicThickeningι_heq_specMap_truncation {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] (A : CompleteLocalAlgCat.{u, u, u} Λ k) (n : ℕ) :
    HEq (adicThickeningι A (maximalIdeal A) n)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (AdicTruncation.ideal A n)))) :=
  HEq.rfl

/-- The morphism of schemes underlying a morphism of `𝒳` does not depend on the identifications of
its endpoints, up to the comparison isomorphisms between them. -/
theorem schemeMap_congr {T : Scheme.{u}} {X : Type*} [Category X] (q : X ⥤ Over T) {y z : X}
    {Y Y' Z Z' : Over T} (hy : q.obj y = Y) (hy' : q.obj y = Y') (hz : q.obj z = Z)
    (hz' : q.obj z = Z') (f : y ⟶ z) :
    schemeMap q hy hz f = eqToHom (congrArg Over.left (hy.symm.trans hy')) ≫
      schemeMap q hy' hz' f ≫ eqToHom (congrArg Over.left (hz'.symm.trans hz)) := by
  subst hy hz
  simp [schemeMap]

/-- A morphism followed by a comparison isomorphism is any morphism heterogeneously equal to
it. -/
theorem comp_eqToHom_eq_of_heq {C : Type*} [Category C] {X Y Y' : C} (f : X ⟶ Y) (e : Y = Y')
    (g : X ⟶ Y') (h : HEq f g) : f ≫ eqToHom e = g := by
  subst e
  simpa using eq_of_heq h

/-- The arrow of a deformation lies over the residue map of its algebra. -/
theorem DeformationObject.schemeMap_arrow {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {iΛ : Spec (.of Λ) ⟶ S} {q : F ⥤ Over S} {x₀ : F}
    {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (d : DeformationObject iΛ q x₀ hx₀) {A₀ : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (h : d.algebra = A₀)
    (hb : q.obj d.point = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A₀)) ≫ iΛ)) :
    schemeMap q hx₀ hb d.arrow = Spec.map (CommRingCat.ofHom (residueMap A₀)) := by
  rcases d with ⟨alg, pt, ar, bs, ab⟩
  dsimp only at h
  subst h
  exact ab

/-- The lifting property only depends on the object of `Over S` through its underlying scheme. -/
theorem liftsAtResiduePoint_congr {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (q : F ⥤ Over S) {U U' : Over S} (hU : U = U') (x : F)
    (hx : q.obj x = U) (κ : Spec (.of k) ⟶ U.left) :
    LiftsAtResiduePoint iΛ q U x hx κ ↔
      LiftsAtResiduePoint iΛ q U' x (hx.trans hU) (κ ≫ eqToHom (congrArg Over.left hU)) := by
  subst hU
  simp

/-- **A versal formal object of a predeformation category over an affine chart gives a formal
object over the site which is versal over the local ring of the base.** Let `ξ` be a versal formal
object of the predeformation category of `x₀` over `𝒞_Λ`, for an affine open `Spec Λ ⊆ S`, and let
`y` realize its formal object over the site. Then that formal object over the site is versal in the
sense of **Stacks 0CXJ** with the local ring `𝒪_{S,s}` at the image `s` of the closed point as
deformation base. -/
theorem isVersal_stalk_ofPredeformation_of_realization [IsLocallyNoetherian S]
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ] {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (predeformationCategory_isPredeformationCategory
      B hS iΛ p x₀ hx₀ hp).cofibered ξ)
    {hA : B.Contains (Spec (.of ξ.base))} {y : F}
    {hy : p.obj y = baseOver B S hS (completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (R : (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ).Realization hA y hy)
    (s : S) (hs : (completeLocalAlgFormalBase iΛ hfinite ξ.base).toS
      (closedPoint ξ.base) = s) [algA : Algebra (S.presheaf.stalk s) ξ.base]
    (hΛ : Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) ξ.base)) ≫
      S.fromSpecStalk s = (completeLocalAlgFormalBase iΛ hfinite ξ.base).toS) :
    @FormalObject.IsVersal B S hS F _ p hp
      (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ)
      (S.presheaf.stalk s) _ algA (S.fromSpecStalk s) hΛ := by
  have qY : (p ⋙ Over.post B.inclusion).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ) :=
    congrArg (Over.post B.inclusion).obj hy
  have hbaseξ : ∀ n, eqToHom (congrArg Over.left (deformationPointBase
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀) (ξ.level n)
      (AdicTruncation.obj ξ.base n) (ξ.level_eq n))).symm ≫
      ((p ⋙ Over.post B.inclusion).map (R.r n)).left ≫ eqToHom (congrArg Over.left qY) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n))) := by
    intro n
    show eqToHom _ ≫ (p.map (R.r n)).left.hom ≫ eqToHom _ = _
    rw [R.map_eq n, bigFppfOver_left_hom_eqToHom]
    exact eqToHom_comp_comp_eqToHom_of_heq _ _ _ _ _ _
      (adicThickeningι_heq_specMap_truncation ξ.base n)
  let C := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let := C.category
  let r₀ : x₀ ⟶ y := (C.objects (ξ.level 0)).arrow ≫ R.r 0
  have hclosedξ : ∀ n, (C.objects (ξ.level n)).arrow ≫ R.r n = r₀ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      calc (C.objects (ξ.level (n + 1))).arrow ≫ R.r (n + 1)
          = ((C.objects (ξ.level n)).arrow ≫ (C.morphisms _ _ (ξ.transition n)).arrow) ≫
              R.r (n + 1) :=
            congrArg (· ≫ R.r (n + 1)) (C.morphisms _ _ (ξ.transition n)).triangle.symm
        _ = (C.objects (ξ.level n)).arrow ≫ ((C.morphisms _ _ (ξ.transition n)).arrow ≫
              R.r (n + 1)) := Category.assoc _ _ _
        _ = (C.objects (ξ.level n)).arrow ≫ R.r n :=
            congrArg ((C.objects (ξ.level n)).arrow ≫ ·) (R.comp_transition n)
        _ = r₀ := ih
  have hκξ : schemeMap (p ⋙ Over.post B.inclusion) hx₀ qY r₀ =
      Spec.map (CommRingCat.ofHom (completeResidueMap ξ.base)) := by
    have hb0 := deformationPointBase C (ξ.level 0) (AdicTruncation.obj ξ.base 0) (ξ.level_eq 0)
    refine (schemeMap_comp _ hx₀ hb0 qY _ _).trans ?_
    refine (congrArg (· ≫ _) (DeformationObject.schemeMap_arrow S
      (C.objects (ξ.level 0)) ((C.object_projection _).symm.trans (ξ.level_eq 0)) hb0)).trans ?_
    refine (congrArg (_ ≫ ·) (hbaseξ 0)).trans ?_
    refine (Spec.map_comp (CommRingCat.ofHom (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base 0)))
      (CommRingCat.ofHom (residueMap (AdicTruncation.obj ξ.base 0)))).symm.trans ?_
    congr 1
    ext a
    exact AdicTruncation.residueEquiv_residue_mk ξ.base 0 a
  have hliftξ := (liftsAtResiduePoint_iff_isVersal_of_realizing B S hS p hp hx₀ ξ qY R.r
    R.comp_transition hbaseξ r₀ hclosedξ hκξ).mpr hξ
  have hlift₁ := (liftsAtResiduePoint_iff_changeResidueField ξ.base.residueEquiv.symm iΛ
    (p ⋙ Over.post B.inclusion) _ y qY _).mp hliftξ
  have hκ₁ : Spec.map (CommRingCat.ofHom ξ.base.residueEquiv.symm.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (completeResidueMap ξ.base)) =
      Spec.map (CommRingCat.ofHom (residue ξ.base)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp [completeResidueMap]
  rw [hκ₁] at hlift₁
  have hlocA : IsLocalHom (algebraMap (S.presheaf.stalk s) ξ.base) := by
    rw [isLocalHom_iff_comap_closedPoint]
    apply (S.fromSpecStalk s).isEmbedding.injective
    have h1 : (S.fromSpecStalk s) (closedPoint (S.presheaf.stalk s)) = s :=
      Scheme.fromSpecStalk_closedPoint
    refine Eq.trans ?_ (hs.trans h1.symm)
    rw [← hΛ]
    rfl
  let algRes : Algebra (S.presheaf.stalk s) (ResidueField ξ.base) := inferInstance
  have hstalkRes : algebraMap (S.presheaf.stalk s) (ResidueField ξ.base) =
      (residue ξ.base).comp (algebraMap (S.presheaf.stalk s) ξ.base) :=
    IsScalarTower.algebraMap_eq _ _ _
  have hlocRes : IsLocalHom (algebraMap (S.presheaf.stalk s) (ResidueField ξ.base)) := by
    rw [hstalkRes]
    exact RingHom.isLocalHom_comp _ _
  have hres₁ : Spec.map (CommRingCat.ofHom (residue ξ.base)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) ξ.base)) =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) (ResidueField ξ.base))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hstalkRes]
  have hκS : Spec.map (CommRingCat.ofHom (residue ξ.base)) ≫
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ)).hom =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) (ResidueField ξ.base))) ≫
        S.fromSpecStalk s := by
    show _ ≫ (completeLocalAlgFormalBase iΛ hfinite ξ.base).toS = _
    rw [← hΛ]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ S.fromSpecStalk s) hres₁)
  obtain ⟨g, hg⟩ := exists_ringHom_comp_fromSpecStalk_of_isOpenImmersion iΛ
    ((Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base))) (closedPoint ξ.base)) s hs
  have hcompat : Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ξ.base))) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) (ResidueField ξ.base))) ≫
        S.fromSpecStalk s := by
    rw [← hκS, IsScalarTower.algebraMap_eq Λ ξ.base (ResidueField ξ.base),
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  have hk := algebraMap_eq_comp_of_specMap_eq (k := ResidueField ξ.base) iΛ g hg hcompat
  have hliftS := (liftsAtResiduePoint_iff_affineOpenBase (k := ResidueField ξ.base) iΛ s
    (p ⋙ Over.post B.inclusion) _ y qY _ hlocRes hκS g hg hk).mpr hlift₁
  have hU : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ) : Over S) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) ξ.base)) ≫
        S.fromSpecStalk s) := congrArg Over.mk hΛ.symm
  have hliftU := (@liftsAtResiduePoint_congr S F _ (S.presheaf.stalk s) (ResidueField ξ.base) _ _
    algRes (S.fromSpecStalk s) (p ⋙ Over.post B.inclusion) _ _ hU y qY _).mp hliftS
  simp only [eqToHom_refl, Category.comp_id] at hliftU
  let algA' : Algebra (S.presheaf.stalk s)
      (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ).base.R := algA
  have hb0 := deformationPointBase (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (ξ.level 0) (AdicTruncation.obj ξ.base 0) (ξ.level_eq 0)
  have hκ0 : ∀ (h₀ : (p ⋙ Over.post B.inclusion).obj
        ((FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ).level 0) =
        Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk s) (ResidueField ξ.base))) ≫ S.fromSpecStalk s)),
      schemeMap (p ⋙ Over.post B.inclusion) h₀ (qY.trans hU) (R.r 0) =
        Spec.map (CommRingCat.ofHom (residue ξ.base)) := by
    intro h₀
    refine (schemeMap_congr (p ⋙ Over.post B.inclusion) h₀ hb0 (qY.trans hU) qY (R.r 0)).trans ?_
    refine (congrArg (fun t => eqToHom _ ≫ t ≫ eqToHom _) (hbaseξ 0)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine comp_eqToHom_eq_of_heq _ _ _ (heq_of_eq ?_)
    exact quotientSpecMap_eqToHom ξ.base (pow_one (maximalIdeal ξ.base)) _
  refine (liftsAtResiduePoint_iff_isVersal_of_realizing B S hS p hp
    (@FormalObject.basePoint B S hS F _ p
      (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ)
      (S.presheaf.stalk s) _ algA (S.fromSpecStalk s) hΛ)
    (@FormalObject.predeformationFormalObject B S hS F _ p
      (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ)
      (S.presheaf.stalk s) _ algA (S.fromSpecStalk s) hΛ) (qY.trans hU) R.r R.comp_transition
    (fun n => hbaseξ n) (R.r 0)
    (fun n => closedPointArrow_restriction _ R.r R.comp_transition n) (hκ0 _)).mp hliftU

end Stalk

end Deformation.Artin

end
