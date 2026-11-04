module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSourceFull
public import StacksFrontier.Deformation.Examples.Geometric.SpecialFibreThickening

/-!
# Lifting a vertical arrow of deformations of the source, and fullness

[Stacks, Tag 0E3X] asserts that `Deformation.Examples.schemeMorphismSourceForgetful` is an
equivalence.  `Deformation.Examples.schemeMorphismSourceForgetful_full_of_lift_of_isHomLift_id`
reduces fullness to one vertical statement: two deformations `R`, `Q` of `f : X ⟶ Y` over the
same object of `𝒞_Λ`, together with an arrow `θ` of the induced deformations of `X` lying over
an identity, are joined by an arrow `R ⟶ Q` of deformations of `f`.  This file proves that
statement, hence fullness.

## Main definitions

* `AlgebraicGeometry.Scheme.isoOfPushforwardStructureSheaf` — **two schemes whose structure
  sheaves are the same direct image of one structure sheaf are isomorphic.**

## Main results

* `Deformation.Examples.schemeMorphismSourceForgetful_exists_lift_of_isHomLift_id` — the
  vertical lifting statement.
* `Deformation.Examples.schemeMorphismSourceForgetful_full_of_specialFibre` — **[Stacks, Tag
  0E3X], the fullness half.**

## Implementation notes

The whole content is the target component `Q.target ⟶ R.target`, which the functor forgets, and
it is built from the two facts recorded in
`StacksFrontier/Deformation/Examples/Geometric/SpecialFibreThickening.lean`: both target families
have the underlying space of `Y`, and the structure sheaf of each is the direct image of the
structure sheaf of its source family.  So the component is a morphism of schemes assembled from
a homeomorphism of underlying spaces and a map of structure sheaves, and that assembly is
isolated here as `AlgebraicGeometry.Scheme.isoOfPushforwardStructureSheaf`.

That general statement is phrased for two morphisms `m : S ⟶ A` and `u : S ⟶ B` out of a common
scheme, each inducing an invertible comparison `𝒪 ⟶ (·)_* 𝒪_S`, whose underlying maps agree
through a homeomorphism `β : |A| ≅ |B|`.  The resulting morphism `A ⟶ B` is then an
*isomorphism*, because the comparison it is built from is a composite of isomorphisms; so no
locality argument on stalks is needed at all —
`AlgebraicGeometry.LocallyRingedSpace.isoOfSheafedSpaceIso` supplies it.  This is why the
construction does not reuse `Stacks.Thickenings.Realization.map`, whose own work is exactly the
locality argument for a morphism that need not be invertible, and which in any case applies only
to realizations of a square-zero extension while the target families here are thickenings of
arbitrary order.

In the application `m` is `Q.morphism`, `u` is `θ.map ≫ R.morphism`, and `β` is the
homeomorphism `|Q.target| ≅ |Y| ≅ |R.target|`; `θ.map` is invertible because `θ` lies over an
identity of `𝒞_Λ`, so its cartesian square has an invertible right edge.  The two remaining
compatibilities of the arrow of deformations — with the identifications of the special fibre,
and with the structure morphisms to the base — are equalities of morphisms out of `Q.target`,
and both are proved the way faithfulness is: the underlying maps of spaces agree because the
identification of the special fibre is surjective on points
(`Deformation.Examples.specialTarget_surjective`), and the maps on sections then agree by
`AlgebraicGeometry.Scheme.Hom.eq_of_comp_eq_of_mono_app`.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The comparison of structure sheaves of a morphism of schemes is invertible on sections**
once it is invertible as a morphism of sheaves of modules: an invertible morphism of sheaves of
modules is invertible on sections over each open, and the map it induces there is the comorphism
of the morphism of schemes. -/
theorem Scheme.isIso_app_of_isIso_unitToPushforwardUnit {W Z : Scheme.{u}} (g : W ⟶ Z)
    (h : IsIso (C := Z.Modules) (Scheme.Modules.unitToPushforwardUnit g)) (O : Z.Opens) :
    IsIso (g.app O) := by
  have := h
  exact (ConcreteCategory.isIso_iff_bijective (g.app O)).mpr
    (ConcreteCategory.bijective_of_isIso
      ((Scheme.Modules.unitToPushforwardUnit g).app O))

/-- The comparison of structure sheaves of a morphism of schemes is invertible as soon as it is
invertible over every open: a morphism of presheaves invertible in each component is
invertible. -/
theorem Scheme.isIso_c_of_isIso_app {W Z : Scheme.{u}} (g : W ⟶ Z)
    (h : ∀ O : Z.Opens, IsIso (g.app O)) : IsIso g.c :=
  have : ∀ U : (Z.Opens)ᵒᵖ, IsIso (g.c.app U) := fun U => h U.unop
  NatIso.isIso_of_isIso_app g.c

/-- A morphism of schemes from a homeomorphism of the underlying spaces together with an
invertible comparison of structure sheaves along it.  Such data is an isomorphism of sheafed
spaces, hence of locally ringed spaces, hence of schemes. -/
def Scheme.isoOfComponents {A B : Scheme.{u}} (β : (A : TopCat.{u}) ⟶ (B : TopCat.{u}))
    (c : B.presheaf ⟶ β _* A.presheaf) [IsIso β] [IsIso c] : A ≅ B :=
  let e : A.toLocallyRingedSpace ≅ B.toLocallyRingedSpace :=
    LocallyRingedSpace.isoOfSheafedSpaceIso
      (SheafedSpace.isoMk (PresheafedSpace.isoOfComponents (asIso β) (asIso c).symm))
  { hom := Scheme.Hom.mk e.hom
    inv := Scheme.Hom.mk e.inv
    hom_inv_id := Scheme.Hom.ext' e.hom_inv_id
    inv_hom_id := Scheme.Hom.ext' e.inv_hom_id }

/-- The underlying map of spaces of `Scheme.isoOfComponents β c` is `β`. -/
@[simp]
theorem Scheme.isoOfComponents_hom_base {A B : Scheme.{u}}
    (β : (A : TopCat.{u}) ⟶ (B : TopCat.{u})) (c : B.presheaf ⟶ β _* A.presheaf)
    [IsIso β] [IsIso c] : (Scheme.isoOfComponents β c).hom.base = β :=
  rfl

/-- The map of structure sheaves of `Scheme.isoOfComponents β c` is `c`. -/
@[simp]
theorem Scheme.isoOfComponents_hom_c {A B : Scheme.{u}}
    (β : (A : TopCat.{u}) ⟶ (B : TopCat.{u})) (c : B.presheaf ⟶ β _* A.presheaf)
    [IsIso β] [IsIso c] : (Scheme.isoOfComponents β c).hom.c = c :=
  rfl

/-- The comparison `u_* 𝒪_S ≅ β _* 𝒪_A` attached to a morphism `m : S ⟶ A` with invertible
comparison of structure sheaves and a homeomorphism `β` identifying `m` with `u` on underlying
spaces: transport along that identification, read the result as an iterated direct image,
and invert the comparison of `m` pushed forward along `β`. -/
def Scheme.pushforwardStructureSheafComparison {S A B : Scheme.{u}} (m : S ⟶ A) (u : S ⟶ B)
    (β : (A : TopCat.{u}) ⟶ (B : TopCat.{u})) (hβ : m.base ≫ β = u.base) [IsIso m.c] :
    (u.base _* S.presheaf) ≅ (β _* A.presheaf) :=
  (TopCat.Presheaf.pushforwardEq hβ.symm S.presheaf).trans
    ((TopCat.Presheaf.Pushforward.comp m.base β S.presheaf).trans
      (asIso ((TopCat.Presheaf.pushforward CommRingCat.{u} β).map m.c)).symm)

/-- Composing the comparison with the direct image of the comparison of `m` leaves only the
transport along the identification of the two underlying maps. -/
theorem Scheme.pushforwardStructureSheafComparison_hom_comp {S A B : Scheme.{u}} (m : S ⟶ A)
    (u : S ⟶ B) (β : (A : TopCat.{u}) ⟶ (B : TopCat.{u})) (hβ : m.base ≫ β = u.base)
    [IsIso m.c] :
    (Scheme.pushforwardStructureSheafComparison m u β hβ).hom ≫
        (TopCat.Presheaf.pushforward CommRingCat.{u} β).map m.c =
      (TopCat.Presheaf.pushforwardEq hβ.symm S.presheaf).hom ≫
        (TopCat.Presheaf.Pushforward.comp m.base β S.presheaf).hom := by
  rw [Scheme.pushforwardStructureSheafComparison, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **Two schemes whose structure sheaves are the same direct image of one structure sheaf are
isomorphic.**  Let `m : S ⟶ A` and `u : S ⟶ B` both exhibit the structure sheaf of their target
as the direct image of `𝒪_S`, and let `β` be a homeomorphism of the underlying spaces of `A` and
`B` through which the two underlying maps agree.  Then `β` and the comparison of structure
sheaves assemble to an isomorphism `A ≅ B`. -/
def Scheme.isoOfPushforwardStructureSheaf {S A B : Scheme.{u}} (m : S ⟶ A) (u : S ⟶ B)
    (β : (A : TopCat.{u}) ⟶ (B : TopCat.{u})) (hβ : m.base ≫ β = u.base)
    [IsIso β] [IsIso m.c] [IsIso u.c] : A ≅ B :=
  Scheme.isoOfComponents β
    (u.c ≫ (Scheme.pushforwardStructureSheafComparison m u β hβ).hom)

/-- The underlying map of spaces of `Scheme.isoOfPushforwardStructureSheaf m u β hβ` is `β`. -/
@[simp]
theorem Scheme.isoOfPushforwardStructureSheaf_hom_base {S A B : Scheme.{u}} (m : S ⟶ A)
    (u : S ⟶ B) (β : (A : TopCat.{u}) ⟶ (B : TopCat.{u})) (hβ : m.base ≫ β = u.base)
    [IsIso β] [IsIso m.c] [IsIso u.c] :
    (Scheme.isoOfPushforwardStructureSheaf m u β hβ).hom.base = β :=
  rfl

/-- The isomorphism built from a shared direct image of a structure sheaf is a morphism under
the common source. -/
theorem Scheme.comp_isoOfPushforwardStructureSheaf_hom {S A B : Scheme.{u}} (m : S ⟶ A)
    (u : S ⟶ B) (β : (A : TopCat.{u}) ⟶ (B : TopCat.{u})) (hβ : m.base ≫ β = u.base)
    [IsIso β] [IsIso m.c] [IsIso u.c] :
    m ≫ (Scheme.isoOfPushforwardStructureSheaf m u β hβ).hom = u := by
  have hbase : (m ≫ (Scheme.isoOfPushforwardStructureSheaf m u β hβ).hom).base = u.base := by
    rw [Scheme.Hom.comp_base, Scheme.isoOfPushforwardStructureSheaf_hom_base]
    exact hβ
  refine Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (PresheafedSpace.ext _ _ hbase ?_))
  refine NatTrans.ext (funext fun U => ?_)
  have hc : (Scheme.pushforwardStructureSheafComparison m u β hβ).hom.app U ≫
      ((TopCat.Presheaf.pushforward CommRingCat.{u} β).map m.c).app U =
      (TopCat.Presheaf.pushforwardEq hβ.symm S.presheaf).hom.app U := by
    rw [← NatTrans.comp_app, Scheme.pushforwardStructureSheafComparison_hom_comp,
      NatTrans.comp_app, TopCat.Presheaf.Pushforward.comp_hom_app]
    exact Category.comp_id _
  have hlhs :
      ((m ≫ (Scheme.isoOfPushforwardStructureSheaf m u β hβ).hom).c).app U =
        u.c.app U ≫ (TopCat.Presheaf.pushforwardEq hβ.symm S.presheaf).hom.app U := by
    rw [show ((m ≫ (Scheme.isoOfPushforwardStructureSheaf m u β hβ).hom).c).app U =
        (u.c.app U ≫ (Scheme.pushforwardStructureSheafComparison m u β hβ).hom.app U) ≫
          ((TopCat.Presheaf.pushforward CommRingCat.{u} β).map m.c).app U from rfl,
      Category.assoc, hc]
    rfl
  rw [NatTrans.comp_app, hlhs, Functor.whiskerRight_app]
  refine (Category.assoc _ _ _).trans
    (Eq.trans (congrArg (fun z => u.c.app U ≫ z) ?_) (Category.comp_id _))
  rw [TopCat.Presheaf.pushforwardEq_hom_app]
  exact (S.presheaf.map_comp _ _).symm.trans
    ((congrArg S.presheaf.map (Subsingleton.elim _ (𝟙 _))).trans (S.presheaf.map_id _))

/-- Two equal morphisms of schemes induce the same map of underlying spaces. -/
theorem Scheme.Hom.congr_base {V W : Scheme.{u}} {a b : V ⟶ W} (h : a = b) :
    a.base = b.base :=
  congrArg (fun g : V ⟶ W => g.base) h

end AlgebraicGeometry

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- The identification of the special fibre of the target family of a deformation of `f` is an
isomorphism of underlying spaces: it is a thickening. -/
theorem isIso_specialTarget_base (Q : schemeMorphismDeformationCategory f pX pY hf) :
    IsIso Q.hom.target.base :=
  (TopCat.isIso_iff_isHomeomorph _).mpr (isHomeomorph_specialTarget f pX pY hf Q)

/-- The identification of the special fibre of the source family of a deformation of `f` is an
isomorphism of underlying spaces: it is a thickening. -/
theorem isIso_specialSource_base (Q : schemeMorphismDeformationCategory f pX pY hf) :
    IsIso Q.hom.source.base :=
  (TopCat.isIso_iff_isHomeomorph _).mpr (isHomeomorph_specialSource f pX pY hf Q)

section Vertical

variable {R Q : schemeMorphismDeformationCategory f pX pY hf}
  (θ : (schemeMorphismSourceForgetful f pX pY hf).obj R ⟶
    (schemeMorphismSourceForgetful f pX pY hf).obj Q)

/-- The cartesian square carried by an arrow of deformations of `X` between the images of two
deformations of `f`, spelled in terms of the source families. -/
theorem forgetfulSource_cartesian :
    IsPullback θ.map Q.left.sourceToBase R.left.sourceToBase (baseSpecMap θ.base) :=
  θ.cartesian

/-- The compatibility with the identifications of the special fibre carried by an arrow of
deformations of `X` between the images of two deformations of `f`. -/
theorem forgetfulSource_special_compat : Q.hom.source ≫ θ.map = R.hom.source :=
  θ.special_compat

/-- An arrow of deformations of `X` lying over an identity of `𝒞_Λ` has invertible component on
bases: the lifting condition exhibits it as a composite of transports. -/
theorem isIso_base_of_isHomLift_id
    (hθ : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).IsHomLift
      (𝟙 ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).obj
        ((schemeMorphismSourceForgetful f pX pY hf).obj Q))) θ) : IsIso θ.base := by
  have := hθ
  have hfac := IsHomLift.fac'
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
    (𝟙 ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).obj
      ((schemeMorphismSourceForgetful f pX pY hf).obj Q))) θ
  have h : IsIso ((schemeDeformationCategoryProjection (Λ := Λ) (k := k)
      (Over.mk pX)).map θ) := by
    rw [hfac]
    infer_instance
  exact h

/-- An arrow of deformations of `X` lying over an identity of `𝒞_Λ` is invertible on the total
spaces: its cartesian square has an invertible right edge. -/
theorem isIso_map_of_isHomLift_id
    (hθ : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).IsHomLift
      (𝟙 ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).obj
        ((schemeMorphismSourceForgetful f pX pY hf).obj Q))) θ) : IsIso θ.map := by
  have hb : IsIso θ.base := isIso_base_of_isHomLift_id f pX pY hf θ hθ
  exact (forgetfulSource_cartesian f pX pY hf θ).isIso_fst_of_isIso
    (isIso_baseSpecMap θ.base)

end Vertical

/-- **[Stacks, Tag 0E3X], the vertical lifting statement.**  Let `f_*𝒪_X = 𝒪_Y` and
`R¹f_*𝒪_X = 0`.  Then two deformations `R`, `Q` of `f` and an arrow `θ` of the deformations of
`X` they induce, lying over an identity of `𝒞_Λ`, are joined by an arrow `R ⟶ Q` of
deformations of `f` whose image is `θ`.

Lying over an identity makes `θ.base` invertible, hence `θ.map` invertible, being the first
edge of a cartesian square whose opposite edge is the spectrum of `θ.base`.  The target
component is then `AlgebraicGeometry.Scheme.isoOfPushforwardStructureSheaf` applied to
`Q.morphism` and to `θ.map ≫ R.morphism`: both exhibit the structure sheaf of their target as
the direct image of the structure sheaf of `Q.source`
(`Deformation.Examples.isIso_unitToPushforwardUnit_of_deformation`), and their underlying maps
agree through the homeomorphism of `|Q.target|` with `|R.target|` that the two identifications
of the special fibre provide.

**No `@[stacks 0E3X]` attribute**: the tag asserts that the functor is an equivalence, and
essential surjectivity is not proved here. -/
theorem schemeMorphismSourceForgetful_exists_lift_of_isHomLift_id
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit f))
    (hR : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (R Q : schemeMorphismDeformationCategory f pX pY hf)
    (θ : (schemeMorphismSourceForgetful f pX pY hf).obj R ⟶
      (schemeMorphismSourceForgetful f pX pY hf).obj Q)
    (hθ : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).IsHomLift
      (𝟙 ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).obj
        ((schemeMorphismSourceForgetful f pX pY hf).obj Q))) θ) :
    ∃ ψ : R ⟶ Q, (schemeMorphismSourceForgetful f pX pY hf).map ψ = θ := by
  -- read off the data of `θ` in the spelling of the two families of morphisms
  have hb0 : IsIso θ.base := isIso_base_of_isHomLift_id f pX pY hf θ hθ
  obtain ⟨b, t, hbiso, htiso, hbsiso, htcart, hsc, hfun⟩ :
      ∃ (b : R.left.base ⟶ Q.left.base) (t : Q.left.source ⟶ R.left.source),
        IsIso b ∧ IsIso t ∧ IsIso (baseSpecMap b) ∧
        IsPullback t Q.left.sourceToBase R.left.sourceToBase (baseSpecMap b) ∧
        Q.hom.source ≫ t = R.hom.source ∧
        ∀ ψ : R ⟶ Q, ψ.left.base = b → ψ.left.source = t →
          (schemeMorphismSourceForgetful f pX pY hf).map ψ = θ :=
    ⟨θ.base, θ.map, hb0, isIso_map_of_isHomLift_id f pX pY hf θ hθ,
      isIso_baseSpecMap θ.base, forgetfulSource_cartesian f pX pY hf θ,
      forgetfulSource_special_compat f pX pY hf θ,
      fun _ h₁ h₂ => SchemeDeformationCategory.Hom.ext h₁ h₂⟩
  have := hbiso
  have := htiso
  have := hbsiso
  -- read off the identifications of the special fibres as morphisms out of `X` and `Y`
  obtain ⟨qs, qt, rs, rt, hqsiso, hqtiso, hrtiso, hqtsurj, hQsq, hRsq, hQtsq, hRtsq,
      htsc, hconc⟩ :
      ∃ (qs : X ⟶ Q.left.source) (qt : Y ⟶ Q.left.target)
        (rs : X ⟶ R.left.source) (rt : Y ⟶ R.left.target),
        IsIso qs.base ∧ IsIso qt.base ∧ IsIso rt.base ∧ Function.Surjective qt ∧
        f ≫ qt = qs ≫ Q.left.morphism ∧ f ≫ rt = rs ≫ R.left.morphism ∧
        qt ≫ Q.left.targetToBase = pY ≫ baseSpecMap Q.hom.base ∧
        rt ≫ R.left.targetToBase = pY ≫ baseSpecMap R.hom.base ∧
        qs ≫ t = rs ∧
        (∀ φ : Q.left.target ⟶ R.left.target, qt ≫ φ = rt →
          Q.hom.target ≫ φ = R.hom.target) :=
    ⟨Q.hom.source, Q.hom.target, R.hom.source, R.hom.target,
      isIso_specialSource_base f pX pY hf Q, isIso_specialTarget_base f pX pY hf Q,
      isIso_specialTarget_base f pX pY hf R, specialTarget_surjective f pX pY hf Q,
      Q.hom.source_pullback.w, R.hom.source_pullback.w,
      Q.hom.target_pullback.w, R.hom.target_pullback.w, hsc, fun _ h => h⟩
  have := hqsiso
  have := hqtiso
  have := hrtiso
  -- the comparisons of structure sheaves are invertible
  have hu : ∀ D : schemeMorphismDeformationCategory f pX pY hf,
      IsIso (C := D.left.target.Modules)
        (Scheme.Modules.unitToPushforwardUnit D.left.morphism) :=
    isIso_unitToPushforwardUnit_of_deformation f pX pY hf h0 hR
  have hc : ∀ D : schemeMorphismDeformationCategory f pX pY hf, IsIso D.left.morphism.c := fun D =>
    Scheme.isIso_c_of_isIso_app _ (Scheme.isIso_app_of_isIso_unitToPushforwardUnit _ (hu D))
  have := hc Q
  have := hc R
  have htc : IsIso t.c := PresheafedSpace.c_isIso_of_iso t.toPshHom
  have huc : IsIso (t ≫ R.left.morphism).c := inferInstanceAs (IsIso (R.left.morphism.c ≫
    (TopCat.Presheaf.pushforward CommRingCat.{u} R.left.morphism.base).map t.c))
  -- the two target families have the same underlying space
  have e1 : f.base ≫ qt.base = qs.base ≫ Q.left.morphism.base := Scheme.Hom.congr_base hQsq
  have e2 : f.base ≫ rt.base = rs.base ≫ R.left.morphism.base := Scheme.Hom.congr_base hRsq
  have e3 : qs.base ≫ t.base = rs.base := Scheme.Hom.congr_base htsc
  have hsq : Q.left.morphism.base ≫ (inv qt.base ≫ rt.base) = (t ≫ R.left.morphism).base := by
    rw [← cancel_epi qs.base, ← Category.assoc, ← e1, Scheme.Hom.comp_base, reassoc_of% e3, ← e2]
    simp
  -- the target component
  obtain ⟨φ, hφiso, hφbase, hmφ⟩ :
      ∃ φ : Q.left.target ⟶ R.left.target, IsIso φ ∧
        φ.base = inv qt.base ≫ rt.base ∧
        Q.left.morphism ≫ φ = t ≫ R.left.morphism :=
    ⟨(Scheme.isoOfPushforwardStructureSheaf Q.left.morphism (t ≫ R.left.morphism)
        (inv qt.base ≫ rt.base) hsq).hom, inferInstance,
      Scheme.isoOfPushforwardStructureSheaf_hom_base _ _ _ hsq,
      Scheme.comp_isoOfPushforwardStructureSheaf_hom _ _ _ hsq⟩
  have := hφiso
  -- compatibility with the identifications of the special fibre
  have hspecial : qt ≫ φ = rt := by
    refine Scheme.Hom.eq_of_comp_eq_of_mono_app f
      (fun W => mono_app_of_isIso_unitToPushforwardUnit f h0 W) ?_ ?_
    · rw [Scheme.Hom.comp_base, hφbase]
      simp
    · rw [reassoc_of% hQsq, hmφ, reassoc_of% htsc, hRsq]
  -- compatibility with the structure morphisms to the base
  have hpre : qt ≫ φ ≫ R.left.targetToBase =
      qt ≫ Q.left.targetToBase ≫ baseSpecMap b := by
    rw [reassoc_of% hspecial, hRtsq, reassoc_of% hQtsq]
    exact (congrArg (fun w => pY ≫ baseSpecMap w)
      ((isTerminal_residueFieldBase (Λ := Λ) (k := k)).hom_ext R.hom.base (b ≫ Q.hom.base))).trans
        (congrArg (pY ≫ ·) (baseSpecMap_comp b Q.hom.base))
  have htb : φ ≫ R.left.targetToBase = Q.left.targetToBase ≫ baseSpecMap b := by
    refine Scheme.Hom.eq_of_comp_eq_of_mono_app Q.left.morphism
      (fun W => mono_app_of_isIso_unitToPushforwardUnit Q.left.morphism (hu Q) W) ?_ ?_
    · refine TopCat.hom_ext (ContinuousMap.ext fun y => ?_)
      obtain ⟨z, rfl⟩ := hqtsurj y
      have e : (qt ≫ φ ≫ R.left.targetToBase) z =
          (qt ≫ Q.left.targetToBase ≫ baseSpecMap b) z := by rw [hpre]
      simpa using e
    · rw [reassoc_of% hmφ, R.left.over_base, htcart.w, ← Q.left.over_base, Category.assoc]
  exact ⟨Over.homMk
    { base := b
      source := t
      target := φ
      source_pullback := IsPullback.of_vert_isIso ⟨hmφ⟩
      target_pullback := IsPullback.of_horiz_isIso ⟨htb⟩ }
    (SchemeMorphismFamily.Hom.ext
      ((isTerminal_residueFieldBase (Λ := Λ) (k := k)).hom_ext _ _) hsc (hconc φ hspecial)),
    hfun _ rfl rfl⟩


/-- **[Stacks, Tag 0E3X], the fullness half.**  If `f_*𝒪_X = 𝒪_Y` and `R¹f_*𝒪_X = 0`, then the
source-forgetful functor on deformations of `f` is full.

`Deformation.Examples.schemeMorphismSourceForgetful_full_of_lift_of_isHomLift_id` reduces
fullness to the arrows lying over an identity of `𝒞_Λ`, which
`Deformation.Examples.schemeMorphismSourceForgetful_exists_lift_of_isHomLift_id` lifts.

**No `@[stacks 0E3X]` attribute**: the tag asserts that the functor is an equivalence, and
essential surjectivity is not proved here. -/
theorem schemeMorphismSourceForgetful_full_of_specialFibre
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit f))
    (hR : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    (schemeMorphismSourceForgetful f pX pY hf).Full :=
  schemeMorphismSourceForgetful_full_of_lift_of_isHomLift_id f pX pY hf
    fun R Q θ hθ =>
      schemeMorphismSourceForgetful_exists_lift_of_isHomLift_id f pX pY hf h0 hR R Q θ hθ

end Deformation.Examples

end
