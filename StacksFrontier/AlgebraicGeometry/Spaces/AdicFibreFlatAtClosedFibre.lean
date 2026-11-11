module

public import StacksFrontier.AlgebraicGeometry.AdicFibreFlatAtClosedFibreSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFibreSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePointwiseCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsFibreProductResidueIso

/-!
# Étaleness along the closed fibre from étaleness of the adic fibres

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `f : T ⟶ U` a morphism of algebraic spaces
over `S = Spec A`, locally of finite type, with `U` locally of finite type over `S`. If every
adic fibre `f_n : T_n ⟶ U_n` is étale, then `f` is étale on an open subspace of `T` containing the
closed fibre `T_0` (all the `T_n` have the same points).

This is the local criterion of flatness along the closed fibre in its étale form. In étale
charts `V ⟶ T`, `V' ⟶ U` at a point of the closed fibre, the scheme morphism `V ⟶ V'` has étale
base changes to all the thickenings `Spec (A / I^{n+1})`, so on affine opens `Spec C ⊆ V`,
`Spec D ⊆ V'` every `D / I^{n+1} D → C / I^{n+1} C` is étale; Stacks 0523 gives flatness of
`D → C` at the point, the first stage gives unramifiedness, and a map of finite presentation
which is flat and unramified at a prime is étale near it
(`AlgebraicGeometry.exists_isOpenImmersion_etale_of_forall_etale_pullbackMap`). The étale locus
of `f` is open, and its open subspace is the one sought.

## Main results

* `AlgebraicGeometry.Space.isEtaleAt_of_forall_isEtale_adicFibreMap`: `f` is étale at every
  point of `T` in the image of an adic fibre.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isEtale_of_forall_isEtale_adicFibreMap`: `f` is
  étale on an open subspace containing every adic fibre.
* `AlgebraicGeometry.Space.isFlatAt_of_forall_isFlat_adicFibreMap`: if every adic fibre of `f`
  is flat, `f` is flat at every point of the closed fibre.

## References

* [Stacks Project, Tag 0523](https://stacks.math.columbia.edu/tag/0523)
* [Stacks Project, Tag 00MK](https://stacks.math.columbia.edu/tag/00MK)
* [Stacks Project, Tag 0GHK](https://stacks.math.columbia.edu/tag/0GHK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}

local notation "𝒯" => BigFppfOver.toScheme B (Spec (CommRingCat.of A)) hS

/-- Every morphism of presheaves from a representable presheaf to the base is the image of a
morphism of the site, the base being terminal. -/
theorem eq_yoneda_map_of_baseObject {X : BigFppfOver B (Spec (.of A)) hS}
    (φ : yoneda.obj X ⟶ yoneda.obj (baseObject A B hS)) (k : X ⟶ baseObject A B hS) :
    φ = yoneda.map k := by
  rw [← yoneda.map_preimage φ, eq_of_hom_baseObject A B hS (yoneda.preimage φ) k]

/-- Étaleness of a base change morphism only depends on the first structure morphism up to
equality. -/
theorem etale_pullbackMap_of_eq {X Y S T : Scheme.{u}} (ι : T ⟶ S) (g : X ⟶ Y) (p : Y ⟶ S)
    (f f' : X ⟶ S) (hf : f = f') (e₁ : f ≫ 𝟙 S = g ≫ p) (e₁' : f' ≫ 𝟙 S = g ≫ p)
    (h : Etale (pullback.map f ι p ι g (𝟙 _) (𝟙 _) e₁ (by simp))) :
    Etale (pullback.map f' ι p ι g (𝟙 _) (𝟙 _) e₁' (by simp)) := by
  subst hf
  exact h

/-- Flatness of a base change morphism only depends on the first structure morphism up to
equality. -/
theorem flat_pullbackMap_of_eq {X Y S T : Scheme.{u}} (ι : T ⟶ S) (g : X ⟶ Y) (p : Y ⟶ S)
    (f f' : X ⟶ S) (hf : f = f') (e₁ : f ≫ 𝟙 S = g ≫ p) (e₁' : f' ≫ 𝟙 S = g ≫ p)
    (h : Flat (pullback.map f ι p ι g (𝟙 _) (𝟙 _) e₁ (by simp))) :
    Flat (pullback.map f' ι p ι g (𝟙 _) (𝟙 _) e₁' (by simp)) := by
  subst hf
  exact h

/-- **The adic fibres of a chart square are étale.** Let `a : V ⟶ T`, `b : V' ⟶ U` be étale
charts and `h : V ⟶ V'` a morphism of charts over `f : T ⟶ U`. If every adic fibre of `f` is
étale, then so is the base change of the scheme morphism underlying `h` to every adic
thickening. -/
theorem etale_pullbackMap_toScheme_of_forall_isEtale_adicFibreMap
    {T U : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    {fT : T ⟶ yoneda.obj (baseObject A B hS)} {fU : U ⟶ yoneda.obj (baseObject A B hS)}
    (f : T ⟶ U) (hf : f ≫ fU = fT)
    (het : ∀ n, IsEtale B _ hS (adicFibreMap A I B hS hSn f hf n))
    {V V' : BigFppfOver B (Spec (.of A)) hS} (a : yoneda.obj V ⟶ T) (b : yoneda.obj V' ⟶ U)
    (h : V ⟶ V')
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) 𝒯).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) 𝒯).presheaf b)
    (comm : yoneda.map h ≫ b = a ≫ f) (kU : V ⟶ baseObject A B hS)
    (kV : V' ⟶ baseObject A B hS) (n : ℕ) :
    Etale (pullback.map ((𝒯).map kU) ((𝒯).map (adicThickeningMap A I B hS hSn n)) ((𝒯).map kV)
      ((𝒯).map (adicThickeningMap A I B hS hSn n)) ((𝒯).map h) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ← Functor.map_comp, eq_of_hom_baseObject A B hS kU (h ≫ kV)])
      (by simp)) := by
  set thk := adicThickeningMap A I B hS hSn n
  have hkU : kU ≫ 𝟙 _ = h ≫ kV := by
    rw [Category.comp_id]
    exact eq_of_hom_baseObject A B hS _ _
  have haU : a ≫ fT = yoneda.map kU := eq_yoneda_map_of_baseObject _ _
  have hbV : b ≫ fU = yoneda.map kV := eq_yoneda_map_of_baseObject _ _
  let an : yoneda.obj (pullback kU thk) ⟶ adicFibre A I B hS hSn fT n :=
    pullback.lift (yoneda.map (pullback.fst kU thk) ≫ a) (yoneda.map (pullback.snd kU thk)) (by
      rw [Category.assoc, haU, ← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  let bn : yoneda.obj (pullback kV thk) ⟶ adicFibre A I B hS hSn fU n :=
    pullback.lift (yoneda.map (pullback.fst kV thk) ≫ b) (yoneda.map (pullback.snd kV thk)) (by
      rw [Category.assoc, hbV, ← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  have hstable := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) 𝒯) (F := yoneda)
  have sqa : IsPullback (yoneda.map (pullback.fst kU thk)) an a
      (pullback.fst fT (yoneda.map thk)) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback fT (yoneda.map thk))
    rw [pullback.lift_snd, haU]
    exact (IsPullback.of_hasPullback kU thk).map yoneda
  have sqb : IsPullback (yoneda.map (pullback.fst kV thk)) bn b
      (pullback.fst fU (yoneda.map thk)) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback fU (yoneda.map thk))
    rw [pullback.lift_snd, hbV]
    exact (IsPullback.of_hasPullback kV thk).map yoneda
  have han := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqa ha
  have hbn := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqb hb
  let hn := pullback.map kU thk kV thk h (𝟙 _) (𝟙 _) hkU (by simp)
  have hl : yoneda.map hn ≫ bn = an ≫ adicFibreMap A I B hS hSn f hf n := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, adicFibreMap_fst,
        pullback.lift_fst_assoc, ← Category.assoc, ← Functor.map_comp,
        show hn ≫ pullback.fst kV thk = pullback.fst kU thk ≫ h from pullback.lift_fst _ _ _,
        Functor.map_comp, Category.assoc, comm, Category.assoc]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, adicFibreMap_snd, pullback.lift_snd,
        ← Functor.map_comp,
        show hn ≫ pullback.snd kV thk = pullback.snd kU thk ≫ 𝟙 _ from pullback.lift_snd _ _ _,
        Category.comp_id]
  have hE : Etale ((𝒯).map hn) := etale_of_comp_etale_chart B _ hS (het n _ an han) hbn hl
  have : PreservesLimitsOfShape WalkingCospan (𝒯) :=
    preservesLimitsOfShape_walkingCospan_toScheme B _ hS
  have e : (PreservesPullback.iso (𝒯) kU thk).inv ≫ (𝒯).map hn ≫
      (PreservesPullback.iso (𝒯) kV thk).hom =
      pullback.map ((𝒯).map kU) ((𝒯).map thk) ((𝒯).map kV) ((𝒯).map thk) ((𝒯).map h) (𝟙 _)
        (𝟙 _) (by rw [Category.comp_id, ← Functor.map_comp,
          eq_of_hom_baseObject A B hS kU (h ≫ kV)])
        (by simp) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp,
        show hn ≫ pullback.fst kV thk = pullback.fst kU thk ≫ h from pullback.lift_fst _ _ _,
        Functor.map_comp, ← Category.assoc, PreservesPullback.iso_inv_fst]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Category.assoc, PreservesPullback.iso_hom_snd, ← Functor.map_comp,
        show hn ≫ pullback.snd kV thk = pullback.snd kU thk ≫ 𝟙 _ from pullback.lift_snd _ _ _,
        Category.comp_id, PreservesPullback.iso_inv_snd]
      exact ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm
  rw [← e]
  infer_instance

/-- **The adic fibres of a chart square are flat.** Let `a : V ⟶ T`, `b : V' ⟶ U` be étale
charts and `h : V ⟶ V'` a morphism of charts over `f : T ⟶ U`. If every adic fibre of `f` is
flat, then so is the base change of the scheme morphism underlying `h` to every adic
thickening. -/
theorem flat_pullbackMap_toScheme_of_forall_isFlat_adicFibreMap
    {T U : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    {fT : T ⟶ yoneda.obj (baseObject A B hS)} {fU : U ⟶ yoneda.obj (baseObject A B hS)}
    (f : T ⟶ U) (hf : f ≫ fU = fT)
    (hfl : ∀ n, IsFlat B _ hS (adicFibreMap A I B hS hSn f hf n))
    {V V' : BigFppfOver B (Spec (.of A)) hS} (a : yoneda.obj V ⟶ T) (b : yoneda.obj V' ⟶ U)
    (h : V ⟶ V')
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) 𝒯).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) 𝒯).presheaf b)
    (comm : yoneda.map h ≫ b = a ≫ f) (kU : V ⟶ baseObject A B hS)
    (kV : V' ⟶ baseObject A B hS) (n : ℕ) :
    Flat (pullback.map ((𝒯).map kU) ((𝒯).map (adicThickeningMap A I B hS hSn n)) ((𝒯).map kV)
      ((𝒯).map (adicThickeningMap A I B hS hSn n)) ((𝒯).map h) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ← Functor.map_comp, eq_of_hom_baseObject A B hS kU (h ≫ kV)])
      (by simp)) := by
  set thk := adicThickeningMap A I B hS hSn n
  have hkU : kU ≫ 𝟙 _ = h ≫ kV := by
    rw [Category.comp_id]
    exact eq_of_hom_baseObject A B hS _ _
  have haU : a ≫ fT = yoneda.map kU := eq_yoneda_map_of_baseObject _ _
  have hbV : b ≫ fU = yoneda.map kV := eq_yoneda_map_of_baseObject _ _
  let an : yoneda.obj (pullback kU thk) ⟶ adicFibre A I B hS hSn fT n :=
    pullback.lift (yoneda.map (pullback.fst kU thk) ≫ a) (yoneda.map (pullback.snd kU thk)) (by
      rw [Category.assoc, haU, ← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  let bn : yoneda.obj (pullback kV thk) ⟶ adicFibre A I B hS hSn fU n :=
    pullback.lift (yoneda.map (pullback.fst kV thk) ≫ b) (yoneda.map (pullback.snd kV thk)) (by
      rw [Category.assoc, hbV, ← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  have hstable := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) 𝒯) (F := yoneda)
  have sqa : IsPullback (yoneda.map (pullback.fst kU thk)) an a
      (pullback.fst fT (yoneda.map thk)) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback fT (yoneda.map thk))
    rw [pullback.lift_snd, haU]
    exact (IsPullback.of_hasPullback kU thk).map yoneda
  have sqb : IsPullback (yoneda.map (pullback.fst kV thk)) bn b
      (pullback.fst fU (yoneda.map thk)) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback fU (yoneda.map thk))
    rw [pullback.lift_snd, hbV]
    exact (IsPullback.of_hasPullback kV thk).map yoneda
  have han := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqa ha
  have hbn := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqb hb
  let hn := pullback.map kU thk kV thk h (𝟙 _) (𝟙 _) hkU (by simp)
  have hl : yoneda.map hn ≫ bn = an ≫ adicFibreMap A I B hS hSn f hf n := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, adicFibreMap_fst,
        pullback.lift_fst_assoc, ← Category.assoc, ← Functor.map_comp,
        show hn ≫ pullback.fst kV thk = pullback.fst kU thk ≫ h from pullback.lift_fst _ _ _,
        Functor.map_comp, Category.assoc, comm, Category.assoc]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, adicFibreMap_snd, pullback.lift_snd,
        ← Functor.map_comp,
        show hn ≫ pullback.snd kV thk = pullback.snd kU thk ≫ 𝟙 _ from pullback.lift_snd _ _ _,
        Category.comp_id]
  have hE : Flat ((𝒯).map hn) := hfl n _ _ an bn hn han hbn hl
  have : PreservesLimitsOfShape WalkingCospan (𝒯) :=
    preservesLimitsOfShape_walkingCospan_toScheme B _ hS
  have e : (PreservesPullback.iso (𝒯) kU thk).inv ≫ (𝒯).map hn ≫
      (PreservesPullback.iso (𝒯) kV thk).hom =
      pullback.map ((𝒯).map kU) ((𝒯).map thk) ((𝒯).map kV) ((𝒯).map thk) ((𝒯).map h) (𝟙 _)
        (𝟙 _) (by rw [Category.comp_id, ← Functor.map_comp,
          eq_of_hom_baseObject A B hS kU (h ≫ kV)])
        (by simp) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp,
        show hn ≫ pullback.fst kV thk = pullback.fst kU thk ≫ h from pullback.lift_fst _ _ _,
        Functor.map_comp, ← Category.assoc, PreservesPullback.iso_inv_fst]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Category.assoc, PreservesPullback.iso_hom_snd, ← Functor.map_comp,
        show hn ≫ pullback.snd kV thk = pullback.snd kU thk ≫ 𝟙 _ from pullback.lift_snd _ _ _,
        Category.comp_id, PreservesPullback.iso_inv_snd]
      exact ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm
  rw [← e]
  infer_instance

/-- **Étaleness at the points of the closed fibre.** Let `A` be Noetherian and `f : T ⟶ U` a
morphism of algebraic spaces over `Spec A`, locally of finite type, with `U` locally of finite
type over `Spec A`. If every adic fibre of `f` is étale, then `f` is étale at every point of `T`
in the image of an adic fibre. -/
theorem isEtaleAt_of_forall_isEtale_adicFibreMap [IsNoetherianRing A]
    {T U : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B _ hS T) (hU : IsAlgebraicSpace B _ hS U)
    {fT : T ⟶ yoneda.obj (baseObject A B hS)} {fU : U ⟶ yoneda.obj (baseObject A B hS)}
    (hlU : IsLocallyOfFiniteType B _ hS fU) (f : T ⟶ U) (hf : f ≫ fU = fT)
    (hlf : IsLocallyOfFiniteType B _ hS f)
    (het : ∀ n, IsEtale B _ hS (adicFibreMap A I B hS hSn f hf n)) (n : ℕ)
    (y : points B _ hS (adicFibre A I B hS hSn fT n)) :
    IsEtaleAt B _ hS f
      (pointsMap B _ hS _ (pullback.fst fT (yoneda.map (adicThickeningMap A I B hS hSn n))) y) := by
  set x := pointsMap B _ hS _ (pullback.fst fT (yoneda.map (adicThickeningMap A I B hS hSn n))) y
  obtain ⟨c⟩ := exists_etaleChartAtPoint B _ hS hT hU f x
  let kV : c.V ⟶ baseObject A B hS := Over.mkIdTerminal.from c.V
  have hbV : c.b ≫ fU = yoneda.map kV := eq_yoneda_map_of_baseObject _ _
  have haU : c.a ≫ fT = yoneda.map (c.h ≫ kV) := by
    rw [← hf, ← Category.assoc, ← c.comm, Category.assoc, hbV, Functor.map_comp]
  have hlV : LocallyOfFiniteType ((𝒯).map kV) :=
    hlU c.V (baseObject A B hS) c.b (𝟙 _) kV c.b_etale
      (presheaf_etale_of_iso B _ hS (Iso.refl _)) (by rw [Category.comp_id, hbV])
  have : IsLocallyNoetherian ((𝒯).obj (baseObject A B hS)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of A)))
  have : IsLocallyNoetherian ((𝒯).obj c.V) := LocallyOfFiniteType.isLocallyNoetherian ((𝒯).map kV)
  have : LocallyOfFiniteType ((𝒯).map c.h) := hlf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  have hfib : ∀ m : ℕ, Etale (pullback.map ((𝒯).map c.h ≫ (𝒯).map kV) (adicThickeningι A I m)
      ((𝒯).map kV) (adicThickeningι A I m) ((𝒯).map c.h) (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
    fun m => etale_pullbackMap_of_eq _ _ _ _ _ (Functor.map_comp _ _ _) _ _
      (etale_pullbackMap_toScheme_of_forall_isEtale_adicFibreMap f hf het c.a c.b c.h c.a_etale
        c.b_etale c.comm (c.h ≫ kV) kV m)
  -- the chosen point of the chart lies over `V(I)`
  have hv : ∃ m, ((𝒯).map c.h ≫ (𝒯).map kV) (c.sourcePoint B _ hS) ∈
      Set.range (adicThickeningι A I m) := by
    refine ⟨n, pointsToScheme B _ hS (adicThickeningObject A I B hS hSn n)
      (pointsMap B _ hS _ (pullback.snd fT (yoneda.map (adicThickeningMap A I B hS hSn n))) y),
      ?_⟩
    have h1 : pointsMap B _ hS (yoneda.obj c.U) (yoneda.map (c.h ≫ kV))
        (c.representative.class B _ hS (yoneda.obj c.U)) =
        pointsMap B _ hS _ (yoneda.map (adicThickeningMap A I B hS hSn n))
          (pointsMap B _ hS _ (pullback.snd fT (yoneda.map (adicThickeningMap A I B hS hSn n)))
            y) := by
      rw [← haU, pointsMap_comp_apply, c.maps_to, ← pointsMap_comp_apply, pullback.condition,
        pointsMap_comp_apply]
    have h2 := congrArg (pointsToScheme B _ hS (baseObject A B hS)) h1
    rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_pointsMap_yoneda,
      pointsToScheme_class_eq B _ hS _ _ c.point, Functor.map_comp] at h2
    exact h2.symm
  obtain ⟨Z, j, hj, ⟨z, hz⟩, hjE⟩ :=
    exists_isOpenImmersion_etale_of_forall_etale_pullbackMap I ((𝒯).map c.h)
      ((𝒯).map kV : _ ⟶ Spec (.of A)) hfib (c.sourcePoint B _ hS) hv
  have hO : Etale (j.opensRange.ι ≫ (𝒯).map c.h) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    infer_instance
  have hgerm : MorphismOfGerms.HasRepresentativeWithProperty @Etale
      (MorphismOfGerms.ofSchemeHom ((𝒯).map c.h) (c.sourcePoint B _ hS)) := by
    refine ⟨⟨j.opensRange, ⟨z, hz⟩, j.opensRange.ι ≫ (𝒯).map c.h, rfl⟩, ?_, hO⟩
    refine MorphismOfGerms.mk_eq_mk_iff.mpr ⟨j.opensRange, ⟨z, hz⟩, le_rfl, le_top, ?_⟩
    simp
  have hQ := MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget
    (@Etale.{u}) etale_isEtaleLocalOnSourceAndTarget
  have hall := (holdsOnEveryEtaleChartAtPoint_iff_of_chart B _ hS _ hQ f x c).mpr hgerm
  obtain ⟨W, hW, ⟨w, hw⟩, heW⟩ := (holdsOnEveryEtaleChartAtPoint_iff_exists_open B _ hS
    (@Etale.{u}) etale_isEtaleLocalOnSourceAndTarget hT hU f x).mp hall
  exact ⟨W, hW, w, hw, (isEtale_iff_holdsOnEveryEtaleChart B _ hS hW.1 hU _).mpr heW⟩

/-- **The local criterion of flatness along the closed fibre, étale form.** Let `A` be a
Noetherian ring, `I ⊆ A` an ideal and `f : T ⟶ U` a morphism of algebraic spaces over `Spec A`,
locally of finite type, with `U` locally of finite type over `Spec A`. If every adic fibre
`f_n : T_n ⟶ U_n` is étale, then `f` is étale on an open subspace of `T` containing every adic
fibre `T_n`.

The open subspace is the étale locus of `f`, which is open since étaleness at a point is
witnessed by an open subspace; it contains the closed fibre by
`AlgebraicGeometry.Space.isEtaleAt_of_forall_isEtale_adicFibreMap`. -/
theorem exists_isOpenSubspace_isEtale_of_forall_isEtale_adicFibreMap [IsNoetherianRing A]
    {T U : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B _ hS T) (hU : IsAlgebraicSpace B _ hS U)
    {fT : T ⟶ yoneda.obj (baseObject A B hS)} {fU : U ⟶ yoneda.obj (baseObject A B hS)}
    (hlU : IsLocallyOfFiniteType B _ hS fU) (f : T ⟶ U) (hf : f ≫ fU = fT)
    (hlf : IsLocallyOfFiniteType B _ hS f)
    (het : ∀ n, IsEtale B _ hS (adicFibreMap A I B hS hSn f hf n)) :
    ∃ W : Subfunctor T, IsOpenSubspace B _ hS W ∧
      (∀ n, Subfunctor.range (pullback.fst fT (yoneda.map (adicThickeningMap A I B hS hSn n))) ≤
        W) ∧
      IsEtale B _ hS (W.ι ≫ f) := by
  set E : Set (points B _ hS T) := {x | IsEtaleAt B _ hS f x} with hE
  have hEopen : IsOpen E := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨V, hV, x', hx', he⟩ := hx
    refine ⟨Set.range (pointsMap B _ hS V.toFunctor V.ι), ?_,
      isOpen_range_pointsMap_of_isOpenImmersion B _ hS V.ι hV.2, ⟨x', hx'⟩⟩
    rintro _ ⟨v, rfl⟩
    exact isEtaleAt_of_isOpenImmersion B _ hS hV.1 V.ι hV.2 f he v
  have hW := isOpenSubspace_openSubspaceOfPoints B _ hS hT E hEopen
  refine ⟨openSubspaceOfPoints B _ hS T E, hW, fun n => ?_, ?_⟩
  · rintro V _ ⟨y, rfl⟩
    rw [mem_openSubspaceOfPoints_iff, ← yonedaEquiv_symm_naturality_right]
    rintro _ ⟨w, rfl⟩
    rw [pointsMap_comp_apply]
    exact isEtaleAt_of_forall_isEtale_adicFibreMap hT hU hlU f hf hlf het n _
  · refine isEtale_of_forall_isEtaleAt B _ hS hW.1 hU _ fun w => ?_
    have hw : pointsMap B _ hS _ (openSubspaceOfPoints B _ hS T E).ι w ∈ E := by
      have := range_pointsMap_ι_openSubspaceOfPoints B _ hS E
      exact this.subset ⟨w, rfl⟩
    have hw' : IsEtaleAt B _ hS f (pointsMap B _ hS _ (openSubspaceOfPoints B _ hS T E).ι w) := hw
    exact IsEtaleAt.comp B _ hS hT (isEtaleAt_of_isEtale B _ hS hW.1 _
      (isEtale_ι_of_isOpenSubspace hW) w) hw'

/-- A morphism of schemes which is flat on an open neighbourhood of a point is flat at it. -/
theorem flat_stalkMap_of_isOpenImmersion {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    (h : ∃ (Z : Scheme.{u}) (j : Z ⟶ X), _root_.AlgebraicGeometry.IsOpenImmersion j ∧
      x ∈ Set.range j ∧ Flat (j ≫ g)) :
    (g.stalkMap x).hom.Flat := by
  obtain ⟨Z, j, hj, ⟨z, rfl⟩, hF⟩ := h
  have h := Flat.stalkMap (j ≫ g) z
  rw [Scheme.Hom.stalkMap_comp] at h
  have h' : ((j.stalkMap z).hom.comp (g.stalkMap (j z)).hom).Flat := h
  exact (RingHom.Flat.comp_iff_of_bijective_left
    (ConcreteCategory.bijective_of_isIso (j.stalkMap z))).mp h'

/-- **Flatness at the points of the closed fibre (Stacks 0523 for algebraic spaces).** Let `A` be
Noetherian and `f : T ⟶ U` a morphism of algebraic spaces over `Spec A`, locally of finite type,
with `U` locally of finite type over `Spec A`. If every adic fibre of `f` is flat, then `f` is
flat at every point of `T` in the image of an adic fibre. -/
theorem isFlatAt_of_forall_isFlat_adicFibreMap [IsNoetherianRing A]
    {T U : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B _ hS T) (hU : IsAlgebraicSpace B _ hS U)
    {fT : T ⟶ yoneda.obj (baseObject A B hS)} {fU : U ⟶ yoneda.obj (baseObject A B hS)}
    (hlU : IsLocallyOfFiniteType B _ hS fU) (f : T ⟶ U) (hf : f ≫ fU = fT)
    (hlf : IsLocallyOfFiniteType B _ hS f)
    (hfl : ∀ n, IsFlat B _ hS (adicFibreMap A I B hS hSn f hf n)) (n : ℕ)
    (y : points B _ hS (adicFibre A I B hS hSn fT n)) :
    IsFlatAt B _ hS f
      (pointsMap B _ hS _ (pullback.fst fT (yoneda.map (adicThickeningMap A I B hS hSn n))) y) := by
  set x := pointsMap B _ hS _ (pullback.fst fT (yoneda.map (adicThickeningMap A I B hS hSn n))) y
  obtain ⟨c⟩ := exists_etaleChartAtPoint B _ hS hT hU f x
  let kV : c.V ⟶ baseObject A B hS := Over.mkIdTerminal.from c.V
  have hbV : c.b ≫ fU = yoneda.map kV := eq_yoneda_map_of_baseObject _ _
  have haU : c.a ≫ fT = yoneda.map (c.h ≫ kV) := by
    rw [← hf, ← Category.assoc, ← c.comm, Category.assoc, hbV, Functor.map_comp]
  have hlV : LocallyOfFiniteType ((𝒯).map kV) :=
    hlU c.V (baseObject A B hS) c.b (𝟙 _) kV c.b_etale
      (presheaf_etale_of_iso B _ hS (Iso.refl _)) (by rw [Category.comp_id, hbV])
  have : IsLocallyNoetherian ((𝒯).obj (baseObject A B hS)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of A)))
  have : IsLocallyNoetherian ((𝒯).obj c.V) := LocallyOfFiniteType.isLocallyNoetherian ((𝒯).map kV)
  have : LocallyOfFiniteType ((𝒯).map c.h) := hlf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  have hfib : ∀ m : ℕ, Flat (pullback.map ((𝒯).map c.h ≫ (𝒯).map kV) (adicThickeningι A I m)
      ((𝒯).map kV) (adicThickeningι A I m) ((𝒯).map c.h) (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
    fun m => flat_pullbackMap_of_eq _ _ _ _ _ (Functor.map_comp _ _ _) _ _
      (flat_pullbackMap_toScheme_of_forall_isFlat_adicFibreMap f hf hfl c.a c.b c.h c.a_etale
        c.b_etale c.comm (c.h ≫ kV) kV m)
  set w := c.representative.class B _ hS (yoneda.obj c.U)
  have hv : ∃ m, ((𝒯).map c.h ≫ (𝒯).map kV) (pointsToScheme B _ hS c.U w) ∈
      Set.range (adicThickeningι A I m) := by
    refine ⟨n, pointsToScheme B _ hS (adicThickeningObject A I B hS hSn n)
      (pointsMap B _ hS _ (pullback.snd fT (yoneda.map (adicThickeningMap A I B hS hSn n))) y),
      ?_⟩
    have h1 : pointsMap B _ hS (yoneda.obj c.U) (yoneda.map (c.h ≫ kV)) w =
        pointsMap B _ hS _ (yoneda.map (adicThickeningMap A I B hS hSn n))
          (pointsMap B _ hS _ (pullback.snd fT (yoneda.map (adicThickeningMap A I B hS hSn n)))
            y) := by
      rw [← haU, pointsMap_comp_apply, c.maps_to, ← pointsMap_comp_apply, pullback.condition,
        pointsMap_comp_apply]
    have h2 := congrArg (pointsToScheme B _ hS (baseObject A B hS)) h1
    rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_pointsMap_yoneda, Functor.map_comp] at h2
    exact h2.symm
  have hstalk := flat_stalkMap_of_isOpenImmersion ((𝒯).map c.h) (pointsToScheme B _ hS c.U w)
    (exists_isOpenImmersion_flat_of_forall_flat_pullbackMap I ((𝒯).map c.h)
      ((𝒯).map kV : _ ⟶ Spec (.of A)) hfib (pointsToScheme B _ hS c.U w) hv)
  have hy := (isFlatAt_yoneda_iff B _ hS c.U c.V c.h c.representative).mpr hstalk
  have := (isFlatAt_chart_iff B _ hS f c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm.symm
    c.representative c.point).mp hy
  rwa [c.maps_to] at this

end AlgebraicGeometry.Space

end
