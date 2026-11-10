module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMapStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkColimits
public import StacksFrontier.CategoryTheory.Limits.FiniteProductFunctorColimits

/-!
# Direct images which are finite products on stalks commute with colimits

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi, and suppose that `D` has a
conservative family of points `Ψ` at each of which the stalk of the direct image of a sheaf of sets
is the product of its stalks at finitely many points `Φ₁, …, Φₙ` of `C`. Then the stalk at `Ψ` of
the direct image `f_*` of sheaves of modules is the finite direct sum of the stalk functors at the
`Φᵢ`, and `f_*` commutes with every colimit indexed by a small category in `Type 0`: in particular
it is exact and commutes with countable direct sums.

## Main definitions

* `abelianStalk`: the stalk of a sheaf of modules, as an abelian group.
* `pushforwardStalkNatTrans`, `pushforwardStalkPiNatTrans`: the maps `(f_*N)_Ψ ⟶ N_Φ` of stalks,
  and their product over the `Φᵢ`, as natural transformations of abelian-group-valued functors.

## Main results

* `isIso_pushforwardStalkPiNatTrans`: the stalk of `f_*` at `Ψ` is the product of the stalks at the
  `Φᵢ`, as functors.
* `preservesColimitsOfSize_pushforwardModules_of_isConservativeFamilyOfPoints`: the direct image of
  modules commutes with colimits of shape in `Type 0`.

## References

* [Stacks Project, Tag 0DK5](https://stacks.math.columbia.edu/tag/0DK5)
* [Stacks Project, Tag 0DK3](https://stacks.math.columbia.edu/tag/0DK3)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
  Stacks.Sheaves.StalkTransport

universe w v u v' u'

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (f : RingedToposHom X Y)

/-- The stalk at a point of a site of a sheaf of modules, as an abelian group. -/
abbrev abelianStalk {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
    {J : GrothendieckTopology C} (Φ : J.Point.{w}) (R : Sheaf J RingCat.{w}) :
    SheafOfModules.{w} R ⥤ AddCommGrpCat.{w} :=
  Stacks.sheafModuleFiber Φ R ⋙
    forget₂ (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R.obj)) AddCommGrpCat.{w}

/-- **The map `(f_*N)_Ψ ⟶ N_Φ` of stalks, naturally in `N`**: the components are
`Stacks.SheafOfModules.pushforwardStalkHom`. -/
def pushforwardStalkNatTrans (Φ : X.J.Point.{w}) (Ψ : Y.J.Point.{w})
    (e : Ψ.sheafFiber (A := Type w) ≅ f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w)) :
    pushforwardModules f ⋙ abelianStalk Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      abelianStalk Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O) where
  app N := AddCommGrpCat.ofHom (pushforwardStalkHom f Φ Ψ e N)
  naturality N N' g := by
    ext z
    obtain ⟨x, rfl⟩ := (Stacks.Sheaves.StalkTransport.bijective_moduleStalkComparison Ψ
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N)).2 z
    change pushforwardStalkHom f Φ Ψ e N'
        ((Stacks.sheafModuleFiber Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((pushforwardModules f).map g) (moduleStalkComparison Ψ _ _ x)) =
      (Stacks.sheafModuleFiber Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map g
        (pushforwardStalkHom f Φ Ψ e N (moduleStalkComparison Ψ _ _ x))
    rw [← Stacks.Sheaves.StalkTransport.moduleStalkComparison_naturality,
      pushforwardStalkHom_moduleStalkComparison, pushforwardStalkHom_moduleStalkComparison,
      ← Stacks.Sheaves.StalkTransport.moduleStalkComparison_naturality]
    exact congrArg (moduleStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N')
      (ConcreteCategory.congr_hom
        ((f.toToposHom.pushforwardFiberMap Φ Ψ e).naturality
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map g)) x)

/-- The component of `pushforwardStalkNatTrans` at `N` is `pushforwardStalkHom`. -/
lemma pushforwardStalkNatTrans_app_apply (Φ : X.J.Point.{w}) (Ψ : Y.J.Point.{w})
    (e : Ψ.sheafFiber (A := Type w) ≅ f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w))
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (z : (Stacks.sheafModuleFiber Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
      ((pushforwardModules f).obj N)) :
    (pushforwardStalkNatTrans f Φ Ψ e).app N z = pushforwardStalkHom f Φ Ψ e N z :=
  rfl

section Product

variable (Ψ : Y.J.Point.{w}) {ι : Type w} (Φ : ι → X.J.Point.{w})
  (e : ∀ i, Ψ.sheafFiber (A := Type w) ≅
    f.toToposHom.inverseImage ⋙ (Φ i).sheafFiber (A := Type w))
  [HasProductsOfShape ι AddCommGrpCat.{w}]

/-- The maps `(f_*N)_Ψ ⟶ N_{Φ i}` of stalks, assembled into a map to the product, naturally in
`N`. -/
def pushforwardStalkPiNatTrans :
    pushforwardModules f ⋙ abelianStalk Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      piObjFunctor (fun i => abelianStalk (Φ i) (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  app N :=
    Pi.lift (f := fun i => (abelianStalk (Φ i) (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N)
      fun i => (pushforwardStalkNatTrans f (Φ i) Ψ (e i)).app N
  naturality N N' g := by
    refine Limits.Pi.hom_ext _ _ fun i => ?_
    rw [Category.assoc, Category.assoc, Limits.Pi.lift_comp_π, piObjFunctor_map, Limits.Pi.map_π,
      Limits.Pi.lift_comp_π_assoc]
    exact (pushforwardStalkNatTrans f (Φ i) Ψ (e i)).naturality g

/-- The `i`-th component of `pushforwardStalkPiNatTrans` is `pushforwardStalkNatTrans` at `Φ i`.
-/
@[reassoc (attr := simp)]
lemma pushforwardStalkPiNatTrans_app_π
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (i : ι) :
    (pushforwardStalkPiNatTrans f Ψ Φ e).app N ≫
        Pi.π (fun i => (abelianStalk (Φ i) (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N) i =
      (pushforwardStalkNatTrans f (Φ i) Ψ (e i)).app N :=
  Pi.lift_comp_π _ _

/-- **The stalk of `f_*` at `Ψ` is the product of the stalks at the `Φ i`**, as functors, when
this holds for sheaves of sets and the family is finite. -/
lemma isIso_pushforwardStalkPiNatTrans [Finite ι]
    (h : ∀ M : Sheaf X.J (Type w), Function.Bijective
      (fun z i => (f.toToposHom.pushforwardFiberMap (Φ i) Ψ (e i)).app M z)) :
    IsIso (pushforwardStalkPiNatTrans f Ψ Φ e) := by
  classical
  have := Fintype.ofFinite ι
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun N => ?_
  let c := AddCommGrpCat.HasLimit.productLimitCone.{w, w}
    (fun i => (abelianStalk (Φ i) (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N)
  let γ := limit.isoLimitCone c
  have hcomp : ∀ z, ((pushforwardStalkPiNatTrans f Ψ Φ e).app N ≫ γ.hom) z =
      pushforwardStalkPiHom f Ψ Φ e N z := fun z => by
    funext i
    have h1 := limit.isoLimitCone_hom_π c ⟨i⟩
    have h2 := ConcreteCategory.congr_hom
      (congrArg (fun φ => (pushforwardStalkPiNatTrans f Ψ Φ e).app N ≫ φ) h1) z
    simp only at h2
    exact h2.trans (ConcreteCategory.congr_hom
      (pushforwardStalkPiNatTrans_app_π f Ψ Φ e N i) z)
  have hb : IsIso ((pushforwardStalkPiNatTrans f Ψ Φ e).app N ≫ γ.hom) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    rw [show ⇑(ConcreteCategory.hom ((pushforwardStalkPiNatTrans f Ψ Φ e).app N ≫ γ.hom)) =
      ⇑(pushforwardStalkPiHom f Ψ Φ e N) from funext hcomp]
    exact bijective_pushforwardStalkPiHom f Ψ Φ e h N
  exact IsIso.of_isIso_comp_right _ γ.hom

end Product

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The direct image of sheaves of modules commutes with colimits** of every shape in `Type 0` —
in particular it is exact and commutes with countable direct sums — when the target site has a
conservative family of points at each of which the stalk of a direct image of sheaves of sets is
the product of its stalks at finitely many points of the source, each identified with it along `f`.
-/
theorem preservesColimitsOfSize_pushforwardModules_of_isConservativeFamilyOfPoints
    {P : ObjectProperty Y.J.Point.{w}} (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ Ψ : Y.J.Point.{w}, P Ψ → ∃ (ι : Type w) (_ : Finite ι) (Φ : ι → X.J.Point.{w})
      (e : ∀ i, Ψ.sheafFiber (A := Type w) ≅
        f.toToposHom.inverseImage ⋙ (Φ i).sheafFiber (A := Type w)),
      ∀ M : Sheaf X.J (Type w), Function.Bijective
        (fun z i => (f.toToposHom.pushforwardFiberMap (Φ i) Ψ (e i)).app M z)) :
    PreservesColimitsOfSize.{0, 0} (pushforwardModules f) where
  preservesColimitsOfShape {K} _ := by
    let s : ∀ Ψ : P.FullSubcategory,
        SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤ AddCommGrpCat.{w} :=
      fun Ψ => abelianStalk Ψ.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    have hs : JointlyReflectIsomorphisms s := ⟨fun {M N} g hg =>
      Stacks.isIso_of_isIso_sheafModuleFiber (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) hP g
        fun Ψ => by
        have : IsIso ((forget₂ (ModuleCat.{w} ((Ψ.obj.presheafFiber
            (A := RingCat.{w})).obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))
              AddCommGrpCat.{w}).map
              ((Stacks.sheafModuleFiber Ψ.obj
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map g)) := hg Ψ
        exact isIso_of_reflects_iso _ (forget₂ (ModuleCat.{w} ((Ψ.obj.presheafFiber
          (A := RingCat.{w})).obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))
            AddCommGrpCat.{w})⟩
    have : ∀ Ψ : P.FullSubcategory, PreservesColimitsOfShape K (pushforwardModules f ⋙ s Ψ) :=
      fun Ψ => by
        obtain ⟨ι, _, Φ, e, hΦ⟩ := h Ψ.obj Ψ.property
        have : HasProductsOfShape ι AddCommGrpCat.{w} :=
          (inferInstance : HasLimitsOfSize.{w, w} AddCommGrpCat.{w}).has_limits_of_shape _
        have := isIso_pushforwardStalkPiNatTrans f Ψ.obj Φ e hΦ
        have : PreservesColimitsOfShape K
            (piObjFunctor
              (fun i => abelianStalk (Φ i) (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
          preservesColimitsOfShape_piObjFunctor ι _
        exact preservesColimitsOfShape_of_natIso
          (asIso (pushforwardStalkPiNatTrans f Ψ.obj Φ e)).symm
    exact hs.preservesColimitsOfShape (pushforwardModules f)

end Stacks.SheafOfModules

end
