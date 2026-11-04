module

public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonDescentAdjunction

/-!
# The unit fork of a single morphism along which descent is fully faithful

Let `F` be a pseudofunctor from the locally discrete bicategory on `C₀ᵒᵖ` to `Cat`, let
`f : X ⟶ Y` be a morphism with a chosen fibre product `g : X ×_Y X ⟶ Y`, and suppose that the
inverse image functors `f⁻¹ = F.map f` and `g⁻¹ = F.map g` have right adjoints `f_*` and `g_*`.
For an object `M` of the fibre over `Y` and a projection `p : X ×_Y X ⟶ X` there is a canonical
restriction map `f_* f⁻¹ M ⟶ g_* g⁻¹ M`, the transpose of the restriction of the counit of
`f⁻¹ ⊣ f_*` along `p`. This file shows that the unit `M ⟶ f_* f⁻¹ M` equalizes the two
restriction maps of the two projections, and that the resulting fork is a limit as soon as the
functor from the fibre over `Y` to descent data along `{f}` is fully faithful.

## Main definitions

* `CategoryTheory.Pseudofunctor.unitForkRestriction`: the restriction map
  `f_* f⁻¹ M ⟶ g_* g⁻¹ M` along a projection.

## Main results

* `CategoryTheory.Pseudofunctor.unit_comp_unitForkRestriction`: the unit of `f` followed by the
  restriction map is the unit of `g`, for either projection.
* `CategoryTheory.Pseudofunctor.isLimitUnitFork`: the unit fork is a limit when descent along
  `{f}` is fully faithful.

## Implementation notes

The limit property is read off the right adjoint
`CategoryTheory.Pseudofunctor.singletonDescentRightAdjoint` of the descent functor: morphisms
`N ⟶ f_* f⁻¹ M` equalizing the two reconstruction morphisms are morphisms of descent data
`N ⟶ M` (`CategoryTheory.Pseudofunctor.reconstructionHom`), hence morphisms `N ⟶ M` by full
faithfulness. The reconstruction morphisms land in `g_*` of the restriction of `f⁻¹ M` along the
first projection; composing with `g_*` of the composition isomorphism identifies them with the
restriction maps of the two projections.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite

universe v u v' u'

namespace Pseudofunctor

open DescentData LocallyDiscreteOpToCat

variable {C₀ : Type u} [Category.{v} C₀]
  (F : Pseudofunctor (LocallyDiscrete C₀ᵒᵖ) Cat.{v', u'})
  {X Y : C₀} (f : X ⟶ Y) (sq : ChosenPullback f f)
  {R : F.obj (.mk (.op X)) ⥤ F.obj (.mk (.op Y))}
  (adj : (F.map f.op.toLoc).toFunctor ⊣ R)
  {T : F.obj (.mk (.op sq.pullback)) ⥤ F.obj (.mk (.op Y))}
  (adjK : (F.map sq.p.op.toLoc).toFunctor ⊣ T)

/-- **The restriction map `f_* f⁻¹ M ⟶ g_* g⁻¹ M` along a projection `p`** of the fibre product
`X ×_Y X`, whose structure morphism to `Y` is `g = p ≫ f`: the transpose, along `g⁻¹ ⊣ g_*`, of
the restriction along `p` of the counit `f⁻¹ f_* f⁻¹ M ⟶ f⁻¹ M`, read through the composition
isomorphisms `g⁻¹ ≅ p⁻¹ f⁻¹`. -/
noncomputable def unitForkRestriction (p : sq.pullback ⟶ X) (hp : p ≫ f = sq.p)
    (M : F.obj (.mk (.op Y))) :
    R.obj ((F.map f.op.toLoc).toFunctor.obj M) ⟶ T.obj ((F.map sq.p.op.toLoc).toFunctor.obj M) :=
  adjK.homEquiv _ _
    ((F.mapComp' f.op.toLoc p.op.toLoc sq.p.op.toLoc (by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, hp])).hom.toNatTrans.app _ ≫
      (F.map p.op.toLoc).toFunctor.map (adj.counit.app _) ≫
      (F.mapComp' f.op.toLoc p.op.toLoc sq.p.op.toLoc (by
        rw [← Quiver.Hom.comp_toLoc, ← op_comp, hp])).inv.toNatTrans.app M)

/-- **The unit of `f` followed by a restriction map is the unit of `g`.** In particular the unit
`M ⟶ f_* f⁻¹ M` equalizes the restriction maps of the two projections. -/
theorem unit_comp_unitForkRestriction (p : sq.pullback ⟶ X) (hp : p ≫ f = sq.p)
    (M : F.obj (.mk (.op Y))) :
    adj.unit.app M ≫ unitForkRestriction F f sq adj adjK p hp M = adjK.unit.app M := by
  rw [unitForkRestriction]
  refine (adjK.homEquiv_naturality_left (adj.unit.app M) _).symm.trans ?_
  refine Eq.trans ?_ (adjK.homEquiv_id M)
  congr 1
  have hnat := (F.mapComp' f.op.toLoc p.op.toLoc sq.p.op.toLoc (by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp, hp])).hom.toNatTrans.naturality (adj.unit.app M)
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hnat
  rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp_assoc,
    adj.left_triangle_components M]
  simp only [Functor.id_obj, Functor.map_id, Category.id_comp,
    Cat.Hom.hom_inv_id_toNatTrans_app]

/-- The reconstruction morphisms, followed by `g_*` of the composition isomorphism, are the
restriction maps of the two projections. -/
theorem reconstructionFirst_comp_eq (M : F.obj (.mk (.op Y))) :
    reconstructionFirst F f sq adj adjK ((F.toDescentData (fun _ : Unit ↦ f)).obj M) ≫
      T.map ((F.mapComp' f.op.toLoc sq.p₁.op.toLoc sq.p.op.toLoc (by
        rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₁])).inv.toNatTrans.app M) =
      unitForkRestriction F f sq adj adjK sq.p₁ sq.hp₁ M := by
  rw [reconstructionFirst, unitForkRestriction]
  exact (adjK.homEquiv_naturality_right _ _).symm.trans
    (congrArg (adjK.homEquiv _ _) (Category.assoc _ _ _))

/-- The second reconstruction morphism, followed by `g_*` of the composition isomorphism, is the
restriction map of the second projection. -/
theorem reconstructionSecond_comp_eq (M : F.obj (.mk (.op Y))) :
    reconstructionSecond F f sq adj adjK ((F.toDescentData (fun _ : Unit ↦ f)).obj M) ≫
      T.map ((F.mapComp' f.op.toLoc sq.p₁.op.toLoc sq.p.op.toLoc (by
        rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₁])).inv.toNatTrans.app M) =
      unitForkRestriction F f sq adj adjK sq.p₂ sq.hp₂ M := by
  rw [reconstructionSecond, unitForkRestriction]
  refine (adjK.homEquiv_naturality_right _ _).symm.trans (congrArg (adjK.homEquiv _ _) ?_)
  dsimp only [toDescentData, ofObj]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]

/-- **The unit fork is a limit when descent along `{f}` is fully faithful.** The unit
`M ⟶ f_* f⁻¹ M` is an equalizer of the restriction maps `f_* f⁻¹ M ⇉ g_* g⁻¹ M` of the two
projections of `X ×_Y X`. -/
noncomputable def isLimitUnitFork
    (hff : (F.toDescentData (fun _ : Unit ↦ f)).FullyFaithful) (M : F.obj (.mk (.op Y))) :
    IsLimit (Fork.ofι (adj.unit.app M)
      ((unit_comp_unitForkRestriction F f sq adj adjK sq.p₁ sq.hp₁ M).trans
        (unit_comp_unitForkRestriction F f sq adj adjK sq.p₂ sq.hp₂ M).symm) :
      Fork (unitForkRestriction F f sq adj adjK sq.p₁ sq.hp₁ M)
        (unitForkRestriction F f sq adj adjK sq.p₂ sq.hp₂ M)) := by
  let D := (F.toDescentData (fun _ : Unit ↦ f)).obj M
  have h1 : (adj.homEquiv _ _).symm (adj.unit.app M) = 𝟙 _ := by
    rw [Adjunction.homEquiv_counit]
    exact adj.left_triangle_components M
  have hmono : Mono (T.map ((F.mapComp' f.op.toLoc sq.p₁.op.toLoc sq.p.op.toLoc (by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₁])).inv.toNatTrans.app M)) :=
    inferInstanceAs (Mono (T.mapIso ((Cat.Hom.toNatIso (F.mapComp' f.op.toLoc sq.p₁.op.toLoc
      sq.p.op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₁]))).app M).symm).hom)
  have hcond : ∀ {N : F.obj (.mk (.op Y))} (ι : N ⟶ R.obj (D.obj ())),
      ι ≫ unitForkRestriction F f sq adj adjK sq.p₁ sq.hp₁ M =
        ι ≫ unitForkRestriction F f sq adj adjK sq.p₂ sq.hp₂ M →
      ι ≫ reconstructionFirst F f sq adj adjK D = ι ≫ reconstructionSecond F f sq adj adjK D :=
    fun ι h ↦ (cancel_mono (T.map ((F.mapComp' f.op.toLoc sq.p₁.op.toLoc sq.p.op.toLoc (by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₁])).inv.toNatTrans.app M))).1
      ((Category.assoc _ _ _).trans
        ((congrArg (ι ≫ ·) (reconstructionFirst_comp_eq F f sq adj adjK M)).trans
          (h.trans ((congrArg (ι ≫ ·) (reconstructionSecond_comp_eq F f sq adj adjK M)).symm.trans
            (Category.assoc _ _ _).symm))))
  refine Fork.IsLimit.mk _
    (fun s ↦ hff.preimage (reconstructionHom F f sq adj adjK D s.ι (hcond s.ι s.condition)))
    (fun s ↦ ?_) (fun s m hm ↦ ?_)
  · change hff.preimage _ ≫ adj.unit.app M = s.ι
    apply (adj.homEquiv _ _).symm.injective
    rw [adj.homEquiv_naturality_left_symm, h1, Category.comp_id, Adjunction.homEquiv_counit]
    exact congrArg (fun φ ↦ φ.hom ()) (hff.map_preimage
      (reconstructionHom F f sq adj adjK D s.ι (hcond s.ι s.condition)))
  · have hm' : m ≫ adj.unit.app M = s.ι := hm
    apply hff.map_injective
    rw [hff.map_preimage]
    ext ⟨⟩
    change (F.map f.op.toLoc).toFunctor.map m =
      (F.map f.op.toLoc).toFunctor.map s.ι ≫ adj.counit.app ((F.map f.op.toLoc).toFunctor.obj M)
    rw [← hm', Functor.map_comp, Category.assoc]
    exact (Category.comp_id _).symm.trans
      (congrArg (_ ≫ ·) (adj.left_triangle_components M).symm)

end Pseudofunctor

end CategoryTheory

end
