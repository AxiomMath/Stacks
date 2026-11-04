module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompGlue

/-!
# The composition isomorphism of direct images with compact support

For composable locally quasi-finite morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of a big étale site
the comparison `(f ≫ g)_! ⟶ g_! ∘ f_!` of `AlgebraicGeometry.SmallEtale.compShriekMap` is an
isomorphism of functors on abelian étale sheaves, which on the stalk decompositions of
Stacks 0F5F is the regrouping of the geometric fibre of `f ≫ g` over that of `g`, and which is
associative. These are the canonical isomorphism of Stacks 0F6T and its properties (3) and (4).

## Main definitions

* `AlgebraicGeometry.SmallEtale.fShriekCompIso` — the isomorphism `(f ≫ g)_! ≅ f_! ⋙ g_!`.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekCompIso_stalk` — property (3), the stalks.
* `AlgebraicGeometry.SmallEtale.fShriekCompIso_assoc` — property (4), associativity.

## References

* [Stacks Project, Tag 0F6T](https://stacks.math.columbia.edu/tag/0F6T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section Regrouping

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  (s : GeometricPoint Z.obj)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The regrouping of the geometric fibre of a composite is injective. -/
public theorem compFiberStalksMap_injective :
    Function.Injective (compFiberStalksMap B f g s F) := by
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ => DFinsupp.ext fun x => ?_
  have h := compFiberStalksMap_apply B f g s F ξ (compFiberPoint B f g s x)
    (compFiberPointLift B f g s x)
  rw [hξ] at h
  refine h.symm.trans ?_
  simp only [DirectSum.zero_apply, map_zero]
  rfl

/-- The regrouping of the geometric fibre of a composite is surjective. -/
public theorem compFiberStalksMap_surjective :
    Function.Surjective (compFiberStalksMap B f g s F) := by
  let := Classical.decEq (GeometricFiberPoint B (f ≫ g) s)
  let := Classical.decEq (GeometricFiberPoint B g s)
  let : ∀ t, DecidableEq (GeometricFiberPoint B f t) := fun t => Classical.decEq _
  have hgen : ∀ (y : GeometricFiberPoint B g s)
      (x : GeometricFiberPoint B f (y.toGeometricPoint B g s))
      (b : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f _) F.obj)),
      DirectSum.of _ y ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).inv
        (DirectSum.of _ x b)) ∈ (compFiberStalksMap B f g s F).range := by
    rintro ⟨y, hy⟩ ⟨x, hx⟩ b
    revert x
    refine fun (x : s.source ⟶ X.obj) (hx : x ≫ B.inclusion.map f = y) b => ?_
    subst hx
    exact ⟨DirectSum.of (fun x : GeometricFiberPoint B (f ≫ g) s =>
      ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s) F.obj))
        (compFiberPointOf B f g s ⟨x ≫ B.inclusion.map f, hy⟩ ⟨x, rfl⟩) b, by
      exact (DirectSum.toAddMonoid_of _ _ _).trans rfl⟩
  have hsum : ∀ (y : GeometricFiberPoint B g s)
      (c : ↑(etaleStalk B Y.obj Y.property (y.toGeometricPoint B g s)
        ((fShriekFunctor.{u, v} B f).obj F).obj)),
      DirectSum.of _ y c ∈ (compFiberStalksMap B f g s F).range := by
    intro y c
    rw [← Iso.hom_inv_id_apply (fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F) c]
    induction (fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom c
      using DirectSum.induction_on with
    | zero =>
      simp only [map_zero]
      exact AddSubgroup.zero_mem _
    | add a b ha hb =>
      simp only [map_add]
      exact AddSubgroup.add_mem _ ha hb
    | of x b => exact hgen y x b
  refine fun η => AddMonoidHom.mem_range.1 ?_
  induction η using DirectSum.induction_on with
  | zero => exact AddSubgroup.zero_mem _
  | add a b ha hb => exact AddSubgroup.add_mem _ ha hb
  | of y c => exact hsum y c

/-- The regrouping of the geometric fibre of a composite, as an isomorphism of abelian groups. -/
public def compFiberStalksEquiv :
    fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F ≃+
      fiberStalks.{u, max (u + 1) v} B g s ((fShriekFunctor.{u, v} B f).obj F) :=
  AddEquiv.ofBijective (compFiberStalksMap B f g s F)
    ⟨compFiberStalksMap_injective B f g s F, compFiberStalksMap_surjective B f g s F⟩

end Regrouping

section Iso

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]

/-- The comparison `(f ≫ g)_! F ⟶ g_!(f_! F)` is an isomorphism: on every geometric stalk it is
the regrouping of the geometric fibre, and the geometric stalks jointly reflect isomorphisms. -/
public instance isIso_compShriekMap
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    IsIso (compShriekMap B f g F) := by
  have : ∀ s : GeometricPoint Z.obj,
      IsIso (((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map (compShriekMap B f g F)) := fun s => by
    rw [compShriekMap_hasCompShriekStalks B f g F s]
    have : IsIso (AddCommGrpCat.ofHom (compFiberStalksMap B f g s F)) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        ⟨compFiberStalksMap_injective B f g s F, compFiberStalksMap_surjective B f g s F⟩
    have h3 : IsIso ((fShriekStalkIso.{u, v} B (f ≫ g) s F).hom ≫
        AddCommGrpCat.ofHom (compFiberStalksMap B f g s F) ≫
        (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).inv) := inferInstance
    exact h3
  exact (jointlyFaithful_etaleStalkSheafFiber.{u, v} B Z.obj
    Z.property).jointlyReflectsIsomorphisms.isIso _

/-- **Stacks 0F6T.** For composable locally quasi-finite morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`
there is a canonical isomorphism of functors `(g ∘ f)_! ≅ g_! ∘ f_!` on abelian étale sheaves:
the comparison of `AlgebraicGeometry.SmallEtale.compShriekMap`, glued from the comparisons on the
inverse images of the affine opens of `Y`, natural in the sheaf and an isomorphism on every
geometric stalk. -/
@[stacks 0F6T "the canonical isomorphism (g ∘ f)_! ≅ g_! ∘ f_!"]
public def fShriekCompIso :
    fShriekFunctor.{u, v} B (f ≫ g) ≅ fShriekFunctor.{u, v} B f ⋙ fShriekFunctor.{u, v} B g :=
  NatIso.ofComponents (fun F => asIso (compShriekMap B f g F))
    (fun φ => compShriekMap_naturality B f g _ φ)

public theorem fShriekCompIso_hom_app
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    (fShriekCompIso B f g).hom.app F = compShriekMap B f g F :=
  rfl

/-- **Stacks 0F6T, part (3).** At a geometric point `z̄` of `Z`, the isomorphism
`((g ∘ f)_!F)_z̄ ≅ (g_!f_!F)_z̄` followed by the stalk decomposition
`(g_!f_!F)_z̄ = ⊕_{g(ȳ) = z̄} (f_!F)_ȳ` of Stacks 0F5F is the stalk decomposition
`((g ∘ f)_!F)_z̄ = ⊕_{g(f(x̄)) = z̄} F_x̄` followed by the regrouping of the geometric fibre of
`g ∘ f` over the one of `g`, each `F_x̄` being placed in `(f_!F)_{f(x̄)} = ⊕_{f(x̄') = f(x̄)} F_x̄'`
through the decomposition of Stacks 0F5F for `f`. -/
@[stacks 0F6T "part (3)"]
public theorem fShriekCompIso_stalk (s : GeometricPoint Z.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map ((fShriekCompIso B f g).hom.app F) ≫
      (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).hom =
    (fShriekStalkIso.{u, v} B (f ≫ g) s F).hom ≫
      AddCommGrpCat.ofHom (compFiberStalksMap B f g s F) :=
  (Iso.eq_comp_inv _).1 ((compShriekMap_hasCompShriekStalks B f g F s).trans
    (Category.assoc _ _ _).symm)

/-- Property (3) of Stacks 0F6T characterizes the isomorphism. -/
public theorem eq_fShriekCompIso
    {e : fShriekFunctor.{u, v} B (f ≫ g) ⟶ fShriekFunctor.{u, v} B f ⋙ fShriekFunctor.{u, v} B g}
    (he : ∀ (s : GeometricPoint Z.obj)
      (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}),
      ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map (e.app F) ≫
        (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).hom =
      (fShriekStalkIso.{u, v} B (f ≫ g) s F).hom ≫
        AddCommGrpCat.ofHom (compFiberStalksMap B f g s F)) :
    e = (fShriekCompIso B f g).hom := by
  ext F : 2
  exact eq_compShriekMap B f g F fun s =>
    ((Iso.eq_comp_inv _).2 (he s F)).trans (Category.assoc _ _ _)

end Iso

section Congr

variable (B : BigEtaleSite.{u}) {X T : B.Scheme} {k₁ k₂ : X ⟶ T}
  [LocallyOfFiniteType (B.inclusion.map k₁)] [LocallyQuasiFinite (B.inclusion.map k₁)]
  [LocallyOfFiniteType (B.inclusion.map k₂)] [LocallyQuasiFinite (B.inclusion.map k₂)]

/-- Equal morphisms have equal direct images with compact support. -/
public theorem fShriekFunctor_congr (h : k₁ = k₂) :
    fShriekFunctor.{u, v} B k₁ = fShriekFunctor.{u, v} B k₂ := by
  subst h
  rfl

/-- The geometric fibres of equal morphisms. -/
public def geometricFiberPointCongr (h : k₁ = k₂) (s : GeometricPoint T.obj) :
    GeometricFiberPoint B k₁ s ≃ GeometricFiberPoint B k₂ s where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h ▸ x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identification of the direct images with compact support of equal morphisms is, on the
stalk decompositions of Stacks 0F5F, the identification of their geometric fibres. -/
public theorem fShriekStalkIso_congr (h : k₁ = k₂) (s : GeometricPoint T.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    ((geometricPointSitePoint B T.obj T.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
        (eqToHom (congrArg (fun G => G.obj F) (fShriekFunctor_congr.{u, v} B h))) ≫
      (fShriekStalkIso.{u, v} B k₂ s F).hom =
    (fShriekStalkIso.{u, v} B k₁ s F).hom ≫
      (AddCommGrpCat.ofHom
          (DirectSum.equivCongrLeft (geometricFiberPointCongr B h s)).toAddMonoidHom :
        AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B k₁ s F) ⟶
          AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B k₂ s F)) := by
  subst h
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).trans <| (Category.comp_id _).symm.trans (congrArg _
    (ConcreteCategory.hom_ext _ _ fun ξ => DFinsupp.ext fun x =>
      (DirectSum.equivCongrLeft_apply (geometricFiberPointCongr B rfl s) ξ x).symm))

end Congr

section Assoc

variable (B : BigEtaleSite.{u}) {X Y Z T : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map h)] [LocallyQuasiFinite (B.inclusion.map h)]

/-- The two regroupings of the geometric fibre of a triple composite agree. -/
public theorem compFiberStalksMap_assoc (s : GeometricPoint T.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (ξ : fiberStalks.{u, max (u + 1) v} B ((f ≫ g) ≫ h) s F) :
    compFiberStalksMap B g h s ((fShriekFunctor.{u, v} B f).obj F)
        (compFiberStalksMap B f (g ≫ h) s F
          (DirectSum.equivCongrLeft (geometricFiberPointCongr B (Category.assoc f g h) s) ξ)) =
      fiberStalksMap.{u, max (u + 1) v} B h s (compShriekMap B f g F)
        (compFiberStalksMap B (f ≫ g) h s F ξ) := by
  refine DFinsupp.ext fun z => ?_
  refine (AddCommGrpCat.mono_iff_injective (fShriekStalkIso.{u, v} B g (z.toGeometricPoint B h s)
    ((fShriekFunctor.{u, v} B f).obj F)).hom).1 inferInstance ?_
  refine DFinsupp.ext fun y => ?_
  refine (AddCommGrpCat.mono_iff_injective (fShriekStalkIso.{u, v} B f
    (y.toGeometricPoint B g (z.toGeometricPoint B h s)) F).hom).1 inferInstance ?_
  refine DFinsupp.ext fun x => ?_
  have hL := compFiberStalksMap_apply B g h s ((fShriekFunctor.{u, v} B f).obj F)
    (compFiberStalksMap B f (g ≫ h) s F
      (DirectSum.equivCongrLeft (geometricFiberPointCongr B (Category.assoc f g h) s) ξ)) z y
  have hL' := compFiberStalksMap_apply B f (g ≫ h) s F
    (DirectSum.equivCongrLeft (geometricFiberPointCongr B (Category.assoc f g h) s) ξ)
    (compFiberPointOf B g h s z y) x
  have hR := ConcreteCategory.congr_hom
    (compShriekMap_hasCompShriekStalks B f g F (z.toGeometricPoint B h s))
    ((compFiberStalksMap B (f ≫ g) h s F ξ : fiberStalks.{u, max (u + 1) v} B h s _) z)
  have hR' := compFiberStalksMap_apply B f g (z.toGeometricPoint B h s) F
    ((fShriekStalkIso.{u, v} B (f ≫ g) (z.toGeometricPoint B h s) F).hom
      ((compFiberStalksMap B (f ≫ g) h s F ξ : fiberStalks.{u, max (u + 1) v} B h s _) z)) y x
  have hR'' := compFiberStalksMap_apply B (f ≫ g) h s F ξ z
    (compFiberPointOf B f g (z.toGeometricPoint B h s) y x)
  refine (congrArg (fun m => ((fShriekStalkIso.{u, v} B f _ F).hom m :
    fiberStalks.{u, max (u + 1) v} B f _ F) x) hL).trans (hL'.trans ?_)
  refine Eq.symm ((congrArg (fun m => ((fShriekStalkIso.{u, v} B f _ F).hom
    (((fShriekStalkIso.{u, v} B g (z.toGeometricPoint B h s)
      ((fShriekFunctor.{u, v} B f).obj F)).hom m : fiberStalks.{u, max (u + 1) v} B g _ _) y) :
        fiberStalks.{u, max (u + 1) v} B f _ F) x) hR).trans ?_)
  refine (congrArg (fun m => ((fShriekStalkIso.{u, v} B f _ F).hom
    ((m : fiberStalks.{u, max (u + 1) v} B g _ _) y) : fiberStalks.{u, max (u + 1) v} B f _ F) x)
    (Iso.inv_hom_id_apply (fShriekStalkIso.{u, v} B g (z.toGeometricPoint B h s)
      ((fShriekFunctor.{u, v} B f).obj F)) _)).trans ?_
  exact hR'.trans hR''

/-- **Stacks 0F6T, part (4).** For a third locally quasi-finite morphism `h : Z ⟶ T` the two
isomorphisms `(h ∘ g ∘ f)_! ≅ h_! ∘ g_! ∘ f_!` obtained from the composition isomorphisms agree:
through `(h ∘ g)_! ∘ f_!` and through `h_! ∘ (g ∘ f)_!`. The identification
`(h ∘ (g ∘ f))_! = ((h ∘ g) ∘ f)_!` along the associativity of composition is written out. -/
@[stacks 0F6T "part (4)"]
public theorem fShriekCompIso_assoc :
    eqToHom (fShriekFunctor_congr.{u, v} B (Category.assoc f g h)) ≫
        (fShriekCompIso B f (g ≫ h)).hom ≫
        Functor.whiskerLeft (fShriekFunctor.{u, v} B f) (fShriekCompIso B g h).hom =
      (fShriekCompIso B (f ≫ g) h).hom ≫
        Functor.whiskerRight (fShriekCompIso B f g).hom (fShriekFunctor.{u, v} B h) := by
  ext F : 2
  refine (jointlyFaithful_etaleStalkSheafFiber.{u, v} B T.obj T.property).map_injective
    fun s => ?_
  refine (cancel_mono (fShriekStalkIso.{u, v} B h s
    ((fShriekFunctor.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F))).hom).1 ?_
  have e1 : (eqToHom (fShriekFunctor_congr.{u, v} B (Category.assoc f g h)) ≫
        (fShriekCompIso B f (g ≫ h)).hom ≫
        Functor.whiskerLeft (fShriekFunctor.{u, v} B f) (fShriekCompIso B g h).hom).app F =
      eqToHom (congrArg (fun G => G.obj F) (fShriekFunctor_congr.{u, v} B
          (Category.assoc f g h))) ≫
        compShriekMap B f (g ≫ h) F ≫ compShriekMap B g h ((fShriekFunctor.{u, v} B f).obj F) := by
    rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app]
    rfl
  have e2 : ((fShriekCompIso B (f ≫ g) h).hom ≫
        Functor.whiskerRight (fShriekCompIso B f g).hom (fShriekFunctor.{u, v} B h)).app F =
      compShriekMap B (f ≫ g) h F ≫ (fShriekFunctor.{u, v} B h).map (compShriekMap B f g F) :=
    rfl
  rw [e1, e2]
  simp only [Functor.map_comp]
  have s1 := fShriekCompIso_stalk B g h s ((fShriekFunctor.{u, v} B f).obj F)
  have s2 := fShriekCompIso_stalk B f (g ≫ h) s F
  have s3 := fShriekCompIso_stalk B (f ≫ g) h s F
  have s4 := fShriekStalkIso_natural.{u, v} B h s (compShriekMap B f g F)
  have s5 := fShriekStalkIso_congr B (Category.assoc f g h) s F
  rw [fShriekCompIso_hom_app] at s1 s2 s3
  have key : ∀ {P Q R S W : AddCommGrpCat} {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ S} {d : S ⟶ R}
      {w : R ⟶ W}, a ≫ b = c ≫ d → a ≫ b ≫ w = c ≫ d ≫ w := fun e => by
    rw [← Category.assoc, e, Category.assoc]
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) s1)))).trans ?_
  refine (congrArg (_ ≫ ·) (key s2)).trans ?_
  refine (key s5).trans ?_
  refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) s4)).symm
  refine Eq.trans ?_ (key s3).symm
  refine congrArg (_ ≫ ·) (ConcreteCategory.hom_ext _ _ fun ξ => ?_)
  exact compFiberStalksMap_assoc B f g h s F ξ

end Assoc

end AlgebraicGeometry.SmallEtale

end
