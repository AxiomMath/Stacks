module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompProperSupportStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProperBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProperBaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeIso

/-!
# The map `c'` of Stacks 0F79 and base change

Consider a diagram of a big étale site
```
X₁ --a--> X
|f₁       |f
v         v
Y₁ --b'-> Y
|g₁       |g
v         v
Z₁ --b--> Z
```
with both squares cartesian, `f`, `f₁` and the composites locally quasi-finite and `g`, `g₁`
separated and locally of finite type. The map `c' : (g ∘ f)_! ⟶ g_! ∘ f_!` of the proof of
Stacks 0F79 is compatible with base change: the base change isomorphism of Stacks 0F5J for the
outer rectangle followed by `c'` for `f₁` and `g₁` is `b⁻¹` of `c'` for `f` and `g`, followed by
the base change map of Stacks 0F55 for the lower square and `g₁_!` of the base change
isomorphism of Stacks 0F5J for the upper square.

The identity is checked on stalks at the geometric points of `Z₁`, read through the germs at the
points of the geometric fibres of `g₁` (Stacks 0F78), where every map is the identification of
stalks of inverse images (Stacks 03Q1) and of the stalk decompositions (Stacks 0F5F).

## Main results

* `AlgebraicGeometry.SmallEtale.properSupportFunctor_hom_ext_stalk` — morphisms into a
  proper-support direct image are determined by their stalks read at the points of the geometric
  fibres.
* `AlgebraicGeometry.SmallEtale.properSupportStalkEval_natural` — the map `(g_! G)_s ⟶ G_ȳ` is
  natural in `G`.
* `AlgebraicGeometry.SmallEtale.properSupportBaseChange_stalkEval` — the base change map of
  Stacks 0F55 on stalks, read at the points of the geometric fibres.
* `AlgebraicGeometry.SmallEtale.sepCompShriekMap_baseChange` — the compatibility of `c'` with
  base change.

## References

* [Stacks Project, Tag 0F79](https://stacks.math.columbia.edu/tag/0F79)
* [Stacks Project, Tag 0F55](https://stacks.math.columbia.edu/tag/0F55)
* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 0F78](https://stacks.math.columbia.edu/tag/0F78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section Eval

variable (B : BigEtaleSite.{u}) {Y Z : B.Scheme} (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map g)]

/-- The map `(g_! G)_s ⟶ G_ȳ` of Stacks 0F78 on the image under `ψ` of a germ: the germ of the
section of `G` obtained from the image of the section. -/
private theorem properSupportStalkEval_colim_map_germ
    {G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}}
    {A : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{max (u + 1) v}}
    (ψ : A ⟶ (properSupportFunctor.{u, max (u + 1) v} B g).obj G) (s : GeometricPoint Z.obj)
    (y : GeometricFiberPoint B g s) (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W) (σ : A.obj.obj (op W)) :
    properSupportStalkEval.{u, v} B g G s y
        (colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B Z.obj Z.property s)).op ψ.hom)
          (etaleGerm B Z.obj Z.property s A.obj W w σ)) =
      etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s) G.obj (baseChange B g W)
        (fiberPointElement B g s W w y) (properSupportSection B g G W (ψ.hom.app (op W) σ)) :=
  (congrArg _ (colim_map_etaleGerm.{u, v} B s ψ.hom W w σ)).trans
    (properSupportStalkEval_germ.{u, v} B g G s y W w _)

/-- **The map `(g_! G)_s ⟶ G_ȳ` of Stacks 0F78 is natural in `G`.** -/
public theorem properSupportStalkEval_natural
    {G H : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : G ⟶ H) (s : GeometricPoint Z.obj) (y : GeometricFiberPoint B g s) :
    colim.map (Functor.whiskerLeft (CategoryOfElements.π
        (geometricPointFiber B Z.obj Z.property s)).op
        ((properSupportFunctor.{u, max (u + 1) v} B g).map φ).hom) ≫
        properSupportStalkEval.{u, v} B g H s y =
      properSupportStalkEval.{u, v} B g G s y ≫
        colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B Y.obj Y.property (y.toGeometricPoint B g s))).op φ.hom) := by
  apply colimit.hom_ext
  rintro ⟨⟨W, w⟩⟩
  refine ConcreteCategory.hom_ext _ _ fun τ => ?_
  have h3 := properSupportStalkEval_germ.{u, v} B g G s y W w τ
  have h4 := colim_map_etaleGerm.{u, v} B (y.toGeometricPoint B g s) φ.hom (baseChange B g W)
    (fiberPointElement B g s W w y) (properSupportSection B g G W τ)
  have h5 := properSupportSection_map.{u, max (u + 1) v} B g φ W τ
  exact (properSupportStalkEval_colim_map_germ B g ((properSupportFunctor.{u, max (u + 1) v}
    B g).map φ) s y W w τ).trans ((congrArg (etaleGerm B Y.obj Y.property
      (y.toGeometricPoint B g s) H.obj (baseChange B g W) (fiberPointElement B g s W w y)) h5).trans
      (h4.symm.trans (congrArg _ h3.symm)))

/-- **Morphisms into the proper-support direct image are determined on stalks.** Two morphisms
`A ⟶ g_! G` agree as soon as their stalks at every geometric point `s` of `Z`, followed by the
maps `(g_! G)_s ⟶ G_ȳ` of Stacks 0F78 at the points `ȳ` of the geometric fibre of `g` over `s`,
agree. -/
public theorem properSupportFunctor_hom_ext_stalk
    {G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}}
    {A : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{max (u + 1) v}}
    {ψ₁ ψ₂ : A ⟶ (properSupportFunctor.{u, max (u + 1) v} B g).obj G}
    (h : ∀ (s : GeometricPoint Z.obj) (y : GeometricFiberPoint B g s),
      colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B Z.obj Z.property s)).op ψ₁.hom) ≫
          properSupportStalkEval.{u, v} B g G s y =
        colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B Z.obj Z.property s)).op ψ₂.hom) ≫
          properSupportStalkEval.{u, v} B g G s y) :
    ψ₁ = ψ₂ := by
  refine properSupportFunctor_hom_ext.{u, v} B g G fun s W w σ y => ?_
  exact (properSupportStalkEval_colim_map_germ B g ψ₁ s y W w σ).symm.trans
    ((ConcreteCategory.congr_hom (h s y) (etaleGerm B Z.obj Z.property s A.obj W w σ)).trans
      (properSupportStalkEval_colim_map_germ B g ψ₂ s y W w σ))

end Eval

section BaseChange

variable (B : BigEtaleSite.{u}) {Y Z Y₁ Z₁ : B.Scheme} (b' : Y₁ ⟶ Y) (g₁ : Y₁ ⟶ Z₁) (g : Y ⟶ Z)
  (b : Z₁ ⟶ Z) (sq : IsPullback b' g₁ g b) (s : GeometricPoint Z₁.obj)
  (y : GeometricFiberPoint B g₁ s)

/-- The comparison `Y₁ ×_{Z₁} W₁ ⟶ b'⁻¹(Y ×_Z W)`, `W₁ = W ×_Z Z₁`, carries the lift of a point of
the geometric fibre of `g₁` to the lift of the corresponding point of the geometric fibre of
`g`. -/
public theorem fiberPointElement_comp_fiberBaseChangeArrow (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property (s.map (B.inclusion.map b))).obj W) :
    (fiberPointElement B g₁ s (baseChange B b W) (geometricPointFiberBaseChangeEquiv B b s W w)
        y).1 ≫ (SmallEtale.toScheme B Y₁.obj Y₁.property).map
          (fiberBaseChangeArrow B b' g₁ g b sq W) ≫
        B.inclusion.map (pullback.fst (baseChange B g W).obj.hom b') =
      (fiberPointElement B g (s.map (B.inclusion.map b)) W w
        (fiberPointBaseChange B b' g₁ g b sq s y)).1 := by
  have hL : (SmallEtale.toScheme B Y₁.obj Y₁.property).map
        (fiberBaseChangeArrow B b' g₁ g b sq W) ≫
        B.inclusion.map (pullback.fst (baseChange B g W).obj.hom b') =
      B.inclusion.map (fiberBaseChangeMap B b' g₁ g b sq W) :=
    (B.inclusion.map_comp _ _).symm.trans
      (congrArg B.inclusion.map (fiberBaseChangeArrow_proj B b' g₁ g b sq W))
  rw [hL]
  refine ((IsPullback.of_hasPullback W.obj.hom g).map B.inclusion).hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (fiberPointLift_comp_fst B g _ W w _).symm
    refine (congrArg (_ ≫ ·) ((B.inclusion.map_comp _ _).symm.trans
      ((congrArg B.inclusion.map (fiberBaseChangeMap_fst B b' g₁ g b sq W)).trans
        (B.inclusion.map_comp _ _)))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (fiberPointLift_comp_fst B g₁ s (baseChange B b W) _ y)).trans ?_
    exact geometricPointFiberBaseChangeEquiv_comp_fst B b s W w
  · refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (fiberPointLift_comp_snd B g _ W w _).symm
    refine (congrArg (_ ≫ ·) ((B.inclusion.map_comp _ _).symm.trans
      ((congrArg B.inclusion.map (fiberBaseChangeMap_snd B b' g₁ g b sq W)).trans
        (B.inclusion.map_comp _ _)))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ B.inclusion.map b')
      (fiberPointLift_comp_snd B g₁ s (baseChange B b W) _ y)

variable [LocallyOfFiniteType (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g₁)]
  (G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})

/-- **The base change map of Stacks 0F55 on stalks.** For a point `ȳ` of the geometric fibre of
`g₁` over a geometric point `s` of `Z₁`, the stalk at `s` of `b⁻¹ g_! G ⟶ g₁_! b'⁻¹ G`, read at
`ȳ` (Stacks 0F78) and through the identifications of the stalks of inverse images (Stacks 03Q1),
is the map `(g_! G)_{b(s)} ⟶ G_{b'(ȳ)}` of Stacks 0F78 at the point `b' ∘ ȳ` of the geometric
fibre of `g` over `b ∘ s`. -/
public theorem properSupportBaseChange_stalkEval :
    (etaleStalkSmallEtalePullObjIso B b s AddCommGrpCat.{max (u + 1) v}
        ((properSupportFunctor.{u, max (u + 1) v} B g).obj G)).inv ≫
        (etaleStalkPresheafFunctor B Z₁.obj Z₁.property s AddCommGrpCat.{max (u + 1) v}).map
          (properSupportBaseChange.{u, v} B b' g₁ g b sq G).hom ≫
        properSupportStalkEval.{u, v} B g₁ ((abPullback.{u, v} B b').obj G) s y ≫
        (etaleStalkSmallEtalePullObjIso B b' (y.toGeometricPoint B g₁ s)
          AddCommGrpCat.{max (u + 1) v} G).hom =
      properSupportStalkEval.{u, v} B g G (s.map (B.inclusion.map b))
        (fiberPointBaseChange B b' g₁ g b sq s y) := by
  apply colimit.hom_ext
  rintro ⟨⟨W, w⟩⟩
  refine ConcreteCategory.hom_ext _ _ fun τ => ?_
  have ha := properSupportBaseChange_stalk_germ.{u, v} B b' g₁ g b sq G s ⟨W, w⟩ τ
  have hb := properSupportStalkEval_germ.{u, v} B g₁ ((abPullback.{u, v} B b').obj G) s y
    (baseChange B b W) (geometricPointFiberBaseChangeEquiv B b s W w)
    ((properSupportBaseChangePushforward.{u, v} B b' g₁ g b sq G).hom.app (op W) τ)
  have hd := AlgebraicGeometry.etaleGerm_pullbackSectionAlongHom.{u, v} B b'
    (y.toGeometricPoint B g₁ s) G
    (baseChange B g₁ (baseChange B b W))
    (fiberPointElement B g₁ s (baseChange B b W) (geometricPointFiberBaseChangeEquiv B b s W w) y)
    (baseChange B g W)
    (fiberPointElement B g (s.map (B.inclusion.map b)) W w
      (fiberPointBaseChange B b' g₁ g b sq s y))
    (fiberBaseChangeArrow B b' g₁ g b sq W)
    (fiberPointElement_comp_fiberBaseChangeArrow B b' g₁ g b sq s y W w)
    (properSupportSection B g G W τ)
  have he := properSupportStalkEval_germ.{u, v} B g G (s.map (B.inclusion.map b))
    (fiberPointBaseChange B b' g₁ g b sq s y) W w τ
  exact (congrArg (fun z => (etaleStalkSmallEtalePullObjIso B b' (y.toGeometricPoint B g₁ s)
      AddCommGrpCat.{max (u + 1) v} G).hom (properSupportStalkEval.{u, v} B g₁
        ((abPullback.{u, v} B b').obj G) s y z)) ha).trans
    ((congrArg (etaleStalkSmallEtalePullObjIso B b' (y.toGeometricPoint B g₁ s)
      AddCommGrpCat.{max (u + 1) v} G).hom hb).trans (hd.trans he.symm))

end BaseChange

section Main

/-- A colimit of a composite of morphisms of sheaves, restricted along the projection of a
category of elements, is the composite of the colimits. -/
private theorem colim_map_whiskerLeft_comp {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {E : Type*} [Category* E] (π : E ⥤ Cᵒᵖ)
    [HasColimitsOfShape E AddCommGrpCat.{u + 1}]
    {P Q R : Sheaf J AddCommGrpCat.{u + 1}} (α : P ⟶ Q) (β : Q ⟶ R) :
    colim.map (Functor.whiskerLeft π (α ≫ β).hom) =
      colim.map (Functor.whiskerLeft π α.hom) ≫ colim.map (Functor.whiskerLeft π β.hom) :=
  (congrArg colim.map (Functor.whiskerLeft_comp π α.hom β.hom)).trans (colim.map_comp _ _)

variable (B : BigEtaleSite.{u}) {X Y Z X₁ Y₁ Z₁ : B.Scheme}
  (f : X ⟶ Y) (g : Y ⟶ Z) (a : X₁ ⟶ X) (f₁ : X₁ ⟶ Y₁) (b' : Y₁ ⟶ Y) (g₁ : Y₁ ⟶ Z₁)
  (b : Z₁ ⟶ Z) (sq₁ : IsPullback a f₁ f b') (sq₂ : IsPullback b' g₁ g b)

/-- **The map `c'` of Stacks 0F79 and base change.** For two cartesian squares on top of each
other, with `f`, `f₁` and the composites locally quasi-finite and `g`, `g₁` separated and
locally of finite type, the base change isomorphism of Stacks 0F5J for the outer rectangle
followed by `c'` for `f₁` and `g₁` is `b⁻¹` of `c'` for `f` and `g`, followed by the base change
map of Stacks 0F55 for the lower square and `g₁_!` of the base change isomorphism of Stacks 0F5J
for the upper square. -/
public theorem sepCompShriekMap_baseChange
    [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [LocallyQuasiFinite (B.inclusion.map (f ≫ g))]
    [IsSeparated (B.inclusion.map g₁)] [LocallyOfFiniteType (B.inclusion.map g₁)]
    [LocallyOfFiniteType (B.inclusion.map f₁)] [LocallyQuasiFinite (B.inclusion.map f₁)]
    [LocallyQuasiFinite (B.inclusion.map (f₁ ≫ g₁))]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (fShriekBaseChangeNatIso.{u} B a (f₁ ≫ g₁) (f ≫ g) b (sq₁.paste_vert sq₂)).hom.app F ≫
        sepCompShriekMap.{u, u + 1} B f₁ g₁ ((abPullback.{u, u + 1} B a).obj F) =
      (abPullback.{u, u + 1} B b).map (sepCompShriekMap.{u, u + 1} B f g F) ≫
        properSupportBaseChange.{u, u + 1} B b' g₁ g b sq₂
          ((fShriekFunctor.{u, u + 1} B f).obj F) ≫
        (properSupportFunctor.{u, u + 1} B g₁).map
          ((fShriekBaseChangeNatIso.{u} B a f₁ f b' sq₁).hom.app F) := by
  refine properSupportFunctor_hom_ext_stalk.{u, u + 1} B g₁ fun s y => ?_
  let y' := y.toGeometricPoint B g₁ s
  let G₁ := (abPullback.{u, u + 1} B a).obj F
  refine (cancel_mono (fShriekStalkIso.{u, u + 1} B f₁ y' G₁).hom).1 ?_
  refine ConcreteCategory.hom_ext _ _ fun t => DFinsupp.ext fun x => ?_
  let t₀ := (etaleStalkSmallEtalePullObjIso B b s AddCommGrpCat.{u + 1}
    ((fShriekFunctor.{u, u + 1} B (f ≫ g)).obj F)).hom t
  -- the left-hand side
  have l1 := sepCompShriekMap_stalk.{u, u + 1} B f₁ g₁ G₁ s y x
    ((etaleStalkPresheafFunctor B Z₁.obj Z₁.property s AddCommGrpCat.{u + 1}).map
      ((fShriekBaseChangeNatIso.{u} B a (f₁ ≫ g₁) (f ≫ g) b (sq₁.paste_vert sq₂)).hom.app F).hom
      t)
  have l2 := ConcreteCategory.congr_hom (fShriekBaseChangeNatIso_stalk.{u} B a (f₁ ≫ g₁) (f ≫ g)
    b (sq₁.paste_vert sq₂) s F) t
  -- the right-hand side
  let c := sepCompShriekMap.{u, u + 1} B f g F
  let t₁ := (etaleStalkPresheafFunctor B Z.obj Z.property (s.map (B.inclusion.map b))
    AddCommGrpCat.{u + 1}).map c.hom t₀
  have r1 := ConcreteCategory.congr_hom ((smallEtalePullbackSheafFiberIso B b s
    AddCommGrpCat.{u + 1}).hom.naturality c) t
  have r2 := ConcreteCategory.congr_hom (properSupportBaseChange_stalkEval.{u, u + 1} B b' g₁ g b
    sq₂ s y ((fShriekFunctor.{u, u + 1} B f).obj F)) t₁
  have r3 := ConcreteCategory.congr_hom (properSupportStalkEval_natural.{u, u + 1} B g₁
    ((fShriekBaseChangeNatIso.{u} B a f₁ f b' sq₁).hom.app F) s y)
  have r4 := ConcreteCategory.congr_hom (fShriekBaseChangeNatIso_stalk.{u} B a f₁ f b' sq₁ y' F)
  have r5 := sepCompShriekMap_stalk.{u, u + 1} B f g F (s.map (B.inclusion.map b))
    (fiberPointBaseChange B b' g₁ g b sq₂ s y) (fiberPointBaseChange B a f₁ f b' sq₁ y' x) t₀
  let IG := etaleStalkSmallEtalePullObjIso B b s AddCommGrpCat.{u + 1}
    ((properSupportFunctor.{u, u + 1} B g).obj ((fShriekFunctor.{u, u + 1} B f).obj F))
  let w := colim.map (Functor.whiskerLeft (CategoryOfElements.π
    (geometricPointFiber B Z₁.obj Z₁.property s)).op ((abPullback.{u, u + 1} B b).map c).hom) t
  have hw : IG.inv t₁ = w := (congrArg IG.inv r1.symm).trans (Iso.hom_inv_id_apply IG w)
  rw [colim_map_whiskerLeft_comp, colim_map_whiskerLeft_comp, colim_map_whiskerLeft_comp]
  refine (l1.trans (congrArg (fun m => (m : fiberStalks.{u, u + 1} B (f₁ ≫ g₁) s G₁)
    (compFiberPointOf B f₁ g₁ s y x)) l2)).trans ?_
  refine Eq.symm ((congrArg (fun m => ((fShriekStalkIso.{u, u + 1} B f₁ y' G₁).hom m :
    fiberStalks.{u, u + 1} B f₁ y' G₁) x) (r3 _)).trans ?_)
  refine (congrArg (fun m => (m : fiberStalks.{u, u + 1} B f₁ y' G₁) x) (r4 _)).trans ?_
  refine congrArg (fiberStalkBaseChangeIso.{u, u + 1} B a f₁ f b' sq₁ y' F x).hom ?_
  refine (congrArg (fun m => ((fShriekStalkIso.{u, u + 1} B f (y'.map (B.inclusion.map b')) F).hom
    m : fiberStalks.{u, u + 1} B f _ F) (fiberPointBaseChange B a f₁ f b' sq₁ y' x)) ?_).trans r5
  refine Eq.trans ?_ r2
  exact congrArg (fun z => (etaleStalkSmallEtalePullObjIso B b' y' AddCommGrpCat.{u + 1}
    ((fShriekFunctor.{u, u + 1} B f).obj F)).hom (properSupportStalkEval.{u, u + 1} B g₁
      ((abPullback.{u, u + 1} B b').obj ((fShriekFunctor.{u, u + 1} B f).obj F)) s y
      ((etaleStalkPresheafFunctor B Z₁.obj Z₁.property s AddCommGrpCat.{u + 1}).map
        (properSupportBaseChange.{u, u + 1} B b' g₁ g b sq₂
          ((fShriekFunctor.{u, u + 1} B f).obj F)).hom z))) hw.symm

end Main

end AlgebraicGeometry.SmallEtale
