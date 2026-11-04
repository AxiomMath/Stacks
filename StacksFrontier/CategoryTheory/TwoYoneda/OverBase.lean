module

public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksAndLocalization
public import StacksFrontier.CategoryTheory.TwoYoneda.SplitModel

/-!
# The 2-Yoneda lemma over a morphism of the base

Let `C` be a category and `p : S ⥤ C` fibred in groupoids. The 2-Yoneda lemma
(`CategoryTheory.Functor.twoYonedaEvaluation_isEquivalence`) identifies the category
`Mor_{Cat/C}(C/U, S)` of functors over `C` on a fixed slice with the fibre `S_U`. This file
constructs the inverse of evaluation on morphisms: a morphism `m : G(1_U) ⟶ H(1_U)` of `S` over
`𝟙 U` extends to a unique 2-morphism `G ⟶ H`, whose component at `a` is the unique lift of
`𝟙 a.left` through the strongly cartesian arrow `H(a ⟶ 1_U)`.

The same works over a morphism of the base. For `r : U ⟶ V`, a functor `G` over `C` on `C/U` and
a functor `H` over `C` on `C/V`, a morphism `m : G(1_U) ⟶ H(1_V)` of `S` lying over `r` extends to
a 2-morphism from `G` to the restriction of `H` along `r`, characterised by the factorisation
`homOverBase.app 1_U ≫ H(1_U · r ⟶ 1_V) = m`.

## Main definitions

* `CategoryTheory.Functor.TwoYoneda.homOfUnitHom`: the 2-morphism extending a morphism between
  the values at `1_U` which lies over `𝟙 U`, i.e. the inverse of
  `CategoryTheory.Functor.twoYonedaEvaluation` on morphisms.
* `CategoryTheory.Functor.TwoYoneda.homOverBase`: the 2-morphism extending a morphism between the
  values at the unit objects which lies over a morphism `r : U ⟶ V` of the base.

## Main results

* `CategoryTheory.Functor.TwoYoneda.hom_ext_of_app_unit`: a 2-morphism of functors over `C` on a
  slice is determined by its component at the unit object.
* `CategoryTheory.Functor.TwoYoneda.homOverBase_fac`: the factorisation characterising
  `homOverBase`.
* `CategoryTheory.Functor.TwoYoneda.exists_basedFunctor_unitHom`: every object of a fibre is the
  value at the unit object of a functor over `C` on the slice, up to a vertical morphism.
* `CategoryTheory.Functor.TwoYoneda.exists_factorisation_of_unitHom`: a filling 2-morphism
  factors through a chosen lift as soon as it factors at the unit object.

## Implementation notes

`CategoryTheory.BasedCategory.ofFunctor` is made `implicit_reducible` locally: the `p` and
`category` fields of the based category attached to a functor have to reduce for the verticality
conditions in a `CategoryTheory.BasedNatTrans` to be recognised as the `IsHomLift` facts proved
about the underlying functors.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
-/

@[expose] public section

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.BasedFunctor.overMap

namespace CategoryTheory.Functor.TwoYoneda

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]

/-! ### Functors over `C` on a fixed slice -/

section FixedBase

variable (p : S ⥤ C) {U : C} {G H : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p}

/-- A functor over `C` on the slice `C/U` sends an arrow of `C/U` to an arrow of `S` over the
underlying arrow of `C`. -/
theorem isHomLift_map_slice {a b : Over U} (g : a ⟶ b) :
    p.IsHomLift g.left (G.map g) :=
  have h : (Over.forget U).IsHomLift ((Over.forget U).map g) g := IsHomLift.map g
  have : (BasedCategory.slice U).p.IsHomLift g.left g := h
  G.preserves_isHomLift _ _

/-- The composite of the image of the canonical arrow `a ⟶ 1_U` with a morphism over `𝟙 U` lies
over the structure morphism of `a`. -/
instance isHomLift_map_from_mkIdTerminal_comp
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 U))) [p.IsHomLift (𝟙 U) m] (a : Over U) :
    p.IsHomLift a.hom (G.map (Over.mkIdTerminal.from a) ≫ m) :=
  IsHomLift.comp_lift_id_right p a.hom (G.map (Over.mkIdTerminal.from a)) m

/-- The component at `a` of the 2-morphism extending a morphism `m : G(1_U) ⟶ H(1_U)` lying over
`𝟙 U`: the unique morphism over `𝟙 a.left` whose composite with the strongly cartesian arrow
`H(a ⟶ 1_U)` is `G(a ⟶ 1_U) ≫ m`. -/
noncomputable def unitHomApp (hp : p.IsFiberedInGroupoids)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 U))) (hm : p.IsHomLift (𝟙 U) m) (a : Over U) :
    G.obj a ⟶ H.obj a :=
  have := hm
  have := isStronglyCartesian_map_from_mkIdTerminal p hp U H a
  IsStronglyCartesian.map p a.hom (H.map (Over.mkIdTerminal.from a))
    (Category.id_comp a.hom).symm (G.map (Over.mkIdTerminal.from a) ≫ m)

/-- `unitHomApp` lies over an identity. -/
instance isHomLift_unitHomApp (hp : p.IsFiberedInGroupoids)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 U))) (hm : p.IsHomLift (𝟙 U) m) (a : Over U) :
    p.IsHomLift (𝟙 a.left) (unitHomApp p hp m hm a) :=
  have := hm
  have := isStronglyCartesian_map_from_mkIdTerminal p hp U H a
  IsStronglyCartesian.map_isHomLift p a.hom (H.map (Over.mkIdTerminal.from a))
    (Category.id_comp a.hom).symm (G.map (Over.mkIdTerminal.from a) ≫ m)

/-- The factorisation defining `unitHomApp`. -/
theorem unitHomApp_fac (hp : p.IsFiberedInGroupoids)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 U))) (hm : p.IsHomLift (𝟙 U) m) (a : Over U) :
    unitHomApp p hp m hm a ≫ H.map (Over.mkIdTerminal.from a) =
      G.map (Over.mkIdTerminal.from a) ≫ m :=
  have := hm
  have := isStronglyCartesian_map_from_mkIdTerminal p hp U H a
  IsStronglyCartesian.fac p a.hom (H.map (Over.mkIdTerminal.from a))
    (Category.id_comp a.hom).symm (G.map (Over.mkIdTerminal.from a) ≫ m)

/-- The 2-morphism of functors over `C` on `C/U` extending a morphism `m : G(1_U) ⟶ H(1_U)` of
`S` lying over `𝟙 U`. This is the inverse of the 2-Yoneda evaluation functor
`CategoryTheory.Functor.twoYonedaEvaluation` on morphisms. -/
noncomputable def homOfUnitHom (hp : p.IsFiberedInGroupoids)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 U))) (hm : p.IsHomLift (𝟙 U) m) : G ⟶ H where
  toNatTrans :=
    { app := unitHomApp p hp m hm
      naturality := fun a a' g => by
        have hgt : g ≫ Over.mkIdTerminal.from a' = Over.mkIdTerminal.from a :=
          Over.mkIdTerminal.hom_ext _ _
        have := hm
        have := isStronglyCartesian_map_from_mkIdTerminal p hp U H a'
        have hGg : p.IsHomLift g.left (G.map g) := isHomLift_map_slice p g
        have hHg : p.IsHomLift g.left (H.map g) := isHomLift_map_slice p g
        have h₁ : p.IsHomLift g.left (G.map g ≫ unitHomApp p hp m hm a') :=
          IsHomLift.comp_lift_id_right p g.left _ _
        have h₂ : p.IsHomLift g.left (unitHomApp p hp m hm a ≫ H.map g) :=
          IsHomLift.comp_lift_id_left p g.left _ _
        refine IsStronglyCartesian.ext p a'.hom (H.map (Over.mkIdTerminal.from a')) g.left ?_
        rw [Category.assoc, unitHomApp_fac, Category.assoc, ← H.map_comp, hgt,
          unitHomApp_fac, ← Category.assoc, ← G.map_comp, hgt] }
  isHomLift' := fun a => isHomLift_unitHomApp p hp m hm a

/-- The component of `homOfUnitHom` at an object `a` of `C/U` is `unitHomApp` at `a`. -/
@[simp]
theorem homOfUnitHom_app (hp : p.IsFiberedInGroupoids)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 U))) (hm : p.IsHomLift (𝟙 U) m) (a : Over U) :
    (homOfUnitHom p hp m hm).app a = unitHomApp p hp m hm a :=
  rfl

/-- The 2-morphism extending `m` evaluates to `m` at the unit object. -/
@[simp]
theorem homOfUnitHom_app_unit (hp : p.IsFiberedInGroupoids)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 U))) (hm : p.IsHomLift (𝟙 U) m) :
    (homOfUnitHom p hp m hm).app (Over.mk (𝟙 U)) = m := by
  have hterm : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
    Over.mkIdTerminal.hom_ext _ _
  have h := unitHomApp_fac p hp m hm (Over.mk (𝟙 U))
  rwa [hterm, H.map_id, Category.comp_id, G.map_id, Category.id_comp] at h

/-- A 2-morphism of functors over `C` on a slice `C/U` is determined by its component at the
unit object `1_U`, when the target of the functors is fibred in groupoids. -/
theorem hom_ext_of_app_unit (hp : p.IsFiberedInGroupoids) (η θ : G ⟶ H)
    (h : η.app (Over.mk (𝟙 U)) = θ.app (Over.mk (𝟙 U))) : η = θ := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext a
  have := isStronglyCartesian_map_from_mkIdTerminal p hp U H a
  have h₁ : p.IsHomLift (𝟙 a.left) (η.app a) := η.isHomLift' a
  have h₂ : p.IsHomLift (𝟙 a.left) (θ.app a) := θ.isHomLift' a
  refine IsStronglyCartesian.ext p a.hom (H.map (Over.mkIdTerminal.from a)) (𝟙 a.left) ?_
  rw [← η.toNatTrans.naturality, ← θ.toNatTrans.naturality, h]

/-- Every 2-morphism of functors over `C` on a slice into a category fibred in groupoids is
invertible. -/
theorem isIso_hom (hp : p.IsFiberedInGroupoids) (η : G ⟶ H) : IsIso η :=
  (isGroupoid_basedFunctor_slice p hp U).all_isIso η

end FixedBase

/-! ### Functors over `C` on slices along a morphism of the base -/

section OverBase

variable (p : S ⥤ C) {U V : C} (r : U ⟶ V)

/-- The canonical object `1_U · r` of `C/V`: the image of the unit object of `C/U` under the
restriction functor along `r`. -/
abbrev unitOver : Over V := (Over.map r).obj (Over.mk (𝟙 U))

variable {G : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p}
  {H : BasedCategory.slice V ⥤ᵇ BasedCategory.ofFunctor p}

/-- The image under a functor `H` over `C` on `C/V` of the canonical arrow `1_U · r ⟶ 1_V` lies
over `r`. -/
instance isHomLift_map_from_mkIdTerminal_unitOver :
    p.IsHomLift r (H.map (Over.mkIdTerminal.from (unitOver r))) := by
  simpa using isHomLift_map_from_mkIdTerminal p V H (unitOver r)

/-- The image under `H` of the canonical arrow `1_U · r ⟶ 1_V` is strongly cartesian over `r`. -/
theorem isStronglyCartesian_map_from_mkIdTerminal_unitOver (hp : p.IsFiberedInGroupoids) :
    p.IsStronglyCartesian r (H.map (Over.mkIdTerminal.from (unitOver r))) :=
  hp.isStronglyCartesian_homLift r (H.map (Over.mkIdTerminal.from (unitOver r)))

/-- `CategoryTheory.Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal_unitOver` for an object of
`C/V` equal to `1_U · r`. -/
theorem isHomLift_map_from_mkIdTerminal_of_eq (W : Over V) (hW : W = unitOver r) :
    p.IsHomLift r (H.map (Over.mkIdTerminal.from W)) := by
  subst hW
  infer_instance

/-- The morphism over `𝟙 U` obtained from `m : G(1_U) ⟶ H(1_V)` by the universal property of the
strongly cartesian arrow `H(1_U · r ⟶ 1_V)`. -/
noncomputable def unitHomOverBase (hp : p.IsFiberedInGroupoids)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 V))) (hm : p.IsHomLift r m) :
    G.obj (Over.mk (𝟙 U)) ⟶ H.obj (unitOver r) :=
  have := hm
  have := isStronglyCartesian_map_from_mkIdTerminal_unitOver p r (H := H) hp
  IsStronglyCartesian.map p r (H.map (Over.mkIdTerminal.from (unitOver r)))
    (Category.id_comp r).symm m

/-- The morphism `unitHomOverBase p r hp m hm` lies over `𝟙 U`. -/
instance isHomLift_unitHomOverBase (hp : p.IsFiberedInGroupoids)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 V))) (hm : p.IsHomLift r m) :
    p.IsHomLift (𝟙 U) (unitHomOverBase p r hp m hm) :=
  have := hm
  have := isStronglyCartesian_map_from_mkIdTerminal_unitOver p r (H := H) hp
  IsStronglyCartesian.map_isHomLift p r (H.map (Over.mkIdTerminal.from (unitOver r)))
    (Category.id_comp r).symm m

/-- The factorisation defining `unitHomOverBase`. -/
theorem unitHomOverBase_fac (hp : p.IsFiberedInGroupoids)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 V))) (hm : p.IsHomLift r m) :
    unitHomOverBase p r hp m hm ≫ H.map (Over.mkIdTerminal.from (unitOver r)) = m :=
  have := hm
  have := isStronglyCartesian_map_from_mkIdTerminal_unitOver p r (H := H) hp
  IsStronglyCartesian.fac p r (H.map (Over.mkIdTerminal.from (unitOver r)))
    (Category.id_comp r).symm m

/-- The 2-morphism of functors over `C` on `C/U` extending a morphism `m : G(1_U) ⟶ H(1_V)` of
`S` lying over `r : U ⟶ V`, with target the restriction of `H` along `r`. -/
noncomputable def homOverBase (hp : p.IsFiberedInGroupoids)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 V))) (hm : p.IsHomLift r m) :
    G ⟶ BasedFunctor.comp (BasedFunctor.overMap r) H :=
  homOfUnitHom p hp (H := BasedFunctor.comp (BasedFunctor.overMap r) H)
    (unitHomOverBase p r hp m hm) (isHomLift_unitHomOverBase p r hp m hm)

/-- The factorisation characterising `homOverBase`: its component at the unit object of `C/U`,
followed by the image under `H` of the canonical arrow `1_U · r ⟶ 1_V`, is `m`. -/
theorem homOverBase_fac (hp : p.IsFiberedInGroupoids)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 V))) (hm : p.IsHomLift r m) :
    (homOverBase p r hp m hm).app (Over.mk (𝟙 U)) ≫
        H.map (Over.mkIdTerminal.from (unitOver r)) = m := by
  show (homOfUnitHom p hp (H := BasedFunctor.comp (BasedFunctor.overMap r) H)
      (unitHomOverBase p r hp m hm) (isHomLift_unitHomOverBase p r hp m hm)).app
      (Over.mk (𝟙 U)) ≫ H.map (Over.mkIdTerminal.from (unitOver r)) = m
  rw [homOfUnitHom_app_unit, unitHomOverBase_fac]

end OverBase

/-- Every object of the fibre over `U` is the value at the unit object of a functor over `C` on
`C/U`, up to a morphism lying over `𝟙 U`. -/
theorem exists_basedFunctor_unitHom (p : S ⥤ C) (hp : p.IsFiberedInGroupoids) {U : C} (Z : S)
    (hZ : p.obj Z = U) :
    ∃ (G : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p)
      (c : G.obj (Over.mk (𝟙 U)) ⟶ Z), p.IsHomLift (𝟙 U) c :=
  have hc : p.IsHomLift (𝟙 U)
      (chosenLift p hp U ⟨Z, hZ⟩ (Over.mk (𝟙 U))).φ :=
    (chosenLift p hp U ⟨Z, hZ⟩ (Over.mk (𝟙 U))).isStronglyCartesian.toIsHomLift
  ⟨liftBased p hp U ⟨Z, hZ⟩, (chosenLift p hp U ⟨Z, hZ⟩ (Over.mk (𝟙 U))).φ, hc⟩

/-! ### Factoring a filling 2-morphism through a chosen lift -/

/-- Let `f` be a 1-morphism over `C` from `p` to `q`, let `G` be a functor over `C` on `C/U` into
`p`, let `H` be one on `C/V` into `q`, let `r : U ⟶ V`, and let `γ` be a 2-morphism from the
restriction of `H` along `r` to `G` followed by `f`. Suppose a functor `A` over `C` on `C/V` into
`p` is given, together with `m : G(1_U) ⟶ A(1_V)` lying over `r` and `b : H(1_V) ⟶ f(A(1_V))`
lying over `𝟙 V`, such that `γ` already factors through them at the unit object of `C/U`.

Then `γ` factors through `A` everywhere: there are 2-morphisms `α` from the restriction of `A`
along `r` to `G`, and `β` from `H` to `A` followed by `f`, with
`γ.app z = β.app (z · r) ≫ f (α.app z)` for every object `z` of `C/U`. -/
theorem exists_factorisation_of_unitHom {T : Type u₃} [Category.{v₃} T]
    (p : S ⥤ C) (q : T ⥤ C) (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    {U V : C} (r : U ⟶ V)
    {G : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p}
    {H : BasedCategory.slice V ⥤ᵇ BasedCategory.ofFunctor q}
    (f : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (γ : BasedFunctor.comp (BasedFunctor.overMap r) H ⟶ BasedFunctor.comp G f)
    (A : BasedCategory.slice V ⥤ᵇ BasedCategory.ofFunctor p)
    (m : G.obj (Over.mk (𝟙 U)) ⟶ A.obj (Over.mk (𝟙 V))) (hm : p.IsHomLift r m)
    (b : H.obj (Over.mk (𝟙 V)) ⟶ f.obj (A.obj (Over.mk (𝟙 V)))) (hb : q.IsHomLift (𝟙 V) b)
    (h : γ.app (Over.mk (𝟙 U)) ≫ f.map m =
      H.map (Over.mkIdTerminal.from (unitOver r)) ≫ b) :
    ∃ (α : BasedFunctor.comp (BasedFunctor.overMap r) A ⟶ G) (β : H ⟶ BasedFunctor.comp A f),
      ∀ z, γ.app z = β.app ((Over.map r).obj z) ≫ f.map (α.app z) := by
  have hδiso := isIso_hom p hp (homOverBase p r hp m hm)
  set δ := homOverBase p r hp m hm
  have hβunit := homOfUnitHom_app_unit q hq (G := H) (H := BasedFunctor.comp A f) b hb
  set β := homOfUnitHom q hq (G := H) (H := BasedFunctor.comp A f) b hb
  have hfac : δ.app (Over.mk (𝟙 U)) ≫ A.map (Over.mkIdTerminal.from (unitOver r)) = m :=
    homOverBase_fac p r hp m hm
  have heq : γ ≫ BasedCategory.whiskerRight δ f =
      BasedCategory.whiskerLeft (BasedFunctor.overMap r) β := by
    refine hom_ext_of_app_unit q hq _ _ ?_
    show γ.app (Over.mk (𝟙 U)) ≫ f.map (δ.app (Over.mk (𝟙 U))) = β.app (unitOver r)
    have hfA : q.IsHomLift r (f.map (A.map (Over.mkIdTerminal.from (unitOver r)))) :=
      f.preserves_isHomLift _ _
    have hcart := hq.isStronglyCartesian_homLift r
      (f.map (A.map (Over.mkIdTerminal.from (unitOver r))))
    have hleft : q.IsHomLift (𝟙 U)
        (γ.app (Over.mk (𝟙 U)) ≫ f.map (δ.app (Over.mk (𝟙 U)))) :=
      (γ ≫ BasedCategory.whiskerRight δ f).isHomLift' (Over.mk (𝟙 U))
    have hright : q.IsHomLift (𝟙 U) (β.app (unitOver r)) :=
      (BasedCategory.whiskerLeft (BasedFunctor.overMap r) β).isHomLift' (Over.mk (𝟙 U))
    refine IsStronglyCartesian.ext q r
      (f.map (A.map (Over.mkIdTerminal.from (unitOver r)))) (𝟙 U) ?_
    have hn := β.toNatTrans.naturality (Over.mkIdTerminal.from (unitOver r))
    change H.map (Over.mkIdTerminal.from (unitOver r)) ≫ β.app (Over.mk (𝟙 V)) =
      β.app (unitOver r) ≫ f.map (A.map (Over.mkIdTerminal.from (unitOver r))) at hn
    rw [hβunit] at hn
    rwa [Category.assoc, ← f.map_comp, hfac, h]
  refine ⟨_root_.CategoryTheory.inv δ, β, fun z => ?_⟩
  have he := congrArg (fun t => t.app z) heq
  change γ.app z ≫ f.map (δ.app z) = β.app ((Over.map r).obj z) at he
  rw [← he, Category.assoc, ← f.map_comp]
  have hd : δ.app z ≫ (_root_.CategoryTheory.inv δ).app z = 𝟙 _ :=
    congrArg (fun t => t.app z) (IsIso.hom_inv_id δ)
  rw [hd, f.map_id]
  exact (Category.comp_id _).symm

end CategoryTheory.Functor.TwoYoneda

end
