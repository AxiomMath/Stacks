module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UnitTorsorsOfInvertibleModules

/-!
# The module attached to a torsor under the units, in independent universes

For a ringed site `X : RingedSite.{u, v, w}` and a torsor `F` under the sheaf of units of the
structure sheaf, the coefficient sections over `U` are the families of maps from sections of `F`
to sections of the structure sheaf over the slice over `U`, compatible with restriction and
equivariant for the unit action twisted by inversion. They form a sheaf of modules, with sections
in `max u v w`; on an essentially `w`-small site it is sectionwise `w`-small and shrinks to a sheaf
of modules with sections in `w`.

## Main definitions

* `coefficientSheafLarge`: The sheaf of modules attached to a torsor under the units, with
  sections in `max u v w`.
* `coefficientSheaf'`: Its sectionwise `w`-small model, on an essentially `w`-small site.

## Main results

* `equivariantHomSubfunctor_isSheaf'`: The equivariant maps from a torsor to the structure sheaf
  form a sheaf.
* `small_coefficientSection`: The coefficient sections over an object are `w`-small when the site
  is essentially `w`-small.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u v w
namespace Stacks.Cohomology.Torsors.Generators

/-- Families assigning a section of the structure sheaf to every section of the torsor over an
object of the slice over `U`.

This generalizes `CoefficientFamily`, stated for `RingedSite.{u, u, u}`,
to independent universes. -/
abbrev CoefficientFamily' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C) :=
  ∀ V : Over U, F.1.presheaf.obj (op V.left) → X.O.obj.obj (op V.left)

/-- The module structure on the coefficient families, with scalars restricted along the
structure morphisms of the slice.

This generalizes `coefficientFamilyModule`, stated for `RingedSite.{u, u, u}`,
to independent universes. -/
@[instance_reducible] def coefficientFamilyModule' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C) :
    Module (X.O.obj.obj (op U)) (CoefficientFamily' X F U) :=
  @Pi.module _ _ _ _ _ (fun V =>
    @Pi.module _ _ _ _ _ (fun _ => Module.compHom _ (X.O.obj.map V.hom.op).hom))

attribute [local instance] coefficientFamilyModule'

/-- The submodule of coefficient families which are compatible with restriction and
equivariant for the unit action, with the action twisted by inversion.

This generalizes `coefficientSubmodule`, stated for `RingedSite.{u, u, u}`,
to independent universes. -/
def coefficientSubmodule' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C) :
    Submodule (X.O.obj.obj (op U)) (CoefficientFamily' X F U) where
  carrier := {a | (∀ (V W : Over U) (f : W ⟶ V) (s : F.1.presheaf.obj (op V.left)),
      a W (F.1.presheaf.map f.left.op s) = (X.O.obj.map f.left.op) (a V s)) ∧
    ∀ (V : Over U) (g : (X.O.obj.obj (op V.left))ˣ) (s : F.1.presheaf.obj (op V.left)),
      a V (F.1.act _ (Multiplicative.ofAdd (Additive.ofMul g)) s) =
        (g⁻¹ : (X.O.obj.obj (op V.left))ˣ).val * a V s}
  zero_mem' := ⟨fun _ _ f _ => (map_zero (X.O.obj.map f.left.op).hom).symm,
    fun _ _ _ => (mul_zero _).symm⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun V W f s => ?_, fun V g s => ?_⟩
    · change a W _ + b W _ = (X.O.obj.map f.left.op) (a V s + b V s)
      rw [ha, hb, map_add]
    · change a V _ + b V _ = _ * (a V s + b V s)
      rw [ha', hb', mul_add]
  smul_mem' := by
    rintro r a ⟨ha, ha'⟩
    refine ⟨fun V W f s => ?_, fun V g s => ?_⟩
    · change (X.O.obj.map W.hom.op) r * a W _ =
        (X.O.obj.map f.left.op) ((X.O.obj.map V.hom.op) r * a V s)
      rw [ha, map_mul]
      congr 1
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w f]
    · change (X.O.obj.map V.hom.op) r * a V _ = _ * ((X.O.obj.map V.hom.op) r * a V s)
      rw [ha', mul_left_comm]

/-- The sections over `U` of the module attached to a torsor.

This generalizes `CoefficientSection`, stated for `RingedSite.{u, u, u}`,
to independent universes. -/
abbrev CoefficientSection' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C) :=
  coefficientSubmodule' X F U

/-- Restriction of coefficient sections, by composing the slice.

This generalizes `coefficientSectionRestrict`, stated for `RingedSite.{u, u, u}`,
to independent universes. -/
def coefficientSectionRestrict' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X))
    {U V : X.C} (f : V ⟶ U) (a : CoefficientSection' X F U) : CoefficientSection' X F V :=
  ⟨fun W => a.val ((Over.map f).obj W), fun _ _ g s => a.property.1 _ _ ((Over.map f).map g) s,
    fun W g s => a.property.2 ((Over.map f).obj W) g s⟩

/-- The presheaf of modules attached to a torsor under the units.

This generalizes `coefficientPresheaf`, stated for `RingedSite.{u, u, u}`, to independent
universes; its sections lie in `max u v w`. -/
def coefficientPresheaf' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    PresheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj where
  obj U := ModuleCat.of (X.O.obj.obj U) (CoefficientSection' X F U.unop)
  map {U V} f := by
    letI : Module (X.O.obj.obj U)
        ((ModuleCat.restrictScalars
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).obj
          (ModuleCat.of (X.O.obj.obj V) (CoefficientSection' X F V.unop))) :=
      inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
        ((ModuleCat.restrictScalars
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).obj
          (ModuleCat.of (X.O.obj.obj V) (CoefficientSection' X F V.unop))))
    exact ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).obj
        (ModuleCat.of (X.O.obj.obj V) (CoefficientSection' X F V.unop))) {
      toFun := coefficientSectionRestrict' X F f.unop
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r a
        apply Subtype.ext
        funext W s
        change (X.O.obj.map (W.hom ≫ f.unop).op) r * _ =
          (X.O.obj.map W.hom.op) ((X.O.obj.map f) r) * _
        rw [op_comp, X.O.obj.map_comp]
        rfl }
  map_id U := by
    ext a
    apply Subtype.ext
    funext W s
    change a.val ((Over.map (𝟙 U.unop)).obj W) s = a.val W s
    simpa using (a.property.1 _ _ ((Over.mapId U.unop).inv.app W) s).symm
  map_comp {U V W} f g := by
    ext a
    apply Subtype.ext
    funext T s
    change a.val ((Over.map (f ≫ g).unop).obj T) s =
      a.val ((Over.map f.unop).obj ((Over.map g.unop).obj T)) s
    simpa using a.property.1 _ _ ((Over.mapComp g.unop f.unop).hom.app T) s

/-- The equivariant maps from the torsor to the structure sheaf, as a subfunctor of the internal
hom presheaf.

This generalizes `equivariantHomSubfunctor`, stated for `RingedSite.{u, u, u}`,
to independent universes. -/
def equivariantHomSubfunctor' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    Subfunctor (presheafHom F.1.presheaf (X.O.obj ⋙ forget CommRingCat)) where
  obj U := {a | ∀ (V : Over U.unop) (g : (X.O.obj.obj (op V.left))ˣ)
      (s : F.1.presheaf.obj (op V.left)),
      a.app (op V) (F.1.act _ (Multiplicative.ofAdd (Additive.ofMul g)) s) =
        @HMul.hMul (X.O.obj.obj (op V.left)) (X.O.obj.obj (op V.left))
          (X.O.obj.obj (op V.left)) inferInstance (g⁻¹).val (a.app (op V) s)}
  map f _ ha W g s := ha ((Over.map f.unop).obj W) g s

/-- The presheaf of modules attached to a torsor is the subfunctor of equivariant maps.

This generalizes `coefficientPresheafIso`, stated for `RingedSite.{u, u, u}`,
to independent universes. -/
def coefficientPresheafIso' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    (coefficientPresheaf' X F).presheaf ⋙ forget AddCommGrpCat ≅
      (equivariantHomSubfunctor' X F).toFunctor :=
  NatIso.ofComponents (fun U => Equiv.toIso {
    toFun := fun a => ⟨{
      app := fun V => ↾(a.val V.unop)
      naturality := by
        intro V W f
        ext s
        exact a.property.1 V.unop W.unop f.unop s }, a.property.2⟩
    invFun := fun a => ⟨fun V s => a.val.app (op V) s,
      (fun V W f s => NatTrans.naturality_apply a.val f.op s), a.property⟩
    left_inv := fun a => rfl
    right_inv := fun a => rfl }) (by intros; rfl)

/-- The equivariant maps from a torsor to the structure sheaf form a sheaf.

This generalizes `equivariantHomSubfunctor_isSheaf`, stated for `RingedSite.{u, u, u}`,
to independent universes. -/
theorem equivariantHomSubfunctor_isSheaf' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    Presheaf.IsSheaf X.J (equivariantHomSubfunctor' X F).toFunctor := by
  let R := X.O.obj ⋙ forget CommRingCat
  have hR : Presheaf.IsSheaf X.J R :=
    Presheaf.isSheaf_comp_of_isSheaf X.J _ _ X.O.property
  apply (isSheaf_iff_isSheaf_of_type X.J _).2
  rw [Subfunctor.isSheaf_iff (G := equivariantHomSubfunctor' X F)
    ((isSheaf_iff_isSheaf_of_type X.J _).1 (Presheaf.IsSheaf.hom F.1.presheaf R hR))]
  intro U a ha V g s
  apply (hR.isSheafFor (((equivariantHomSubfunctor' X F).sieveOfSection a).pullback V.hom)
    (X.J.pullback_stable _ ha)).isSeparatedFor.ext
  intro W f hf
  let gW : (X.O.obj.obj (op W))ˣ := Units.map (X.O.obj.map f.op).hom.toMonoidHom g
  have hnat (t : F.1.presheaf.obj (op V.left)) :
      a.app (op (Over.mk (f ≫ V.hom))) (F.1.presheaf.map f.op t) =
        R.map f.op (a.app (op V) t) :=
    NatTrans.naturality_apply a (Over.homMk f : Over.mk (f ≫ V.hom) ⟶ V).op t
  have hres : ((presheafHom F.1.presheaf R).map (f ≫ V.hom).op a).app (op (Over.mk (𝟙 W))) =
      a.app (op (Over.mk (f ≫ V.hom))) :=
    presheafHom_map_app (𝟙 W) (f ≫ V.hom) (f ≫ V.hom) (by simp) a
  have hlocal := hf (Over.mk (𝟙 W)) gW (F.1.presheaf.map f.op s)
  rw [hres] at hlocal
  have hact : F.1.presheaf.map f.op
      (F.1.act (op V.left) (Multiplicative.ofAdd (Additive.ofMul g)) s) =
      F.1.act (op W) (Multiplicative.ofAdd (Additive.ofMul gW))
        (F.1.presheaf.map f.op s) := F.1.naturality f.op _ s
  have hgW : (gW⁻¹ : (X.O.obj.obj (op W))ˣ).val =
      R.map f.op (g⁻¹ : (X.O.obj.obj (op V.left))ˣ).val := rfl
  calc R.map f.op (a.app (op V)
          (F.1.act (op V.left) (Multiplicative.ofAdd (Additive.ofMul g)) s))
      = a.app (op (Over.mk (f ≫ V.hom))) (F.1.presheaf.map f.op
          (F.1.act (op V.left) (Multiplicative.ofAdd (Additive.ofMul g)) s)) := (hnat _).symm
    _ = a.app (op (Over.mk (f ≫ V.hom)))
          (F.1.act (op W) (Multiplicative.ofAdd (Additive.ofMul gW))
            (F.1.presheaf.map f.op s)) := congrArg _ hact
    _ = @HMul.hMul (X.O.obj.obj (op W)) (X.O.obj.obj (op W)) (X.O.obj.obj (op W))
          inferInstance (gW⁻¹).val
          (a.app (op (Over.mk (f ≫ V.hom))) (F.1.presheaf.map f.op s)) := hlocal
    _ = @HMul.hMul (X.O.obj.obj (op W)) (X.O.obj.obj (op W)) (X.O.obj.obj (op W))
          inferInstance (R.map f.op (g⁻¹ : (X.O.obj.obj (op V.left))ˣ).val)
          (R.map f.op (a.app (op V) s)) := by rw [hgW, hnat s]
    _ = R.map f.op (@HMul.hMul (X.O.obj.obj (op V.left)) (X.O.obj.obj (op V.left))
          (X.O.obj.obj (op V.left)) inferInstance (g⁻¹).val (a.app (op V) s)) :=
        (map_mul (X.O.obj.map f.op).hom _ _).symm

/-- The sheaf of modules attached to a torsor under the units, with its sections in the
universe `max u v w` in which the construction lands. -/
def coefficientSheafLarge (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) :
    SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  ⟨coefficientPresheaf' X F,
    (Presheaf.isSheaf_iff_isSheaf_comp X.J (coefficientPresheaf' X F).presheaf
      (forget AddCommGrpCat)).2
      ((Presheaf.isSheaf_of_iso_iff (coefficientPresheafIso' X F)).2
        (equivariantHomSubfunctor_isSheaf' X F))⟩

/-- Restriction in the sheaf attached to a torsor is restriction of coefficient sections. -/
theorem coefficientSheafLarge_restrict (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X))
    {U V : X.C} (f : V ⟶ U) (a : CoefficientSection' X F U) :
    (coefficientSheafLarge X F).val.restrictₛₗ f.op a = coefficientSectionRestrict' X F f a := rfl

/-! ### Shrinking the attached module to the universe of the sections

A coefficient section over `U` is a family indexed by the slice `X.C/U`, so the sections of
`coefficientSheafLarge` live in `Type (max u v w)`, whereas a sheaf of modules on `X` has its
sections in `Type w`. On a site that is essentially `w`-small the raise is an artefact of the
construction: a coefficient section is compatible with restriction and the structure morphism of
an isomorphism of the slice is an isomorphism, so a coefficient section is determined by its
components on a `w`-small model of the slice. The attached module is therefore sectionwise
`w`-small, and `Stacks.SheafOfModules.sheafShrink` brings it down to `SheafOfModules.{w}`. -/

section EssentiallySmall

variable (X : RingedSite.{u, v, w}) [EssentiallySmall.{w} X.C]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X))

/-- **The coefficient sections over an object are `w`-small** when the site is essentially
`w`-small. Restriction to a `w`-small model of the slice over the object is injective: the
component of a coefficient section at an object of the slice determines its component at every
isomorphic object, because the section is compatible with restriction and the structure morphism
of an isomorphism of the slice is an isomorphism. -/
instance small_coefficientSection (U : X.C) : Small.{w} (CoefficientSection' X F U) := by
  have : EssentiallySmall.{w} (Over U) := Stacks.essentiallySmall_over.{w} U
  apply small_of_injective (f := fun a : CoefficientSection' X F U =>
    (fun (V : SmallModel.{w} (Over U)) =>
      a.val ((equivSmallModel.{w} (Over U)).inverse.obj V) :
      ∀ V : SmallModel.{w} (Over U),
        F.1.presheaf.obj (op ((equivSmallModel.{w} (Over U)).inverse.obj V).left) →
          X.O.obj.obj (op ((equivSmallModel.{w} (Over U)).inverse.obj V).left)))
  intro a b hab
  apply Subtype.ext
  funext W t
  set e : W ≅ (equivSmallModel.{w} (Over U)).inverse.obj
      ((equivSmallModel.{w} (Over U)).functor.obj W) :=
    (equivSmallModel.{w} (Over U)).unitIso.app W
  have hcomp : e.hom.left ≫ e.inv.left = 𝟙 W.left := by
    rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  set s := F.1.presheaf.map e.inv.left.op t with hs
  have hts : F.1.presheaf.map e.hom.left.op s = t := by
    rw [hs, ← Functor.map_comp_apply, ← op_comp, hcomp, op_id,
      Functor.map_id_apply]
  have ha := a.property.1 _ W e.hom s
  have hb := b.property.1 _ W e.hom s
  rw [hts] at ha hb
  have hV : a.val ((equivSmallModel.{w} (Over U)).inverse.obj
      ((equivSmallModel.{w} (Over U)).functor.obj W)) =
      b.val ((equivSmallModel.{w} (Over U)).inverse.obj
        ((equivSmallModel.{w} (Over U)).functor.obj W)) := congrFun hab _
  rw [ha, hb, hV]

/-- The sections of the attached module are `w`-small, in the spelling that
`Stacks.SheafOfModules.sheafShrink` consumes. -/
instance small_coefficientSheafLarge_obj (U : X.Cᵒᵖ) :
    Small.{w} ((coefficientSheafLarge X F).val.obj U) :=
  inferInstanceAs (Small.{w} (CoefficientSection' X F U.unop))

/-- **The sheaf of modules attached to a torsor under the units**, with its sections in the
universe of the sections of the structure sheaf: the sectionwise `w`-small model of
`coefficientSheafLarge`, whose universe lift it is.

This generalizes `coefficientSheaf`, stated for `RingedSite.{u, u, u}`, to an essentially
`w`-small site with independent universes. -/
def coefficientSheaf' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Stacks.SheafOfModules.sheafShrink.{w, max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (coefficientSheafLarge X F)

/-- The module structure on the coefficient sections with the scalars read through the sheaf of
rings of the site, which instance search does not find through the forgetful functor from
commutative rings. -/
@[instance_reducible] local instance coefficientSectionRingModule (U : X.C) :
    Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
      (CoefficientSection' X F U) :=
  inferInstanceAs (Module (X.O.obj.obj (op U)) (CoefficientSection' X F U))

/-- The sections of `coefficientSheaf'` over `U` are the coefficient sections over `U`. -/
def coefficientSheafEquiv (U : X.C) :
    (coefficientSheaf' X F).val.obj (op U) ≃ CoefficientSection' X F U :=
  Shrink.addEquiv.toEquiv

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Restriction in `coefficientSheaf'` is restriction of coefficient sections. -/
theorem coefficientSheafEquiv_restrict {U V : X.Cᵒᵖ} (f : U ⟶ V)
    (a : (coefficientSheaf' X F).val.obj U) :
    coefficientSheafEquiv X F V.unop ((coefficientSheaf' X F).val.restrictₛₗ f a) =
      coefficientSectionRestrict' X F f.unop (coefficientSheafEquiv X F U.unop a) :=
  Stacks.shrinkPresheaf_map_apply (coefficientSheafLarge X F).val.presheaf f a

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Multiplication in `coefficientSheaf'` is multiplication of coefficient sections. -/
theorem coefficientSheafEquiv_smul (U : X.C)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (a : (coefficientSheaf' X F).val.obj (op U)) :
    coefficientSheafEquiv X F U (r • a) = r • coefficientSheafEquiv X F U a :=
  Stacks.SheafOfModules.shrinkPresheaf_addEquiv_smul
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (coefficientSheafLarge X F).val (op U) r a

end EssentiallySmall

end Stacks.Cohomology.Torsors.Generators

end
