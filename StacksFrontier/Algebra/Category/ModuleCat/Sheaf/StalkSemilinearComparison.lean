module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatStalk

/-!
# Semilinear comparison of the fibre of a presheaf of modules with a module stalk

Let `(C, J)` be a site, `Φ` a point of it, `O` a sheaf of commutative rings on `C` and `M` a
sheaf of `O`-modules. Let `R` be a commutative ring identified with the stalk `O_Φ` by a ring
isomorphism `e`, let `P` be a presheaf of `R`-modules, and let `τ : P ⟶ M` be a morphism of
presheaves of abelian groups which is semilinear over a family of ring maps `R → O(U)` whose
germs are `e`, and which the fibre functor at `Φ` inverts. This file identifies the fibre of `P`
at `Φ` with the stalk of `M` at `Φ`, as `R`-modules after restriction of scalars along `e`.

The identification is pinned down by its effect on germs: a section of `P` over a neighbourhood
of `Φ` goes to the germ of its image under `τ`. That formula is what makes the identification
natural in the triple `(P, M, τ)`, and naturality is what upgrades it from a comparison of
objects to a comparison of functors at use sites.

## Main definitions

* `Stacks.moduleStalkForget₂Iso` : the comparison on underlying abelian groups.
* `Stacks.moduleStalkIso` : the comparison as an isomorphism of `R`-modules.

## Main results

* `Stacks.moduleStalkIso_hom_toPresheafFiber` : the comparison takes the germ of a section of `P`
  to the germ of its image under `τ`.
* `Stacks.moduleStalkIso_naturality` : the comparison is natural in the triple `(P, M, τ)`.
* `Stacks.moduleStalkGerm_naturality` : the germ maps into a module stalk are natural in the
  sheaf of modules.

## Implementation notes

The fibre of `P` is taken in `ModuleCat R` by Mathlib's `presheafFiber`, not by
`Stacks.presheafModuleFiber`: the ring `R` is constant, so no module structure over a filtered
colimit of rings is involved on that side. On the other side the module stalk is
`Stacks.moduleStalk`, whose underlying abelian group is the fibre of the underlying presheaf of
abelian groups on the nose, by `Stacks.presheafModuleFiberCompForget₂`. The only comparison that
has to be constructed is therefore the one expressing that the forgetful functor
`ModuleCat R ⥤ AddCommGrpCat` commutes with the colimit defining the fibre.

## References

* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe z v u rr

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{z} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{z} RingCat.{z})]
  (Φ : J.Point.{z}) (O : Sheaf J CommRingCat.{z})

/-! ### The fibre and sheafification functors preserve zero morphisms -/

section ZeroMorphisms

universe uA vA

/-- The fibre functor at a point of a site preserves zero morphisms: each leg of the colimit
cocone defining the fibre composes to zero with the induced map. -/
instance presheafFiber_preservesZeroMorphisms (Φ : J.Point.{z}) {A : Type uA} [Category.{vA} A]
    [HasZeroMorphisms A] [HasColimitsOfSize.{z, z} A] :
    (Φ.presheafFiber (A := A)).PreservesZeroMorphisms where
  map_zero P Q := by
    apply Φ.presheafFiber_hom_ext
    intro U x
    rw [Φ.toPresheafFiber_naturality]
    simp

variable {R₀ : Cᵒᵖ ⥤ RingCat.{z}} {R : Sheaf J RingCat.{z}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]

/-- Sheafification of presheaves of modules along `α`, followed by passage to the underlying
presheaf of abelian groups, preserves zero morphisms. -/
instance sheafificationCompForgetCompToPresheaf_preservesZeroMorphisms :
    (PresheafOfModules.sheafification.{z} α ⋙ SheafOfModules.forget R ⋙
      PresheafOfModules.toPresheaf R.obj).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso
    (PresheafOfModules.sheafificationCompForgetCompToPresheaf α).symm

/-- Sheafification of presheaves of modules along a locally bijective morphism of presheaves of
rings preserves zero morphisms: it does so on underlying presheaves of abelian groups, where it
is sheafification of presheaves. -/
instance sheafification_preservesZeroMorphisms :
    (PresheafOfModules.sheafification.{z} α).PreservesZeroMorphisms where
  map_zero M N :=
    (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map_injective
      (((PresheafOfModules.sheafification.{z} α ⋙ SheafOfModules.forget R ⋙
          PresheafOfModules.toPresheaf R.obj).map_zero M N).trans
        ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map_zero _ _).symm)

end ZeroMorphisms

/-! ### Naturality of the germ maps -/

/-- The germ maps into the stalk of a sheaf of modules are natural in the sheaf of modules. -/
lemma moduleStalkGerm_naturality
    {M M' : SheafOfModules.{z} (commRingSheafToRingSheaf O)} (g : M ⟶ M')
    (U : C) (x : Φ.fiber.obj U) (m : M.val.obj (op U)) :
    (sheafModuleFiberOfCommRing Φ O).map g (moduleStalkGerm Φ O M U x m) =
      moduleStalkGerm Φ O M' U x (g.val.app (op U) m) :=
  toPresheafModuleFiber_naturality Φ g.val U x m

/-! ### The comparison on underlying abelian groups -/

section

variable {R : Type rr} [CommRing R] (P : Cᵒᵖ ⥤ ModuleCat.{z} R)

/-- The fibre at `Φ` of a presheaf of `R`-modules has, as underlying abelian group, the fibre of
the underlying presheaf of abelian groups: the forgetful functor preserves the colimit defining
the fibre. -/
def presheafFiberForget₂Iso :
    (forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z}).obj
        ((Φ.presheafFiber (A := ModuleCat.{z} R)).obj P) ≅
      (Φ.presheafFiber (A := AddCommGrpCat.{z})).obj
        (P ⋙ forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z}) :=
  preservesColimitIso (forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z})
    ((CategoryOfElements.π Φ.fiber).op ⋙ P)

omit [LocallySmall.{z} C] [J.HasSheafCompose (forget₂ CommRingCat.{z} RingCat.{z})] in
/-- `Stacks.presheafFiberForget₂Iso` takes the germ of a section of `P` to its germ in the fibre
of the underlying presheaf of abelian groups. -/
lemma presheafFiberForget₂Iso_hom_toPresheafFiber (U : C) (x : Φ.fiber.obj U)
    (m : P.obj (op U)) :
    (presheafFiberForget₂Iso Φ P).hom
        ((forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z}).map (Φ.toPresheafFiber U x P) m) =
      Φ.toPresheafFiber U x (P ⋙ forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z}) m :=
  ConcreteCategory.congr_hom
    (ι_preservesColimitIso_hom (forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z})
      ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op ⟨U, x⟩)) m

variable (M : SheafOfModules.{z} (commRingSheafToRingSheaf O))
  (τ : P ⋙ forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z} ⟶ M.val.presheaf)

/-- The comparison between the fibre of `P` and the stalk of `M`, on underlying abelian groups:
the fibre of `τ`, read through `Stacks.presheafFiberForget₂Iso`. -/
def moduleStalkForget₂Iso [IsIso (Φ.presheafFiber.map τ)] :
    (forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z}).obj
        ((Φ.presheafFiber (A := ModuleCat.{z} R)).obj P) ≅
      (Φ.presheafFiber (A := AddCommGrpCat.{z})).obj M.val.presheaf :=
  presheafFiberForget₂Iso Φ P ≪≫ asIso (Φ.presheafFiber.map τ)

/-- The comparison takes the germ at a neighbourhood of a section of `P` to the germ of its image
under `τ`. -/
lemma moduleStalkForget₂Iso_hom_toPresheafFiber [IsIso (Φ.presheafFiber.map τ)]
    (U : C) (x : Φ.fiber.obj U) (m : P.obj (op U)) :
    (moduleStalkForget₂Iso Φ O P M τ).hom (Φ.toPresheafFiber U x P m) =
      moduleStalkGerm Φ O M U x (τ.app (op U) m) := by
  show (Φ.presheafFiber.map τ) ((presheafFiberForget₂Iso Φ P).hom
    ((forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z}).map (Φ.toPresheafFiber U x P) m)) = _
  rw [presheafFiberForget₂Iso_hom_toPresheafFiber Φ P U x m,
    Φ.toPresheafFiber_naturality_apply τ U x m]
  rfl

end

/-! ### The comparison as an isomorphism of modules -/

section

variable {R : Type rr} [CommRing R] (P : Cᵒᵖ ⥤ ModuleCat.{z} R)
  (M : SheafOfModules.{z} (commRingSheafToRingSheaf O))
  (τ : P ⋙ forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z} ⟶ M.val.presheaf)
  (e : R ≃+* (Φ.presheafFiber (A := CommRingCat.{z})).obj O.obj)
  (a : ∀ U : Cᵒᵖ, R →+* O.obj.obj U)

/-- **The fibre of `P` is the stalk of `M`.** The fibre at `Φ` of a presheaf of `R`-modules `P`
mapping to a sheaf of `O`-modules `M` by a morphism `τ` which the fibre functor inverts and which
is semilinear over the ring maps `a` is the stalk of `M` at `Φ`, as an `R`-module through the
identification `e` of `R` with the stalk of `O`. -/
def moduleStalkIso [IsIso (Φ.presheafFiber.map τ)]
    (ha : ∀ (U : C) (x : Φ.fiber.obj U) (r : R), ringStalkGerm Φ O U x (a (op U) r) = e r)
    (hτ : ∀ (U : Cᵒᵖ) (r : R) (m : P.obj U),
      letI : Module (O.obj.obj U) (M.val.presheaf.obj U) := (M.val.obj U).isModule
      τ.app U (r • m) = a U r • τ.app U m) :
    (Φ.presheafFiber (A := ModuleCat.{z} R)).obj P ≅
      (ModuleCat.restrictScalars e.toRingHom).obj (moduleStalk Φ O M) :=
  ModuleCat.isoMk (moduleStalkForget₂Iso Φ O P M τ) (by
    let : Module ((Φ.presheafFiber (A := CommRingCat.{z})).obj O.obj)
        ↑((Φ.presheafFiber (A := AddCommGrpCat.{z})).obj M.val.presheaf) :=
      (moduleStalk Φ O M).isModule
    have hpres : PreservesColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P)
        (forget (ModuleCat.{z} R)) := by
      change PreservesColimit _
        (forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z} ⋙ forget AddCommGrpCat.{z})
      infer_instance
    have key : ∀ (r : R) (n : ↑((Φ.presheafFiber (A := ModuleCat.{z} R)).obj P)),
        (moduleStalkForget₂Iso Φ O P M τ).hom (r • n) =
          e r • (moduleStalkForget₂Iso Φ O P M τ).hom n := by
      intro r n
      obtain ⟨j, m, rfl⟩ :=
        Concrete.colimit_exists_rep ((CategoryOfElements.π Φ.fiber).op ⋙ P) n
      obtain ⟨⟨U, x⟩⟩ := j
      change (moduleStalkForget₂Iso Φ O P M τ).hom (r • Φ.toPresheafFiber U x P m) =
        e r • (moduleStalkForget₂Iso Φ O P M τ).hom (Φ.toPresheafFiber U x P m)
      rw [← (Φ.toPresheafFiber U x P).hom.map_smul,
        moduleStalkForget₂Iso_hom_toPresheafFiber, moduleStalkForget₂Iso_hom_toPresheafFiber,
        hτ, ← ha U x r]
      exact moduleStalkGerm_smul Φ O M U x (a (op U) r) (τ.app (op U) m)
    intro r
    ext n
    exact (key r n).symm)

/-- The comparison takes the germ at a neighbourhood of a section of `P` to the germ of its image
under `τ`. -/
@[simp]
lemma moduleStalkIso_hom_toPresheafFiber [IsIso (Φ.presheafFiber.map τ)]
    (ha : ∀ (U : C) (x : Φ.fiber.obj U) (r : R), ringStalkGerm Φ O U x (a (op U) r) = e r)
    (hτ : ∀ (U : Cᵒᵖ) (r : R) (m : P.obj U),
      letI : Module (O.obj.obj U) (M.val.presheaf.obj U) := (M.val.obj U).isModule
      τ.app U (r • m) = a U r • τ.app U m)
    (U : C) (x : Φ.fiber.obj U) (m : P.obj (op U)) :
    (moduleStalkIso Φ O P M τ e a ha hτ).hom (Φ.toPresheafFiber U x P m) =
      moduleStalkGerm Φ O M U x (τ.app (op U) m) :=
  moduleStalkForget₂Iso_hom_toPresheafFiber Φ O P M τ U x m

end

/-! ### Naturality -/

section

variable {R : Type rr} [CommRing R]
  (e : R ≃+* (Φ.presheafFiber (A := CommRingCat.{z})).obj O.obj)
  (a : ∀ U : Cᵒᵖ, R →+* O.obj.obj U)
  (ha : ∀ (U : C) (x : Φ.fiber.obj U) (r : R), ringStalkGerm Φ O U x (a (op U) r) = e r)

/-- **The comparison is natural.** A morphism `φ : P ⟶ P'` of presheaves of `R`-modules and a
morphism `g : M ⟶ M'` of sheaves of `O`-modules which are compatible with the comparison
morphisms `τ` and `τ'` induce a commuting square of fibres and stalks. -/
lemma moduleStalkIso_naturality
    {P P' : Cᵒᵖ ⥤ ModuleCat.{z} R}
    {M M' : SheafOfModules.{z} (commRingSheafToRingSheaf O)}
    (τ : P ⋙ forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z} ⟶ M.val.presheaf)
    (τ' : P' ⋙ forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z} ⟶ M'.val.presheaf)
    [IsIso (Φ.presheafFiber.map τ)] [IsIso (Φ.presheafFiber.map τ')]
    (hτ : ∀ (U : Cᵒᵖ) (r : R) (m : P.obj U),
      letI : Module (O.obj.obj U) (M.val.presheaf.obj U) := (M.val.obj U).isModule
      τ.app U (r • m) = a U r • τ.app U m)
    (hτ' : ∀ (U : Cᵒᵖ) (r : R) (m : P'.obj U),
      letI : Module (O.obj.obj U) (M'.val.presheaf.obj U) := (M'.val.obj U).isModule
      τ'.app U (r • m) = a U r • τ'.app U m)
    (φ : P ⟶ P') (g : M ⟶ M')
    (hcompat : ∀ (U : Cᵒᵖ) (m : P.obj U), τ'.app U (φ.app U m) = g.val.app U (τ.app U m)) :
    (Φ.presheafFiber (A := ModuleCat.{z} R)).map φ ≫
        (moduleStalkIso Φ O P' M' τ' e a ha hτ').hom =
      (moduleStalkIso Φ O P M τ e a ha hτ).hom ≫
        (ModuleCat.restrictScalars e.toRingHom).map
          ((sheafModuleFiberOfCommRing Φ O).map g) := by
  apply Φ.presheafFiber_hom_ext
  intro U x
  apply ConcreteCategory.ext_apply
  intro m
  show (moduleStalkIso Φ O P' M' τ' e a ha hτ').hom
      ((Φ.presheafFiber (A := ModuleCat.{z} R)).map φ (Φ.toPresheafFiber U x P m)) =
    (ModuleCat.restrictScalars e.toRingHom).map ((sheafModuleFiberOfCommRing Φ O).map g)
      ((moduleStalkIso Φ O P M τ e a ha hτ).hom (Φ.toPresheafFiber U x P m))
  rw [Φ.toPresheafFiber_naturality_apply φ U x m,
    moduleStalkIso_hom_toPresheafFiber, moduleStalkIso_hom_toPresheafFiber, hcompat]
  exact (moduleStalkGerm_naturality Φ O g U x (τ.app (op U) m)).symm

end

end Stacks

end
